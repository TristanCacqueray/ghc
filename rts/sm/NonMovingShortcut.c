/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2019
 *
 * Non-moving garbage collector and allocator:
 * Indirection short-cutting and the selector optimisation
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "GC.h"
#include "SMPClosureOps.h"
#include "NonMovingMark.h"
#include "NonMovingShortcut.h"

#define MAX_CHAIN_LENGTH 1024

static StgSelector *selector_chain[MAX_CHAIN_LENGTH];
static uint32_t selector_chain_len;

// p should be locked
static void push_selector_thunk(StgSelector *p)
{
    ASSERT(selector_chain_len < MAX_CHAIN_LENGTH);
    selector_chain[selector_chain_len++] = p;
}

static StgSelector *pop_selector_thunk(void)
{
    if (selector_chain_len == 0) {
        return NULL;
    }
    return selector_chain[selector_chain_len--];
}


static void
nonmoving_unchain_thunk_selectors(StgClosure *val)
{
    for (StgSelector *p = pop_selector_thunk(); p; p = pop_selector_thunk()) {
        ((StgInd*)p)->indirectee = val;
        unlockClosure((StgClosure*)p, &stg_IND_info);
    }
}

#if defined(DEBUG)
static void
print_selector_chain(void)
{
    debugBelch("Selector chain:\n");
    for (int i = 0; i < selector_chain_len; ++i) {
        printClosure((StgClosure*)SELECTOR_CHAIN[i]);
    }
}
#endif

void
nonmoving_eval_thunk_selector(MarkQueue *queue, StgSelector *p, StgClosure **origin)
{
    // We need this to check that the origin pointer has not been mutated when
    // we CAS it.
    const StgSelector *const p0 = p;

    // Idea: `origin` will be updated with the value of this selector. When
    // looking for the value if the selectee is also a selector thunk we
    // recurse.
    //
    // Note that `origin` should be updated with cas() as the it may be a field
    // of a mutable object and may be mutated in the meantime.
    //
    // If value is a selector then we add it to the chain. All selectors in the
    // chain are WHITEHOLEs at this point. Locking these closures is fine
    // becuase they're all thunk so we don't have tagged pointers to them.
    //
    // All selectors in the chain will be updated with INDs to the final value.

    ASSERT(HEAP_ALLOCED_GC((P_)p) && (Bdescr((P_)p)->flags & BF_NONMOVING));

    // Info table of the selector closure when we lock it
    StgInfoTable *info_ptr;

    // Final value of the selector thunk. All selectors in the chain will become
    // an IND to this value and origin will point to this directly.
    //
    // Update when we actually select a value from a selectee.
    StgClosure *val = NULL;

    // Three loops:
    //
    // - selector_loop: When selectee is a THUNK or BLACKHOLE we follow the
    //   indirection.
    //
    // - selector_chain: When val is a selector evaluate the selector. New val
    //   is the value of the selector.
    //
    // - val_loop: When val is a THUNK or BLACKHOLE follow the indirection.

selector_chain:
    markQueuePushClosure(queue, (StgClosure*)p, NULL);

    // Lock the closure we're evaluating
    info_ptr = lockClosure((StgClosure*)p);

    if (INFO_PTR_TO_STRUCT(info_ptr)->type != THUNK_SELECTOR) {
        // A mutator updated the closure in the meantime
        // debugBelch("THUNK_SELECTOR evaluated in the meantime\n");
        ASSERT(info_ptr == &stg_BLACKHOLE_info);
        // Update the whole chain with the value of BLACKHOLE
        val = ((StgInd*)p)->indirectee;
        goto bale_out;
    }

    // Select `field` from `selectee`
    uint32_t field = INFO_PTR_TO_STRUCT((StgInfoTable *)info_ptr)->layout.selector_offset;
    StgClosure *selectee = UNTAG_CLOSURE(p->selectee);

    markQueuePushClosure(queue, selectee, NULL);

    StgInfoTable *selectee_info;
selector_loop:
    selectee_info = INFO_PTR_TO_STRUCT(selectee->header.info);

    switch (selectee_info->type) {
        case WHITEHOLE:
            goto bale_out; // A loop

        case CONSTR:
        case CONSTR_1_0:
        case CONSTR_0_1:
        case CONSTR_2_0:
        case CONSTR_1_1:
        case CONSTR_0_2:
        case CONSTR_NOCAF: {
            // check that the size is in range
            ASSERT(field <  (StgWord32)(selectee_info->layout.payload.ptrs +
                                        selectee_info->layout.payload.nptrs));

            val = selectee->payload[field];

            // We will update this selector too so push it to the chain
            push_selector_thunk(p);

            // `val` is the value of this selector thunk. We need to check a
            // few cases:
            //
            // - If `val` is in the moving heap, we stop here and update the
            //   chain. All updated objects should be added to the mut_list
            //   (which is handled by `nonmoving_unchain_thunk_selectors`).
            //
            // - If `val` is in the non-moving heap, we check if it's also a
            //   selector. If it is we add it to the chain and loop.

        val_loop:
            // TODO: does it have to be a heap-allocated object?
            if (!(Bdescr((P_)val)->flags & BF_NONMOVING)) {
                // A moving object, stop
                goto bale_out;
            }

            StgInfoTable *val_info_ptr =
                INFO_PTR_TO_STRUCT(UNTAG_CLOSURE(val)->header.info);

            switch (val_info_ptr->type) {
            case IND:
            case IND_STATIC:
                val = ((StgInd*)val)->indirectee;
                goto val_loop;
            case THUNK_SELECTOR:
                p = (StgSelector*)val;
                goto selector_chain;
            default:
                break;
            }

            goto bale_out;
        }

        case IND:
        case IND_STATIC:
            selectee = UNTAG_CLOSURE( ((StgInd *)selectee)->indirectee );
            goto selector_loop;

        case BLACKHOLE: {
            // Not all blackholes are indirections!
            StgClosure *r = ((StgInd*)selectee)->indirectee;

            // establish whether this BH has been updated, and is now an
            // indirection, as in evacuate().
            if (GET_CLOSURE_TAG(r) == 0) {
                const StgInfoTable *i = r->header.info;
                if (i == &stg_TSO_info
                    || i == &stg_WHITEHOLE_info
                    || i == &stg_BLOCKING_QUEUE_CLEAN_info
                    || i == &stg_BLOCKING_QUEUE_DIRTY_info) {
                    goto bale_out;
                }
                ASSERT(i != &stg_IND_info); // TODO not sure about this part
            }

            selectee = UNTAG_CLOSURE(r);
            goto selector_loop;
        }

        case AP:
        case AP_STACK:
        case THUNK:
        case THUNK_1_0:
        case THUNK_0_1:
        case THUNK_2_0:
        case THUNK_1_1:
        case THUNK_0_2:
        case THUNK_STATIC:
        case THUNK_SELECTOR: {
            // not evaluated yet
            // note that for THUNK_SELECTOR we can recursively evaluate it TODO
            goto bale_out;
        }

        default:
            barf("nonmoving_eval_thunk_selector: strange selectee %d",
                 (int)(selectee_info->type));
    }

bale_out:
    if (val) {
        // debugBelch("Updating selector chain\n");
        nonmoving_unchain_thunk_selectors(val);
        if (origin) {
            cas(origin, p0, val);
        }
    } else {
        // debugBelch("val is NULL -- skipping selector chain\n");
    }
}
