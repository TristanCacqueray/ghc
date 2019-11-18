#include <Rts.h>

void ACQUIRE_SPIN_LOCK_slow(SpinLock * p)
{
    do {
        if (TRY_ACQUIRE_SPIN_LOCK(p)) return;
        IF_PROF_SPIN(p->yield++);
        yieldThread();
    } while (1);
}
