{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ApplicativeDo #-}

module HaddockUtils
  ( addFieldDoc,
    addFieldDocs,
    addConDoc,
    addConDocs,
    addConDocFirst,

    addModuleHaddock,
  ) where

import GhcPrelude

import GHC.Hs
import SrcLoc
import DynFlags ( WarningFlag(..) )
import Outputable hiding ( (<>) )

import Data.Semigroup
import Data.Foldable
import Data.Traversable
import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import Data.Coerce

import Lexer

addModuleHaddock :: Located (HsModule GhcPs) -> P (Located (HsModule GhcPs))
addModuleHaddock lmod = runAddHaddock (addHaddockModule lmod)

newtype HdkM a = MkHdkM (ReaderT LocRange (State [RealLocated HdkComment]) a)
  deriving (Functor, Applicative, Monad)
  -- The state of HdkM is a list of pending (unassociated with an AST node)
  -- Haddock comments, sorted by location, in ascending order.
  --
  -- We go over the AST, looking up these comments using 'takeHdkComments'.
  -- The remaining ones are ignored with a warning (-Wignored-haddock).

mkHdkM :: (LocRange -> [RealLocated HdkComment] -> (a, [RealLocated HdkComment])) -> HdkM a
unHdkM :: HdkM a -> (LocRange -> [RealLocated HdkComment] -> (a, [RealLocated HdkComment]))
mkHdkM = coerce
unHdkM = coerce

data HdkA a = MkHdkA SrcSpan (HdkM a)

instance Functor HdkA where
  fmap f (MkHdkA l m) = MkHdkA l (fmap f m)

instance Applicative HdkA where
  pure a = MkHdkA mempty (pure a)
  MkHdkA l1 m1 <*> MkHdkA l2 m2 =
    MkHdkA (l1 <> l2) (delim1 m1 <*> delim2 m2)
    where
      delim1 m = m `inLocRange` locRangeTo (srcSpanStart l2)
      delim2 m = m `inLocRange` locRangeFrom (srcSpanEnd l1)

mkHdkA :: (Located a -> HdkM b) -> Located a -> HdkA b
mkHdkA f a = MkHdkA (getLoc a) (f a)

registerHdkA :: Located a -> HdkA ()
registerHdkA a = MkHdkA (getLoc a) (pure ())

sepHdkA :: SrcLoc -> HdkA ()
sepHdkA l = MkHdkA (srcLocSpan l) (pure ())

delimitHdkA :: SrcSpan -> HdkA a -> HdkA a
delimitHdkA l' (MkHdkA l m) = MkHdkA (l' <> l) m

runAddHaddock :: HdkA a -> P a
runAddHaddock (MkHdkA _ m) = do
  pState <- getPState
  let (a, other_hdk_comments) = unHdkM m mempty (reverse (hdk_comments pState))
  mapM_ reportHdkComment other_hdk_comments
  return a
  where
    reportHdkComment :: RealLocated HdkComment -> P ()
    reportHdkComment (L l _) =
      addWarning Opt_WarnIgnoredHaddock (RealSrcSpan l) $
        text "A Haddock comment cannot appear in this position and will be ignored."

getLocStart, getLocEnd :: Located a -> SrcLoc
getLocEnd   = srcSpanEnd   . getLoc
getLocStart = srcSpanStart . getLoc

concatLHsDocString :: [LHsDocString] -> Maybe LHsDocString
concatLHsDocString [] = Nothing
concatLHsDocString [a] = Just a
concatLHsDocString (L l1 d1 : ds) = do
  L l2 d2 <- concatLHsDocString ds
  return $ L (combineSrcSpans l1 l2) (appendDocs d1 d2)

addHaddockModule :: Located (HsModule GhcPs) -> HdkA (Located (HsModule GhcPs))
addHaddockModule (L l_mod mod) = do
  headerDocs <-
    for @Maybe (hsmodName mod) $
    mkHdkA $ \name -> do
      docs <- takeHdkComments getDocNext `inLocRange` locRangeTo (getLocStart name)
      pure $ concatLHsDocString docs
  hsmodExports' <- traverse @Maybe addHaddockExports (hsmodExports mod)
  traverse_ registerHdkA (hsmodImports mod)
  hsmodDecls' <- addHaddockInterleaveItems getDocDecl addHaddockDecl (hsmodDecls mod)
  pure $ L l_mod $
    mod { hsmodExports = hsmodExports'
        , hsmodDecls = hsmodDecls'
        , hsmodHaddockModHeader = join @Maybe headerDocs }

addHaddockExports
  :: Located [LIE GhcPs]
  -> HdkA (Located [LIE GhcPs])
addHaddockExports (L l_exports exports) =
  delimitHdkA l_exports $ do
    exports' <- addHaddockInterleaveItems getDocIE (mkHdkA pure) exports
    sepHdkA (srcSpanEnd l_exports)
    pure $ L l_exports exports'

-- Add Haddock items to a list of non-Haddock items.
-- Used to process export lists (with getDocIE) and declarations (with getDocDecl).
addHaddockInterleaveItems
  :: forall a.
     (RealLocated HdkComment -> Maybe a) -- Get a documentation item
  -> (a -> HdkA a) -- Process a non-documentation item
  -> [a]           -- Unprocessed (non-documentation) items
  -> HdkA [a]      -- Documentation items & processed non-documentation items
addHaddockInterleaveItems getDocItem processItem = go
  where
    go :: [a] -> HdkA [a]
    go [] = MkHdkA mempty (takeHdkComments getDocItem)
    go (item : items) = do
      docItems <- MkHdkA mempty (takeHdkComments getDocItem)
      item' <- processItem item
      other_items <- go items
      pure $ docItems ++ item':other_items

getDocDecl :: RealLocated HdkComment -> Maybe (LHsDecl GhcPs)
getDocDecl a = mapLoc (DocD noExtField) <$> getDocDecl' a

getDocDecl' :: RealLocated HdkComment -> Maybe LDocDecl
getDocDecl' (L l_comment hdk_comment) =
  Just $ L (RealSrcSpan l_comment) $
    case hdk_comment of
      HdkCommentNext doc -> DocCommentNext doc
      HdkCommentPrev doc -> DocCommentPrev doc
      HdkCommentNamed s doc -> DocCommentNamed s doc
      HdkCommentSection n doc -> DocGroup n doc

getDocIE :: RealLocated HdkComment -> Maybe (LIE GhcPs)
getDocIE (L l_comment hdk_comment) =
  case hdk_comment of
    HdkCommentSection n doc -> Just $ L l (IEGroup noExtField n doc)
    HdkCommentNamed s _doc -> Just $ L l (IEDocNamed noExtField s)
    HdkCommentNext doc -> Just $ L l (IEDoc noExtField doc)
    _ -> Nothing
  where l = RealSrcSpan l_comment

getDocNext :: RealLocated HdkComment -> Maybe LHsDocString
getDocNext (L l (HdkCommentNext doc)) = Just $ L (RealSrcSpan l) doc
getDocNext _ = Nothing

getDocPrev :: RealLocated HdkComment -> Maybe LHsDocString
getDocPrev (L l (HdkCommentPrev doc)) = Just $ L (RealSrcSpan l) doc
getDocPrev _ = Nothing

addHaddockDecl :: LHsDecl GhcPs -> HdkA (LHsDecl GhcPs)
addHaddockDecl (L l_decl (SigD _ (TypeSig _ names t))) =
  delimitHdkA l_decl $ do
    traverse_ registerHdkA names
    t' <- addHaddockSigWcType t
    pure (L l_decl (SigD noExtField (TypeSig noExtField names t')))
addHaddockDecl (L l_decl (SigD _ (ClassOpSig _ is_dflt names t))) =
  delimitHdkA l_decl $ do
    traverse_ registerHdkA names
    t' <- addHaddockSigType t
    pure (L l_decl (SigD noExtField (ClassOpSig noExtField is_dflt names t')))
addHaddockDecl (L l_decl (TyClD _ decl))
  | DataDecl { tcdLName, tcdTyVars, tcdFixity, tcdDataDefn = defn } <- decl
  , HsDataDefn { dd_ND, dd_ctxt, dd_cType, dd_kindSig, dd_cons, dd_derivs } <- defn
  = delimitHdkA l_decl $ do
      registerHdkA tcdLName
      traverse_ registerHdkA dd_kindSig
      dd_cons' <- traverse addHaddockConDecl dd_cons
      dd_derivs' <- addHaddockDeriving dd_derivs
      pure $
        let defn' = HsDataDefn
                      { dd_ext = noExtField
                      , dd_ND, dd_ctxt, dd_cType, dd_kindSig
                      , dd_derivs = dd_derivs'
                      , dd_cons = dd_cons' }
            decl' = DataDecl
                      { tcdDExt = noExtField
                      , tcdLName, tcdTyVars, tcdFixity
                      , tcdDataDefn = defn' }
        in L l_decl (TyClD noExtField decl')
  | ClassDecl { tcdCtxt, tcdLName, tcdTyVars, tcdFixity, tcdFDs,
                tcdSigs, tcdMeths, tcdATs, tcdATDefs } <- decl
  = delimitHdkA l_decl $ do
      where_cls' <-
        addHaddockInterleaveItems getDocDecl addHaddockDecl $
        flattenBindsAndSigs (tcdMeths, tcdSigs, tcdATs, tcdATDefs, [], [])
      sepHdkA (srcSpanEnd l_decl)
      pure $
        let (tcdMeths', tcdSigs', tcdATs', tcdATDefs', _, tcdDocs) = partitionBindsAndSigs id where_cls'
            decl' = ClassDecl { tcdCExt = noExtField
                              , tcdCtxt, tcdLName, tcdTyVars, tcdFixity, tcdFDs
                              , tcdSigs = tcdSigs'
                              , tcdMeths = tcdMeths'
                              , tcdATs = tcdATs'
                              , tcdATDefs = tcdATDefs'
                              , tcdDocs }
        in L l_decl (TyClD noExtField decl')
addHaddockDecl (L l_decl (InstD _ decl))
  | DataFamInstD { dfid_inst } <- decl
  , DataFamInstDecl { dfid_eqn } <- dfid_inst
  = delimitHdkA l_decl $ do
    dfid_eqn' <- addHaddockImplicitBndrs (\fam_eqn -> case fam_eqn of
      FamEqn { feqn_tycon, feqn_bndrs, feqn_pats, feqn_fixity, feqn_rhs }
        | HsDataDefn { dd_ND, dd_ctxt, dd_cType, dd_kindSig, dd_cons, dd_derivs } <- feqn_rhs
        -> do
          registerHdkA feqn_tycon
          traverse_ registerHdkA dd_kindSig
          dd_cons' <- traverse addHaddockConDecl dd_cons
          dd_derivs' <- addHaddockDeriving dd_derivs
          pure $
            let defn' = HsDataDefn
                          { dd_ext = noExtField
                          , dd_ND, dd_ctxt, dd_cType, dd_kindSig
                          , dd_derivs = dd_derivs'
                          , dd_cons = dd_cons' }
            in FamEqn { feqn_ext = noExtField,
                        feqn_tycon, feqn_bndrs, feqn_pats, feqn_fixity,
                        feqn_rhs = defn' }
      FamEqn { feqn_rhs = XHsDataDefn x } -> noExtCon x
      XFamEqn x -> noExtCon x
      ) dfid_eqn
    pure $ L l_decl (InstD noExtField (DataFamInstD {
      dfid_ext = noExtField,
      dfid_inst = DataFamInstDecl { dfid_eqn = dfid_eqn' } }))
addHaddockDecl (L l_decl (ForD _ decl))
  = delimitHdkA l_decl $ do
    decl' <-
      case decl of
        ForeignImport { fd_name, fd_sig_ty, fd_fi } -> do
          registerHdkA fd_name
          fd_sig_ty' <- addHaddockSigType fd_sig_ty
          pure ForeignImport { fd_i_ext = noExtField,
                               fd_sig_ty = fd_sig_ty',
                               fd_name, fd_fi }
        ForeignExport { fd_name, fd_sig_ty, fd_fe } -> do
          registerHdkA fd_name
          fd_sig_ty' <- addHaddockSigType fd_sig_ty
          pure ForeignExport { fd_e_ext = noExtField,
                               fd_sig_ty = fd_sig_ty',
                               fd_name, fd_fe }
        XForeignDecl x -> noExtCon x
    pure $ L l_decl (ForD noExtField decl')
addHaddockDecl d = delimitHdkA (getLoc d) (pure d)

addHaddockDeriving :: HsDeriving GhcPs -> HdkA (HsDeriving GhcPs)
addHaddockDeriving lderivs =
  delimitHdkA (getLoc lderivs) $
  for @Located lderivs $ \derivs ->
    traverse addHaddockDerivingClause derivs

addHaddockDerivingClause :: LHsDerivingClause GhcPs -> HdkA (LHsDerivingClause GhcPs)
addHaddockDerivingClause lderiv =
  delimitHdkA (getLoc lderiv) $
  for @Located lderiv $ \deriv ->
  case deriv of
    HsDerivingClause { deriv_clause_strategy, deriv_clause_tys } -> do
      traverse_ @Maybe registerHdkA deriv_clause_strategy
      deriv_clause_tys' <-
        delimitHdkA (getLoc deriv_clause_tys) $
        for @Located (deriv_clause_tys) $ \tys ->
          traverse addHaddockSigType tys
      pure HsDerivingClause
        { deriv_clause_ext = noExtField,
          deriv_clause_strategy,
          deriv_clause_tys = deriv_clause_tys' }
    XHsDerivingClause x -> noExtCon x

addHaddockConDecl :: LConDecl GhcPs -> HdkA (LConDecl GhcPs)
addHaddockConDecl = mkHdkA $ \(L l_con con) -> do
  trailingConDocs <- do
    nextDocs <- peekHdkComments getDocNext `inLocRange` locRangeTo (srcSpanStart l_con)
    -- See Note [Trailing comment on constructor declaration]
    innerDocs <- peekHdkComments Just `inLocRange` locRangeFrom (srcSpanStart l_con)
                                      `inLocRange` locRangeTo (srcSpanEnd l_con)
    if null innerDocs && null nextDocs
      then takeHdkComments getDocPrev `inLocRange` locRangeFrom (srcSpanEnd l_con)
      else return []
  let getConDoc = mkHdkA $ \(L l _) -> do
        nextDocs <- takeHdkComments getDocNext `inLocRange` locRangeTo (srcSpanStart l)
        prevDocs <- takeHdkComments getDocPrev `inLocRange` locRangeFrom (srcSpanEnd l)
        return $ concatLHsDocString (nextDocs ++ prevDocs ++ trailingConDocs)
      hdk_a_m (MkHdkA _ m) = m
  hdk_a_m $ case con of
    ConDeclGADT { con_g_ext, con_names, con_forall, con_qvars, con_mb_cxt, con_args, con_res_ty } -> do
      con_doc' <- getConDoc (head con_names)
      con_args' <-
        case con_args of
          PrefixCon ts -> do
            ts' <- traverse addHaddockType ts
            pure $ PrefixCon ts'
          RecCon (L l_rec flds) -> do
            flds' <- traverse addHaddockConDeclField flds
            pure $ RecCon (L l_rec flds')
          InfixCon _ _ -> panic "ConDeclGADT InfixCon"
      con_res_ty' <- addHaddockType con_res_ty
      pure $ L l_con $
        ConDeclGADT { con_g_ext, con_names, con_forall, con_qvars, con_mb_cxt,
                      con_doc = con_doc',
                      con_args = con_args',
                      con_res_ty = con_res_ty' }
    ConDeclH98 { con_ext, con_name, con_forall, con_ex_tvs, con_mb_cxt, con_args } -> do
      case con_args of
        PrefixCon ts -> do
          con_doc' <- getConDoc con_name
          ts' <- traverse addHaddockType ts
          pure $ L l_con $
            ConDeclH98 { con_ext, con_name, con_forall, con_ex_tvs, con_mb_cxt,
                         con_doc = con_doc',
                         con_args = PrefixCon ts' }
        InfixCon t1 t2 -> do
          t1' <- addHaddockType t1
          con_doc' <- getConDoc con_name
          t2' <- addHaddockType t2
          pure $ L l_con $
            ConDeclH98 { con_ext, con_name, con_forall, con_ex_tvs, con_mb_cxt,
                         con_doc = con_doc',
                         con_args = InfixCon t1' t2' }
        RecCon (L l_rec flds) -> do
          con_doc' <- getConDoc con_name
          flds' <- traverse addHaddockConDeclField flds
          pure $ L l_con $
            ConDeclH98 { con_ext, con_name, con_forall, con_ex_tvs, con_mb_cxt,
                         con_doc = con_doc',
                         con_args = RecCon (L l_rec flds') }
    XConDecl x -> noExtCon x

{- Note [Trailing comment on constructor declaration]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The trailing comment after a constructor declaration is associated with the
constructor itself when there are no other comments inside the declaration:

   data T = MkT A B        -- ^ Comment on MkT
   data T = MkT { x :: A } -- ^ Comment on MkT

When there are other comments, the trailing comment applies to the last field:

   data T = MkT -- ^ Comment on MkT
            A   -- ^ Comment on A
            B   -- ^ Comment on B

   data T =
     MkT { a :: A   -- ^ Comment on a
         , b :: B   -- ^ Comment on b
         , c :: C } -- ^ Comment on c
-}

addHaddockConDeclField :: LConDeclField GhcPs -> HdkA (LConDeclField GhcPs)
addHaddockConDeclField = mkHdkA $ \(L l_fld fld) -> do
  nextDocs <- takeHdkComments getDocNext `inLocRange` locRangeTo (srcSpanStart l_fld)
  prevDocs <- takeHdkComments getDocPrev `inLocRange` locRangeFrom (srcSpanEnd l_fld)
  let cd_fld_doc = concatLHsDocString (nextDocs ++ prevDocs)
  return $ L l_fld $ case fld of
    ConDeclField { cd_fld_ext, cd_fld_names, cd_fld_type } ->
      ConDeclField { cd_fld_ext, cd_fld_names, cd_fld_type, cd_fld_doc }
    XConDeclField x -> noExtCon x

addHaddockWildCardBndrs
  :: (a -> HdkA a)
  -> HsWildCardBndrs GhcPs a
  -> HdkA (HsWildCardBndrs GhcPs a)
addHaddockWildCardBndrs f (HsWC _ t) = HsWC noExtField <$> f t
addHaddockWildCardBndrs _ (XHsWildCardBndrs x) = noExtCon x

addHaddockImplicitBndrs
  :: (a -> HdkA a)
  -> HsImplicitBndrs GhcPs a
  -> HdkA (HsImplicitBndrs GhcPs a)
addHaddockImplicitBndrs f (HsIB _ t) = HsIB noExtField <$> f t
addHaddockImplicitBndrs _ (XHsImplicitBndrs x) = noExtCon x

addHaddockSigType :: LHsSigType GhcPs -> HdkA (LHsSigType GhcPs)
addHaddockSigType = addHaddockImplicitBndrs addHaddockType

addHaddockSigWcType :: LHsSigWcType GhcPs -> HdkA (LHsSigWcType GhcPs)
addHaddockSigWcType = addHaddockWildCardBndrs addHaddockSigType

addHaddockType :: LHsType GhcPs -> HdkA (LHsType GhcPs)
addHaddockType (L l_t (HsForAllTy _ fvf bndrs body)) =
  delimitHdkA l_t $ do
    body' <- addHaddockType body
    pure (L l_t (HsForAllTy noExtField fvf bndrs body'))
addHaddockType (L l_t (HsQualTy _ lhs rhs)) =
  delimitHdkA l_t $ do
    rhs' <- addHaddockType rhs
    pure (L l_t (HsQualTy noExtField lhs rhs'))
addHaddockType (L l_t (HsFunTy _ lhs rhs)) =
  delimitHdkA l_t $ do
    lhs' <- addHaddockType lhs
    rhs' <- addHaddockType rhs
    pure (L l_t (HsFunTy noExtField lhs' rhs'))
addHaddockType t = mkHdkA go t where
  go t' = do
    nextDocs <- takeHdkComments getDocNext `inLocRange` locRangeTo (getLocStart t')
    prevDocs <- takeHdkComments getDocPrev `inLocRange` locRangeFrom (getLocEnd t')
    let mDoc = concatLHsDocString (nextDocs ++ prevDocs)
    return $ mkLHsDocTyMaybe t mDoc

data LowerLocBound = StartOfFile | StartLoc RealSrcLoc

instance Semigroup LowerLocBound where
  StartOfFile <> l = l
  l <> StartOfFile = l
  StartLoc l1 <> StartLoc l2 = StartLoc (max l1 l2)

instance Monoid LowerLocBound where
  mempty = StartOfFile

data UpperLocBound = EndOfFile | EndLoc RealSrcLoc

instance Semigroup UpperLocBound where
  EndOfFile <> l = l
  l <> EndOfFile = l
  EndLoc l1 <> EndLoc l2 = EndLoc (min l1 l2)

instance Monoid UpperLocBound where
  mempty = EndOfFile

-- | A location range for extracting documentation comments.
data LocRange =
  LocRange
    LowerLocBound  -- from
    UpperLocBound  -- to

instance Semigroup LocRange where
  LocRange from1 to1 <> LocRange from2 to2 =
    LocRange (from1 <> from2) (to1 <> to2)

instance Monoid LocRange where
  mempty = LocRange mempty mempty

locRangeFrom :: SrcLoc -> LocRange
locRangeFrom (UnhelpfulLoc _) = mempty
locRangeFrom (RealSrcLoc l) = LocRange (StartLoc l) EndOfFile

locRangeTo :: SrcLoc -> LocRange
locRangeTo (UnhelpfulLoc _) = mempty
locRangeTo (RealSrcLoc l) = LocRange StartOfFile (EndLoc l)

inLocRange :: HdkM a -> LocRange -> HdkM a
m `inLocRange` r = mkHdkM $ \range -> unHdkM m (r <> range)

-- | The state monad but without newtype wrapping/unwrapping.
type InlineState s a = s -> (a, s)

-- Take the Haddock comments that satisfy the matching function,
-- leaving the rest pending.
takeHdkComments :: forall a. (RealLocated HdkComment -> Maybe a) -> HdkM [a]
takeHdkComments f =
  mkHdkM $ \range ->
  case range of
    LocRange hdk_from hdk_to ->
      zoom_after hdk_from $
      zoom_before hdk_to $
      foldr add_comment ([], [])
  where
    add_comment
      :: RealLocated HdkComment
      -> ([a], [RealLocated HdkComment])
      -> ([a], [RealLocated HdkComment])
    add_comment hdk_comment (items, other_hdk_comments) =
      case f hdk_comment of
        Just item -> (item : items, other_hdk_comments)
        Nothing -> (items, hdk_comment : other_hdk_comments)

    zoom_after
      :: LowerLocBound
      -> InlineState [RealLocated e] x
      -> InlineState [RealLocated e] x
    zoom_after StartOfFile m = m
    zoom_after (StartLoc l) m =
      \comments ->
        let
          is_after (L l_comment _) = realSrcSpanStart l_comment >= l
          (comments_before, comments_after) = break is_after comments
          (result, other_comments) = m comments_after
        in
          -- 'comments_before' will typically include only incorrectly
          -- positioned comments, so the concatenation cost is small.
          (result, comments_before ++ other_comments)

    zoom_before
      :: UpperLocBound
      -> InlineState [RealLocated e] x
      -> InlineState [RealLocated e] x
    zoom_before EndOfFile m = m
    zoom_before (EndLoc l) m =
      \comments ->
        let
          is_before (L l_comment _) = realSrcSpanStart l_comment <= l
          (comments_before, comments_after) = span is_before comments
          (result, other_comments) = m comments_before
        in
          -- 'other_comments' will typically include only incorrectly
          -- positioned comments, so the concatenation cost is small.
          (result, other_comments ++ comments_after)

-- | Peek at the Haddock comments that satisfy the matching function. Unlike
-- 'takeHdkComments', leave them pending.
peekHdkComments :: (RealLocated HdkComment -> Maybe a) -> HdkM [a]
peekHdkComments f =
  mkHdkM $ \range comments ->
    let (r, _) = unHdkM (takeHdkComments f) range comments
    in (r, comments)

mkLHsDocTy :: LHsType GhcPs -> LHsDocString -> LHsType GhcPs
mkLHsDocTy t doc =
  let loc = getLoc t `combineSrcSpans` getLoc doc
  in L loc (HsDocTy noExtField t doc)

mkLHsDocTyMaybe :: LHsType GhcPs -> Maybe LHsDocString -> LHsType GhcPs
mkLHsDocTyMaybe t = maybe t (mkLHsDocTy t)

-- -----------------------------------------------------------------------------
-- Adding documentation to record fields (used in parsing).

addFieldDoc :: LConDeclField a -> Maybe LHsDocString -> LConDeclField a
addFieldDoc (L l fld) doc
  = L l (fld { cd_fld_doc = cd_fld_doc fld `mplus` doc })

addFieldDocs :: [LConDeclField a] -> Maybe LHsDocString -> [LConDeclField a]
addFieldDocs [] _ = []
addFieldDocs (x:xs) doc = addFieldDoc x doc : xs


addConDoc :: LConDecl a -> Maybe LHsDocString -> LConDecl a
addConDoc decl    Nothing = decl
addConDoc (L p c) doc     = L p ( c { con_doc = con_doc c `mplus` doc } )

addConDocs :: [LConDecl a] -> Maybe LHsDocString -> [LConDecl a]
addConDocs [] _ = []
addConDocs [x] doc = [addConDoc x doc]
addConDocs (x:xs) doc = x : addConDocs xs doc

addConDocFirst :: [LConDecl a] -> Maybe LHsDocString -> [LConDecl a]
addConDocFirst [] _ = []
addConDocFirst (x:xs) doc = addConDoc x doc : xs
