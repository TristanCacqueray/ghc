{-
(c) The University of Glasgow 2006
(c) The AQUA Project, Glasgow University, 1993-1998

\section[TcAnnotations]{Typechecking annotations}
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module TcAnnotations ( tcAnnotations, annCtxt ) where

import GhcPrelude

import {-# SOURCE #-} TcSplice ( runAnnotation )
import Module
import GHC.Driver.Session
import Control.Monad ( when )

import GHC.Hs
import Name
import Annotations
import TcRnMonad
import SrcLoc
import Outputable
import GHC.Driver.Types

-- Some platforms don't support the interpreter, and compilation on those
-- platforms shouldn't fail just due to annotations
tcAnnotations :: [LAnnDecl GhcRn] -> TcM [Annotation]
tcAnnotations anns = do
  hsc_env <- getTopEnv
  case hsc_interp hsc_env of
    Just _  -> mapM tcAnnotation anns
    Nothing -> warnAnns anns

warnAnns :: [LAnnDecl GhcRn] -> TcM [Annotation]
--- No GHCI; emit a warning (not an error) and ignore. cf #4268
warnAnns [] = return []
warnAnns anns@(L loc _ : _)
  = do { setSrcSpan loc $ addWarnTc NoReason $
             (text "Ignoring ANN annotation" <> plural anns <> comma
             <+> text "because this is a stage-1 compiler without -fexternal-interpreter or doesn't support GHCi")
       ; return [] }

tcAnnotation :: LAnnDecl GhcRn -> TcM Annotation
tcAnnotation (L loc ann@(HsAnnotation _ _ provenance expr)) = do
    -- Work out what the full target of this annotation was
    mod <- getModule
    let target = annProvenanceToTarget mod provenance

    -- Run that annotation and construct the full Annotation data structure
    setSrcSpan loc $ addErrCtxt (annCtxt ann) $ do
      -- See #10826 -- Annotations allow one to bypass Safe Haskell.
      dflags <- getDynFlags
      when (safeLanguageOn dflags) $ failWithTc safeHsErr
      runAnnotation target expr
    where
      safeHsErr = vcat [ text "Annotations are not compatible with Safe Haskell."
                  , text "See https://gitlab.haskell.org/ghc/ghc/issues/10826" ]
tcAnnotation (L _ (XAnnDecl nec)) = noExtCon nec

annProvenanceToTarget :: Module -> AnnProvenance Name
                      -> AnnTarget Name
annProvenanceToTarget _   (ValueAnnProvenance (L _ name)) = NamedTarget name
annProvenanceToTarget _   (TypeAnnProvenance (L _ name))  = NamedTarget name
annProvenanceToTarget mod ModuleAnnProvenance             = ModuleTarget mod

annCtxt :: (OutputableBndrId p) => AnnDecl (GhcPass p) -> SDoc
annCtxt ann
  = hang (text "In the annotation:") 2 (ppr ann)
