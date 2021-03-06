module GHC.HsToCore.Match where

import GhcPrelude
import Var      ( Id )
import TcType   ( Type )
import GHC.HsToCore.Monad  ( DsM, EquationInfo, MatchResult )
import GHC.Core  ( CoreExpr )
import GHC.Hs   ( LPat, HsMatchContext, MatchGroup, LHsExpr )
import GHC.Hs.Extension ( GhcRn, GhcTc )

match   :: [Id]
        -> Type
        -> [EquationInfo]
        -> DsM MatchResult

matchWrapper
        :: HsMatchContext GhcRn
        -> Maybe (LHsExpr GhcTc)
        -> MatchGroup GhcTc (LHsExpr GhcTc)
        -> DsM ([Id], CoreExpr)

matchSimply
        :: CoreExpr
        -> HsMatchContext GhcRn
        -> LPat GhcTc
        -> CoreExpr
        -> CoreExpr
        -> DsM CoreExpr

matchSinglePatVar
        :: Id
        -> HsMatchContext GhcRn
        -> LPat GhcTc
        -> Type
        -> MatchResult
        -> DsM MatchResult
