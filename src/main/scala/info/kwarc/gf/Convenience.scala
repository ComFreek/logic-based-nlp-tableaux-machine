package info.kwarc.gf

import info.kwarc.mmt.api.objects.{OMS, Term}
import info.kwarc.mmt.api.{GlobalName, LocalName}
import info.kwarc.mmt.lf.{Apply, ApplySpine, Lambda}

object Convenience {
  implicit class orApply(tm : Term) {
    def or(tm2 : Term) = Convenience.or(tm,tm2)
  }
  object forall {
    val path = MMTGF.dpath ? "LogicSyntax" ? "forall"
    val indpath = MMTGF.dpath ? "LogicSyntax" ? "ind"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(`path`),Lambda(x,_,bd) :: Nil) =>
        Some((x,bd))
      case _ => None
    }
    def apply(v : LocalName, bd : Term) = Apply(OMS(path),Lambda(v,OMS(indpath),bd))
  }
  object or {
    val path = MMTGF.dpath ? "LogicSyntax" ? "or"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(`path`),List(tm1,tm2)) => Some((tm1,tm2))
      case _ => None
    }
    def apply(tm1 : Term, tm2 : Term) = ApplySpine(OMS(path),tm1,tm2)
  }
  object not {
    val path = MMTGF.dpath ? "LogicSyntax" ? "negation"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(`path`),List(tm1)) => Some(tm1)
      case _ => None
    }
    def apply(tm1 : Term) = ApplySpine(OMS(path),tm1)
  }
  implicit class Eq(tm : Term) {
    def ieq(tm2 : Term) = Convenience.Eq.apply(tm,tm2)
  }
  object Eq {
    val predpath = MMTGF.dpath ? "LogicSyntax" ? "npeq"
    val path = MMTGF.dpath ? "LogicSyntax" ? "ieq"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(`path`),List(tm1,tm2)) => Some((tm1,tm2))
      case _ => None
    }
    def apply(tm1 : Term, tm2 : Term) = ApplySpine(OMS(path),tm1,tm2)
  }
  object the {
    val path = MMTGF.dpath ? "LogicSyntax" ? "that"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(`path`),List(tm1)) => Some(tm1)
      case _ => None
    }
    def apply(tm1 : Term) = ApplySpine(OMS(path),tm1)
  }
  object Pred1 {
    val path = MMTGF.dpath ? "LogicSyntax" ? "that"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(p),List(tm1)) if p.module != path.module => Some((p,tm1))
      case _ => None
    }
    def apply(p : GlobalName, tm1 : Term) = ApplySpine(OMS(p),tm1)
  }
  object Pred2 {
    val path = MMTGF.dpath ? "LogicSyntax" ? "that"
    def unapply(tm : Term) = tm match {
      case ApplySpine(OMS(p),List(tm1,tm2)) if p.module != path.module => Some((p,tm1,tm2))
      case _ => None
    }
    def apply(p : GlobalName, tm1 : Term, tm2 : Term) = ApplySpine(OMS(p),tm1,tm2)
  }

}