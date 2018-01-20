package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.gf.Convenience.{Eq, Pred1, Pred2, not, or, forall}
import info.kwarc.mmt.api.objects.{OMV, Term}

object TermStringHelpers {
  def termToString(term: Term): String = term match {
    case not(a) or b => "(" + termToString(a) + ") -> (" + termToString(b) + ")"
    case a or b => "(" + termToString(a) + ") v (" + termToString(b) + ")"
    case not(a) => "not(" + termToString(a) + ")"
    case Pred1(globalName, arg1) => globalName.name.steps.last.toPath + "(" + termToString(arg1) + ")"
    case Pred2(globalName, arg1, arg2) =>
      globalName.name.steps.last.toPath + "((" + termToString(arg1) + "), (" + termToString(arg2) + "))"
    case a Eq b => "(" + termToString(a) + ") = (" + termToString(b) + ")"
    case forall(variable, innerTerm) => "∀" + variable.steps.last.toPath + "(" + termToString(innerTerm) + ")"
    //case OMV(name) => name.steps.last.toPath
    case any => any.toStr(true)
  }

  def termSeqToString(terms: Seq[(Term, Boolean)]): String = {
    terms.map(annotatedTerm => termToString(annotatedTerm._1) + ": " + annotatedTerm._2).mkString(", ")
  }

  def termSetToString(terms: Set[(Term, Boolean)]): String = termSeqToString(terms.toSeq)
}