package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{Pred1, Pred2, forall => termForall, not => termNot, or => termOr}

abstract class ModelGeneratorSpec extends FlatSpec with Matchers {

  trait Machine {
    val machine: ModelGenerator = new GraphTableauxMachine()
  }

  // For debugging purposes
  protected def modelToString(model: Model): String = {
    val interpretation = model.getInterpretation
    interpretation.keys.map(term => {
      TermStringHelpers.termToString(term) + ": " + interpretation(term)
    }).mkString("\n")
  }

  protected def genGlobalPredName(name: String): GlobalName = {
    val mpath = MPath(DPath(URI.http colon "test"), new LocalName(List(SimpleStep("test"))))
    GlobalName(mpath, new LocalName(List(SimpleStep(name))))
  }

  protected def v(name: String): Term = {
    val term = new OMV(new LocalName(List(SimpleStep(name))))

    Pred1(genGlobalPredName(name), term)
  }

  protected def c(name: String): Term = {
    OMV(LocalName(List(SimpleStep(name))))
  }

  protected def pred1(name: String, arg1: Term): Term = {
    Pred1(genGlobalPredName(name), arg1)
  }

  protected def pred2(name: String, arg1: Term, arg2: Term): Term = {
    Pred2(genGlobalPredName(name), arg1, arg2)
  }

  protected def and(term1: Term, term2: Term): Term = {
    termNot(termOr(termNot(term1), termNot(term2)))
  }

  protected def imp(term1: Term, term2: Term): Term = {
    termOr(termNot(term1), term2)
  }

  protected def forall(variableName: String, innerTerm: Term): OMA = {
    termForall(new LocalName(List(SimpleStep(variableName))), innerTerm)
  }

  protected def exists(variableName: String, innerTerm: Term): Term = {
    termNot(forall(variableName, termNot(innerTerm)))
  }
}
