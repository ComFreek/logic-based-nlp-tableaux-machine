package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects.{OMV, Term}
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{Pred1, Pred2, not => termNot, or => termOr}

import scala.collection.Map
class ModelGeneratorTest extends FlatSpec with Matchers {

  trait Machine {
    val machine: ModelGenerator = new GraphTableauxMachine()
  }

  private def genGlobalPredName(name: String): GlobalName = {
    val mpath = MPath(DPath(URI.http colon "test"), new LocalName(List(SimpleStep("test"))))
    GlobalName(mpath, new LocalName(List(SimpleStep(name))))
  }

  private def v(name: String): Term = {
    val term = new OMV(new LocalName(List(SimpleStep(name))))

    Pred1(genGlobalPredName(name), term)
  }

  private def pred1(name: String, arg1: Term): Term = {
    Pred1(genGlobalPredName(name), arg1)
  }

  private def pred2(name: String, arg1: Term, arg2: Term): Term = {
    Pred2(genGlobalPredName(name), arg1, arg2)
  }

  private def and(term1: Term, term2: Term): Term = {
    termNot(termOr(termNot(term1), termNot(term2)))
  }

  it should "generate simple models" in new Machine {
    machine.feed(v("a"))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true))

    machine.feed(v("b"))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true, v("b") -> true))

    machine.feed(termNot(v("c")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true, v("b") -> true, v("c") -> false))
  }

  it should "switch models upon closing of branches" in new Machine {
    machine.feed(termOr(v("a"), v("b")))

    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true))

    machine.feed(termNot(v("b")))
    machine.nextModel() should be (None)
  }

  it should "retain fed inputs upon switching models" in new Machine {
    machine.feed(termOr(v("a"), v("b")))

    machine.feed(termNot(v("c")))
    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true, v("c") -> false))
  }

  it should "generate some deeply-branched models" in new Machine {
    machine.feed(termOr(v("a"), termOr(v("b"), termNot(v("c")))))
    machine.feed(termOr(v("d"), v("a")))

    machine.feed(v("c"))
    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true, v("c") -> true, v("d") -> true))
  }

  it should "work with binary predicates as in the course notes" in new Machine {
    // Cf. LBS lecture notes, slide 101, Example 5.3.6

    // (Peter loves Mary and Mary sleeps) or (Peter snores)
    val initialTerm = termOr(and(pred2("love", v("peter"), v("mary")), pred1("sleep", v("mary"))), pred1("snore", v("peter")))
    machine.feed(initialTerm)
    
    // Peter does not love Mary.
    machine.feed(termNot(pred2("love", v("peter"), v("mary"))))

    machine.nextModel().get.getInterpretation should be (Map(
      pred2("love", v("peter"), v("mary")) -> false,
      pred1("snore", v("peter")) -> true
    ))

    machine.feed(pred1("sleep", v("mary")))

    // No changes expected
    machine.nextModel().get.getInterpretation should be (Map(
      pred2("love", v("peter"), v("mary")) -> false,
      pred1("snore", v("peter")) -> true,
      pred1("sleep", v("mary")) -> true
    ))
  }
}
