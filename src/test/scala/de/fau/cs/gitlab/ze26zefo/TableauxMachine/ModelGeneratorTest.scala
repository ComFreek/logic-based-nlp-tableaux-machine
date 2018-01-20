package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.gf.Convenience.Pred1
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects.{OMV, Term}
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{not => termNot, or => termOr}

import scala.collection.Map
class ModelGeneratorTest extends FlatSpec with Matchers {

  trait Machine {
    val machine: ModelGenerator = new GraphTableauxMachine()
  }

  private def v(name: String): Term = {
    // val mpath = new MPath(DPath(URI.http colon "mathhub.info") / "Teaching" / "LBS", new LocalName(List(new SimpleStep("test"))))
    val mpath = MPath(DPath(URI.http colon "gov"), new LocalName(List(SimpleStep("test"))))
    val globalName = GlobalName(mpath, new LocalName(List(SimpleStep(name))))
    val term = new OMV(new LocalName(List(SimpleStep(name))))

    Pred1(globalName, term)
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
}
