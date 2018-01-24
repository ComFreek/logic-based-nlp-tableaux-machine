package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term

/**
  * A machine capable of model generation when it is fed Terms.
  *
  * It inherently supports theorem proving as well:
  * By feeding negated formulae (e.g. ~φ) and checking whether
  * nextModel() returns None, one has proven φ.
  *
  * @see Term
  */
trait ModelGenerator {
  /**
    * Feed a new term into the machine, which is annotated with True.
    */
  def feed(term: Term): Unit

  /**
    * Generate the next model if it exists.
    *
    * @return A populated Option if a model exists and None otherwise.
    */
  def nextModel(): Option[Model]
}