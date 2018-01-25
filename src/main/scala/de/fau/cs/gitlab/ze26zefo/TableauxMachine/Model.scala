package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term

/**
  * A FOL model, which is ready to inspect, i.e. its interpretation is guaranteed to be
  * accessible in constant time.
  */
trait Model {
  /**
    * Get the interpretation. This function must run in O(1).
    * @return
    */
  def getInterpretation: Map[Term, Boolean]
}
