package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term

trait Model {
  def getInterpretation: Map[Term, Boolean]
}
