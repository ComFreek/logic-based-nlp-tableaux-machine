package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term

trait ModelGenerator {
  def feed(term: Term): Unit

  def nextModel(): Option[Model]
}