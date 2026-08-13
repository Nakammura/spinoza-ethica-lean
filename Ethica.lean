/-
  Spinoza, *Ethica Ordine Geometrico Demonstrata* — Lean 4 formalisation.

  Top-level module. Re-exports each Pars in turn. Build with
  `lake build`; check propositions interactively in your editor.
-/

-- Pars I — De Deo
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Models.SingleSubstance
import Ethica.Pars1.Models.TwoSubstance
import Ethica.Pars1.ModalForm
import Ethica.Pars1.Models.MultiWorld
import Ethica.Pars1.Models.Counterexamples
import Ethica.Pars1.Theologia
import Ethica.Pars1.Models.NoGod
import Ethica.Pars1.Models.GodWorld
import Ethica.Pars1.Mereology
import Ethica.Pars1.Models.MereologyWitness
import Ethica.Pars1.Inherence
import Ethica.Pars1.Models.InherenceWitness
import Ethica.Pars1.Models.CounterexamplesII
import Ethica.Pars1.Consecutio
import Ethica.Pars1.Models.ConsecutioWitness
import Ethica.Pars1.Realitas
import Ethica.Pars1.Models.MultiAttribute
import Ethica.Pars1.Classificatio
import Ethica.Pars1.Models.ClassificatioWitness

-- Attributum — the re-typed attribute layer (GAP-25 / GAP-8a).
-- A parallel branch: nothing under Ethica/Pars1/ is modified, so the
-- v1.0.0 register and the published irreducibility results stand.
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms
import Ethica.Attributum.Bridge
import Ethica.Attributum.Models.DualAttribute
import Ethica.Attributum.Models.InfiniteAttribute

-- Pars II — De natura et origine mentis
import Ethica.Pars2.Idea
import Ethica.Pars2.Quatenus
import Ethica.Pars2.Models.MensWitness

-- Future Pars (stubs):
-- import Ethica.Pars3.Definitions   -- De origine et natura affectuum
-- import Ethica.Pars4.Definitions   -- De servitute humana
-- import Ethica.Pars5.Definitions   -- De potentia intellectus
