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

-- Future Pars (stubs):
-- import Ethica.Pars2.Definitions   -- De natura et origine mentis
-- import Ethica.Pars3.Definitions   -- De origine et natura affectuum
-- import Ethica.Pars4.Definitions   -- De servitute humana
-- import Ethica.Pars5.Definitions   -- De potentia intellectus
