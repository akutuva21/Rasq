/-!
# StochasticQuantization

A small Lean library for the mathematics behind processivity-driven stochastic
quantization.  The focus is the finite stochastic slow/fast mechanism itself: how
discrete catalyst occupancy, target relaxation, and catalyst residence time combine
to create or erase quantized output states.

The library proves algebraic statements used by the accompanying Ras analysis:

* the exact frozen-occupancy target equilibrium;
* exact conditional peak spacing and low-saturation error;
* local detailed balance for the finite birth/death target chain;
* how common scaling of binding/unbinding changes dwell time/processivity while
  preserving equilibrium binding ratios;
* a quantitative slow/fast tracking rule connecting Ras relaxation to the chance
  that an SOS occupancy state survives long enough for Ras to follow it;
* Ras-specific peak formulas, peak-crowding conditions, and the Model 1 -> Model 3
  kinetic rescaling invariants.

See `formalization/README.md` for the biological interpretation and proof status.
-/

import StochasticQuantization.Core
import StochasticQuantization.BirthDeath
import StochasticQuantization.Processivity
import StochasticQuantization.SlowFast
import StochasticQuantization.Ras
import StochasticQuantization.RasEquilibrium
