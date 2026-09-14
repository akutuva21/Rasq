# Full finite-count Ras CTMC certificate

This is numerical verification of the same six-reaction count process used by the Lean source. The Lean theorem is untruncated; this sparse solve caps only total bound SOS for tractability while keeping all 1000 Ras molecules.

## Native high-SOS conditions

| model | rhoSOS | states | cap mass | TV to frozen mixture | stationary residual | Poisson identity rel. error |
|---|---:|---:|---:|---:|---:|---:|
| Model1 | 10 | 65,626 | 4.98e-07 | 0.59656 | 1.47e-12 | 2.72e-12 |
| Model2 | 30 | 65,626 | 0.000297 | 0.23570 | 6.09e-12 | 4.85e-12 |
| Model3 | 10 | 65,626 | 4.61e-07 | 0.80793 | 2.61e-11 | 7.50e-10 |

The exact checked identity is `pi - P*pi = -R*(Q_SOS*pi)` at epsilon=1. The residual column tests this identity after independently solving the stationary distribution and then applying the O(F) blockwise Poisson corrector.

## Bound-SOS cap convergence (Model 2, 30 nM)

| Bmax | states | probability on cap | TV |
|---:|---:|---:|---:|
| 8 | 44,805 | 0.00254 | 0.235982 |
| 10 | 65,626 | 0.000297 | 0.235701 |
| 12 | 90,363 | 2.56e-05 | 0.235673 |

## Slow-clock scaling on the native count model

| model | epsilon | TV to frozen mixture |
|---|---:|---:|
| Model1 | 1 | 0.596559 |
| Model1 | 0.3 | 0.335110 |
| Model1 | 0.1 | 0.141807 |
| Model1 | 0.03 | 0.046673 |
| Model1 | 0.01 | 0.015991 |
| Model2 | 1 | 0.235701 |
| Model2 | 0.3 | 0.085231 |
| Model2 | 0.1 | 0.030123 |
| Model2 | 0.03 | 0.009230 |
| Model2 | 0.01 | 0.003095 |
| Model3 | 1 | 0.807934 |
| Model3 | 0.01 | 0.750055 |
| Model3 | 0.001 | 0.596559 |

Small-epsilon log-log slopes: Model 1 = 0.947; Model 2 = 0.988. A first-order theorem predicts slope 1.
Model 3 at epsilon=0.001 gives TV=0.596559, while Model 1 at epsilon=1 gives TV=0.596559; these agree because the Model 3 SOS clock is exactly 1000x Model 1.

## History-filter reconstruction of the shipped SSA traces

| model | rhoSOS | history RMSE | instantaneous frozen RMSE | correlation | sample dt (s) |
|---|---:|---:|---:|---:|---:|
| Model1 | 10 | 11.54 | 176.01 | 0.9996 | 10.001 |
| Model2 | 30 | 15.80 | 43.10 | 0.9980 | 10.001 |
| Model3 | 10 | 32.50 | 458.53 | 0.5459 | 10.001 |

Models 1/2 are reconstructed extremely well from sampled occupancy history. Model 3 switches much faster than the 10 s sampling interval, so its unobserved within-sample SOS events cannot be reconstructed from the stored trajectory alone.
