# Scripts

This folder contains the R scripts required to reproduce the computational and graphical components of the FES-MADM II Version 1.1.0 reproducibility package.

## Contents

```text
FES_MADM_II_APP_V1_1_0.R
```

Main R/Shiny implementation of the FES-MADM II model. The application performs fuzzy α-cut processing, entropy-based weighting, subjective–objective integrated weighting, alternative scoring, entropy diagnostics, sensitivity analysis and structured Excel export.

```text
FES_MADM_II_all_figures_standalone_v1_1_0.R
```

Standalone R script with embedded data for reproducing all manuscript figures except the conceptual workflow diagram. The script is intended to support graphical reproducibility and layout verification.

```text
FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R
```

Standalone R script with embedded data for reproducing the fuzzy TOPSIS benchmark used for comparative validation. It computes fuzzy TOPSIS closeness coefficients, rankings, rank differences and rank-concordance indicators against FES-MADM II.

## Software requirements

The scripts were developed and tested under:

```text
R version 4.5.1
Windows 11, 64-bit
```

Main packages used across the scripts include:

```text
shiny
shinythemes
readxl
writexl
ggplot2
dplyr
DT
gridExtra
reshape2
ggrepel
grid
```

If a required package is missing, install it in R before running the scripts, for example:

```r
install.packages("writexl")
install.packages("ggplot2")
```

## Reproducibility note

All computational results are produced in R. The exported Excel files are static outputs intended for verification, documentation and replication. No Excel formulas are required for reproducing the benchmark results.
