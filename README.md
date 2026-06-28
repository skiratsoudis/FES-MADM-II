# FES-MADM II

## Fuzzy Entropy–Synergy Multi-Attribute Decision-Making Model

### R/Shiny Application and Reproducibility Package — Version 1.1.0

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21011321.svg)](https://doi.org/10.5281/zenodo.21011321)
![Release](https://img.shields.io/github/v/release/skiratsoudis/FES-MADM-II?label=release)
![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)
![R](https://img.shields.io/badge/R-4.5.1-blue)
![Platform](https://img.shields.io/badge/platform-Windows%2011-lightgrey)

---

## Overview

This repository contains the **FES-MADM II R/Shiny Application and Reproducibility Package** accompanying the manuscript:

**“FES-MADM II: A Fuzzy Entropy–Synergy Multi-Attribute Decision Framework for Information-Aware Assessment of National Logistics Performance.”**

FES-MADM II is a fuzzy entropy–synergy multi-attribute decision-making framework that extends the ES-MADM II model to uncertain evaluation environments. The model integrates α-cut-based triangular fuzzy representations, entropy-derived objective weighting, subjective–objective integrated weighting, fuzzy alternative scoring and information-theoretic diagnostic indices into a unified decision-support structure.

The empirical application evaluates national logistics performance using the World Bank Logistics Performance Index framework, covering thirteen countries and six logistics pillars.

---

## Version 1.1.0

Version 1.1.0 provides the revised reproducibility package prepared for the revised manuscript submission to *Operational Research*.

This release includes:

* corrected α-cut operationalisation for triangular fuzzy numbers, aligned with the standard interpretation where α = 0 corresponds to full support and α = 1 collapses to the central value;
* updated R/Shiny implementation of the FES-MADM II model;
* revised LPI input and output files for α = 0, α = 0.5 and α = 1;
* standalone R script with embedded data for reproducing all manuscript figures except the conceptual workflow diagram;
* standalone fuzzy TOPSIS benchmark script with embedded data;
* static fuzzy TOPSIS benchmark output file;
* folder-level documentation supporting computational, graphical and benchmark reproducibility.

---

## Main Capabilities

The implementation supports:

* triangular fuzzy performance representation;
* α-cut fuzzy interval processing;
* benefit/cost criteria handling;
* conditional fuzzy probability construction;
* entropy-based objective weighting;
* subjective–objective integrated weighting;
* fuzzy alternative score calculation;
* Integrated Criteria Importance analysis;
* entropy and joint-information diagnostics;
* diagnostic indices: NMI, CES, CSF, ADI and NMGI;
* sensitivity analysis across α-cut levels;
* fuzzy TOPSIS comparative benchmarking;
* structured Excel output export;
* standalone manuscript figure reproduction.

---

## Repository Structure

```text
FES-MADM-II/

├── scripts/
│   ├── README.md
│   ├── FES_MADM_II_APP_V1_1_0.R
│   ├── FES_MADM_II_all_figures_standalone_v1_1_0.R
│   └── FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R
│
├── data/
│   ├── README.md
│   │
│   ├── input/
│   │   ├── FESMADM2_CaseStudy_LPI_a0_INPUT.xlsx
│   │   ├── FESMADM2_CaseStudy_LPI_a0_5_INPUT.xlsx
│   │   └── FESMADM2_CaseStudy_LPI_a1_INPUT.xlsx
│   │
│   └── output/
│       ├── FESMADM2_CaseStudy_LPI_a0_v1_1_0.xlsx
│       ├── FESMADM2_CaseStudy_LPI_a0_5_v1_1_0.xlsx
│       └── FESMADM2_CaseStudy_LPI_a1_v1_1_0.xlsx
│
├── benchmark/
│   └── fuzzy_topsis/
│       ├── README.md
│       └── FESMADM2_Fuzzy_TOPSIS_Benchmark_v1_1_0_OUTPUT.xlsx
│
├── README.md
├── CHANGELOG.md
├── LICENSE
└── .gitignore
```

---

## Scripts

The `scripts/` folder contains the R scripts required for computational and graphical reproducibility.

### `FES_MADM_II_APP_V1_1_0.R`

Main R/Shiny application implementing the FES-MADM II framework. It performs fuzzy α-cut processing, entropy-based weighting, integrated subjective–objective weighting, alternative scoring, entropy diagnostics, sensitivity analysis and structured Excel export.

### `FES_MADM_II_all_figures_standalone_v1_1_0.R`

Standalone R script with embedded data for reproducing all manuscript figures except the conceptual workflow diagram. It is intended to support graphical reproducibility and final layout verification.

### `FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R`

Standalone R script with embedded data for reproducing the fuzzy TOPSIS benchmark used for comparative validation. It computes fuzzy TOPSIS closeness coefficients, rankings, rank differences and rank-concordance indicators against FES-MADM II.

---

## Data

The `data/` folder contains both input and output files for the LPI case study.

### Input files

The `data/input/` folder contains the case-study input workbooks used by the R/Shiny implementation. These include the central performance matrix, fuzzy deviation matrix, subjective weights, criteria orientation and α-cut configuration.

### Output files

The `data/output/` folder contains structured Excel outputs generated by the FES-MADM II R/Shiny application for:

```text
α = 0
α = 0.5
α = 1
```

These outputs include alternative scores, criteria weights, Integrated Criteria Importance values, entropy measures and entropy-based diagnostic indices.

---

## Fuzzy TOPSIS Benchmark

The `benchmark/fuzzy_topsis/` folder contains the static Excel output for the fuzzy TOPSIS benchmark.

The benchmark is computed entirely in R through the standalone script located in:

```text
scripts/FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R
```

The benchmark includes:

* triangular fuzzy performance representation;
* fuzzy subjective weights;
* fuzzy normalization under benefit-type criteria;
* Fuzzy Positive-Ideal Solution;
* Fuzzy Negative-Ideal Solution;
* vertex-distance calculation;
* fuzzy TOPSIS closeness coefficients;
* fuzzy TOPSIS ranking;
* rank comparison with FES-MADM II;
* Spearman rank correlation;
* Kendall tau-b rank correlation;
* pairwise concordance and discordance counts.

The Excel benchmark file contains static exported results and does not rely on Excel formulas. This avoids spreadsheet localisation issues such as `#NAME?` or `#ΟΝΟΜΑ?`.

---

## Software Requirements

The scripts were developed and tested under:

```text
R version 4.5.1
Windows 11, 64-bit
```

Main R packages used across the repository include:

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

Missing packages can be installed in R, for example:

```r
install.packages("shiny")
install.packages("readxl")
install.packages("writexl")
install.packages("ggplot2")
install.packages("dplyr")
install.packages("DT")
install.packages("gridExtra")
install.packages("reshape2")
install.packages("ggrepel")
```

---

## How to Run the R/Shiny Application

After downloading or cloning the repository, open R or RStudio and run:

```r
shiny::runApp("scripts/FES_MADM_II_APP_V1_1_0.R")
```

The application allows the user to upload the relevant input workbook, select the α-cut level, compute FES-MADM II outputs, inspect entropy-based diagnostics and export structured results.

---

## How to Reproduce the Manuscript Figures

Run:

```r
source("scripts/FES_MADM_II_all_figures_standalone_v1_1_0.R")
```

This script reproduces all manuscript figures except the conceptual workflow diagram.

---

## How to Reproduce the Fuzzy TOPSIS Benchmark

Run:

```r
source("scripts/FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R")
```

The script computes the fuzzy TOPSIS benchmark in R and exports the benchmark results as a static Excel file.

---

## Reproducibility Statement

All core computations are performed in R. The Excel files provided in this repository are static input or output files intended for transparency, verification and manuscript replication. The fuzzy TOPSIS benchmark and manuscript figures are generated by standalone R scripts with embedded data, ensuring that the reported results can be reproduced independently of spreadsheet formulas.

---

## DOI

The archived Version 1.1.0 release is available on Zenodo:

**https://doi.org/10.5281/zenodo.21011321**

---

## Recommended Citation

If you use this software, data or reproducibility package in academic work, please cite:

Kiratsoudis, S. (2026). *FES-MADM II R/Shiny Application and Reproducibility Package* (Version 1.1.0) [Software and data set]. Zenodo. https://doi.org/10.5281/zenodo.21011321

---

## License

This repository is distributed under the MIT License.
