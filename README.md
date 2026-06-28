# FES-MADM II Fuzzy Entropy–Synergy Multi-Attribute Decision-Making Model

## R/Shiny Application and Reproducibility Package — Version 1.1.0

**DOI:** to be updated after Zenodo Version 1.1.0 publication.

## Overview

FES-MADM II is a fuzzy entropy–synergy multi-attribute decision-making framework that extends the ES-MADM II model to uncertain evaluation environments. The model integrates α-cut-based triangular fuzzy representations, entropy-derived objective weights, subjective–objective integrated weighting, fuzzy alternative scoring and a suite of information-theoretic diagnostic indices into a unified decision-support structure.

This repository provides the R/Shiny implementation and reproducibility material accompanying the manuscript:

**“FES-MADM II: A Fuzzy Entropy–Synergy Multi-Attribute Decision Framework for Information-Aware Assessment of National Logistics Performance.”**

The case study evaluates national logistics performance using the World Bank Logistics Performance Index dataset for thirteen countries and six logistics pillars.

## Version 1.1.0 update

Version 1.1.0 provides the revised reproducibility package prepared for the revised manuscript submission.

This version includes:

* corrected α-cut operationalisation for triangular fuzzy numbers, aligned with the standard interpretation where α = 0 corresponds to the full support and α = 1 collapses to the central value;
* updated R/Shiny implementation of the FES-MADM II model;
* revised LPI output files for α = 0, α = 0.5 and α = 1;
* standalone R script with embedded data for reproducing all manuscript figures except the conceptual workflow diagram;
* standalone fuzzy TOPSIS benchmark script with embedded data;
* static fuzzy TOPSIS benchmark output file;
* updated documentation supporting computational and graphical reproducibility.

## Main features

The implementation provided here includes:

* fuzzy α-cut processing;
* triangular fuzzy performance representation;
* entropy-based objective weighting;
* subjective–objective integrated weighting;
* conditional fuzzy probability construction;
* fuzzy alternative score calculation;
* Integrated Criteria Importance analysis;
* entropy and joint-information diagnostics;
* decision-quality indices: NMI, CES, CSF, ADI and NMGI;
* sensitivity analysis across α-cut levels;
* fuzzy TOPSIS comparative benchmarking;
* structured Excel output export;
* standalone manuscript figure reproduction.

## ## Repository contents

```text
FES-MADM-II/

├── scripts/
│   ├── FES_MADM_II_APP_V1_1_0.R
│   │   Main R/Shiny implementation of the FES-MADM II model.
│   │
│   ├── FES_MADM_II_all_figures_standalone_v1_1_0.R
│   │   Standalone R script with embedded data for reproducing all manuscript figures
│   │   except the conceptual workflow diagram.
│   │
│   └── FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R
│       Standalone R script with embedded data for the fuzzy TOPSIS benchmark.
│
├── data/
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
│       └── FESMADM2_Fuzzy_TOPSIS_Benchmark_v1_1_0_OUTPUT.xlsx
│
├── README.md
├── CHANGELOG.md
├── LICENSE
└── .gitignore
```


LICENSE
MIT License.
```

## Software requirements

The R/Shiny application was developed and tested under:

```text
R version 4.5.1
Windows 11, 64-bit
```

The main R packages used are:

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

## Reproducibility notes

All core computations are performed in R. The Excel files provided in this repository are static output files generated from the R implementation and are intended for verification, reporting and replication purposes.

The fuzzy TOPSIS benchmark is also computed entirely in R through a standalone script. The corresponding Excel file contains the exported results and does not rely on Excel formulas, avoiding localisation issues such as `#NAME?` or `#ΟΝΟΜΑ?`.

The standalone figure-generation script reproduces all manuscript figures except the conceptual workflow diagram, which is a methodological schematic.

## Citation

If you use this software, data or reproducibility package in academic work, please cite:

Kiratsoudis, S. (2025). *FES-MADM II R/Shiny Application and Reproducibility Package* (Version 1.1.0) [Software and data set]. Zenodo. DOI to be updated after Zenodo Version 1.1.0 publication.

## License

This repository is distributed under the MIT License.
