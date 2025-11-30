# FES-MADM-II

R/Shiny implementation of the Fuzzy Entropy-based Multi-Attribute Decision-Making
framework FES-MADM II.

## Overview

FES-MADM II is a fuzzy–entropy multi-criteria decision model integrating
triangular fuzzy evaluations, entropy-based objective weights and
information-theoretic diagnostic indices (NMI, CES, CSF, ADI, NMGI) into a
unified decision-support framework.

This repository contains:
- `app.R`: the full R/Shiny application implementing FES-MADM II.
- `example_LPI.xlsx`: an illustrative dataset based on the World Bank
  Logistics Performance Index (LPI), used for the numerical example in the paper.

## Requirements

- R (≥ 4.5.1)
- Packages: `shiny`, `shinythemes`, `readxl`, `writexl`, `ggplot2`,
  `dplyr`, `DT`, `gridExtra`, `reshape2`, `ggrepel`.

## How to run

```r
library(shiny)
shiny::runApp("path/to/FES-MADM-II")
