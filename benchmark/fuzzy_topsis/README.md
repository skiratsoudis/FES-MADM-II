# Fuzzy TOPSIS Benchmark

This folder contains the fuzzy TOPSIS benchmark material used for the comparative validation of FES-MADM II at α = 0.5.

The benchmark supports the comparative validation section of the manuscript:

**“FES-MADM II: A Fuzzy Entropy–Synergy Multi-Attribute Decision Framework for Information-Aware Assessment of National Logistics Performance.”**

## Contents

```text
FESMADM2_Fuzzy_TOPSIS_Benchmark_v1_1_0_OUTPUT.xlsx
```

Static Excel output containing the fuzzy TOPSIS benchmark results and rank-concordance calculations.

The corresponding standalone R script is located in:

```text
scripts/FESMADM2_Fuzzy_TOPSIS_Benchmark_standalone_v1_1_0.R
```

## Methodological summary

The fuzzy TOPSIS benchmark is computed using the same LPI case-study structure and α-cut setting used for the FES-MADM II comparison at α = 0.5.

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

## Excel output sheets

The benchmark Excel file includes structured sheets such as:

```text
README
Input_LPI_Center
Input_LPI_Delta
Fuzzy_Weights
AlphaCut_TFN
Normalized_TFN
Weighted_TFN
Ideal_Solutions
Distances_CC
Fuzzy_TOPSIS_Benchmark
Rank_Concordance
Kendall_Pairs
Manuscript_Values
```

## Reproducibility note

All fuzzy TOPSIS calculations are performed in R. The Excel file contains static exported results and does not rely on Excel formulas. This avoids spreadsheet localisation issues such as `#NAME?` or `#ΟΝΟΜΑ?` and ensures that the benchmark is reproducible directly from the R script.
