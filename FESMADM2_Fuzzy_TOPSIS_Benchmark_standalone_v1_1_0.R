# =============================================================================
# FES-MADM II - Fuzzy TOPSIS Benchmark Script
# Version: 1.1.0 - fixed standalone benchmark export
# Manuscript: FES-MADM II: A Fuzzy Entropy-Synergy Multi-Attribute Decision
#             Framework for Information-Aware Assessment of National Logistics
#             Performance
#
# Purpose:
#   This standalone script reproduces the fuzzy TOPSIS benchmark used for the
#   comparative validation of FES-MADM II at alpha = 0.5.
#
# Important implementation notes:
#   - No external input files are required; all LPI case-study data are embedded.
#   - All fuzzy TOPSIS and rank-concordance calculations are performed in R.
#   - The exported Excel workbook contains static computed values only.
#   - No Excel formulas are written, avoiding localisation errors such as
#     #NAME? / #ΟΝΟΜΑ?.
#   - The script safely handles locked output files by writing a timestamped
#     alternative file if the standard filename is unavailable.
#
# Main outputs:
#   1) FESMADM2_Fuzzy_TOPSIS_Benchmark_v1_1_0.xlsx
#   2) Optional rank-concordance PNG figure, if ggplot2 is installed.
# =============================================================================

# -----------------------------
# 1. Basic settings
# -----------------------------

alpha <- 0.5
ROUND_DIGITS <- 6
DISPLAY_DIGITS <- 3
EXPORT_XLSX <- TRUE
EXPORT_PLOT <- TRUE
OUTPUT_PREFIX <- "FESMADM2_Fuzzy_TOPSIS_Benchmark_v1_1_0"
OUTPUT_DIR <- getwd()

round_out <- function(x) round(x, ROUND_DIGITS)
round_display <- function(x) round(x, DISPLAY_DIGITS)

rank_desc_min <- function(x) {
  as.integer(rank(-x, ties.method = "min"))
}

rank_desc_avg <- function(x) {
  rank(-x, ties.method = "average")
}

vertex_distance <- function(a, b) {
  sqrt(sum((a - b)^2) / 3)
}

safe_write_xlsx <- function(output_list, file_path) {
  if (!requireNamespace("writexl", quietly = TRUE)) {
    stop("Package 'writexl' is required for Excel export. Install it with install.packages('writexl').")
  }

  tryCatch({
    writexl::write_xlsx(output_list, path = file_path)
    normalizePath(file_path, winslash = "/", mustWork = FALSE)
  }, error = function(e) {
    timestamped <- file.path(
      dirname(file_path),
      paste0(tools::file_path_sans_ext(basename(file_path)),
             "_", format(Sys.time(), "%Y%m%d_%H%M%S"), ".xlsx")
    )
    message("Standard Excel output file could not be written, probably because it is open or locked.")
    message("Original error: ", conditionMessage(e))
    message("Writing timestamped alternative file instead.")
    writexl::write_xlsx(output_list, path = timestamped)
    normalizePath(timestamped, winslash = "/", mustWork = FALSE)
  })
}

# -----------------------------
# 2. Embedded case-study data
# -----------------------------

countries <- data.frame(
  Code = paste0("Y", 1:13),
  Country = c(
    "Singapore", "Germany", "Netherlands", "Japan", "United States",
    "United Kingdom", "France", "Italy", "Canada", "China", "India",
    "United Arab Emirates", "South Africa"
  ),
  stringsAsFactors = FALSE
)

criteria <- data.frame(
  Criterion = paste0("X", 1:6),
  Description = c(
    "Customs", "Infrastructure", "International Shipments",
    "Logistics Competence", "Tracking & Tracing", "Timeliness"
  ),
  Type = rep("Benefit", 6),
  stringsAsFactors = FALSE
)

# Central LPI data matrix, criteria in rows and alternatives in columns.
# Rows: X1-X6. Columns: Y1-Y13.
center_matrix <- matrix(c(
  4.2, 3.9, 3.9, 3.9, 3.7, 3.5, 3.7, 3.4, 4.0, 3.3, 3.0, 3.7, 2.6,
  4.6, 4.3, 4.2, 4.2, 3.9, 3.7, 3.8, 3.8, 4.3, 4.0, 3.2, 4.1, 2.8,
  4.0, 3.7, 3.7, 3.3, 3.4, 3.5, 3.7, 3.4, 3.6, 3.6, 3.5, 3.8, 2.7,
  4.4, 4.2, 4.2, 4.1, 3.9, 3.7, 3.8, 3.8, 4.2, 3.8, 3.5, 4.0, 2.7,
  4.4, 4.2, 4.2, 4.0, 4.2, 4.0, 4.0, 3.9, 4.1, 3.8, 3.4, 4.1, 2.9,
  4.3, 4.1, 4.0, 4.0, 3.8, 3.7, 4.1, 3.9, 4.1, 3.7, 3.6, 4.2, 3.1
), nrow = 6, byrow = TRUE)

# Empirical fuzzy deviations, criteria in rows and alternatives in columns.
delta_matrix <- matrix(c(
  0.31, 0.19, 0.02, 0.09, 0.08, 0.27, 0.11, 0.07, 0.40, 0.01, 0.04, 0.07, 0.57,
  0.54, 0.07, 0.01, 0.05, 0.15, 0.33, 0.20, 0.05, 0.55, 0.25, 0.29, 0.08, 0.39,
  0.42, 0.16, 0.02, 0.29, 0.11, 0.17, 0.15, 0.11, 0.22, 0.06, 0.29, 0.05, 0.81,
  0.30, 0.11, 0.11, 0.01, 0.03, 0.35, 0.04, 0.14, 0.30, 0.21, 0.37, 0.08, 0.49,
  0.32, 0.04, 0.18, 0.05, 0.11, 0.11, 0.00, 0.05, 0.29, 0.15, 0.08, 0.14, 0.51,
  0.02, 0.29, 0.25, 0.25, 0.28, 0.63, 0.05, 0.23, 0.14, 0.14, 0.10, 0.18, 0.64
), nrow = 6, byrow = TRUE)

rownames(center_matrix) <- criteria$Criterion
colnames(center_matrix) <- countries$Code
rownames(delta_matrix) <- criteria$Criterion
colnames(delta_matrix) <- countries$Code

# Equal fuzzy subjective weights used in the LPI case study.
weight_center <- rep(1 / 6, 6)
weight_delta  <- rep(0.05, 6)

# FES-MADM II reference scores/ranks at alpha = 0.5, used only for comparison.
fes_score <- c(0.083, 0.078, 0.077, 0.075, 0.073, 0.070, 0.073,
               0.070, 0.078, 0.070, 0.063, 0.075, 0.053)
fes_rank  <- c(1, 2, 4, 5, 7, 9, 7, 9, 2, 9, 12, 5, 13)

# -----------------------------
# 3. Fuzzy TOPSIS computation
# -----------------------------

compute_fuzzy_topsis <- function(center, delta, alpha, w_center, w_delta) {
  # Convert matrices to alternative x criterion orientation.
  C <- t(center)
  D <- t(delta)
  n_alt <- nrow(C)
  n_crit <- ncol(C)

  # Triangular fuzzy numbers at alpha-cut.
  L <- C - (1 - alpha) * D
  M <- C
  U <- C + (1 - alpha) * D

  # Benefit-type fuzzy normalization using maximum upper bound by criterion.
  max_upper <- apply(U, 2, max)
  R_L <- sweep(L, 2, max_upper, "/")
  R_M <- sweep(M, 2, max_upper, "/")
  R_U <- sweep(U, 2, max_upper, "/")

  # Fuzzy subjective weights at the same alpha-cut.
  W_L <- pmax(w_center - (1 - alpha) * w_delta, 0)
  W_M <- w_center
  W_U <- pmax(w_center + (1 - alpha) * w_delta, 0)

  # Weighted normalized triangular fuzzy matrix.
  V_L <- sweep(R_L, 2, W_L, "*")
  V_M <- sweep(R_M, 2, W_M, "*")
  V_U <- sweep(R_U, 2, W_U, "*")

  # Fuzzy Positive-Ideal Solution (FPIS) and Fuzzy Negative-Ideal Solution (FNIS).
  # Since all criteria are benefit-type, the ideal normalized performance is one.
  # After fuzzy weighting, FPIS is represented by the upper fuzzy weight.
  FPIS <- cbind(W_U, W_U, W_U)
  FNIS <- matrix(0, nrow = n_crit, ncol = 3)

  d_plus <- numeric(n_alt)
  d_minus <- numeric(n_alt)

  for (i in seq_len(n_alt)) {
    for (j in seq_len(n_crit)) {
      v_ij <- c(V_L[i, j], V_M[i, j], V_U[i, j])
      d_plus[i]  <- d_plus[i]  + vertex_distance(v_ij, FPIS[j, ])
      d_minus[i] <- d_minus[i] + vertex_distance(v_ij, FNIS[j, ])
    }
  }

  cc <- d_minus / (d_plus + d_minus)

  list(
    L = L, M = M, U = U,
    R_L = R_L, R_M = R_M, R_U = R_U,
    V_L = V_L, V_M = V_M, V_U = V_U,
    W_L = W_L, W_M = W_M, W_U = W_U,
    FPIS = FPIS, FNIS = FNIS,
    d_plus = d_plus,
    d_minus = d_minus,
    cc = cc,
    rank = rank_desc_min(cc)
  )
}

topsis <- compute_fuzzy_topsis(
  center = center_matrix,
  delta = delta_matrix,
  alpha = alpha,
  w_center = weight_center,
  w_delta = weight_delta
)

# -----------------------------
# 4. Helper tables
# -----------------------------

make_long_tfn_table <- function(L, M, U, value_prefix) {
  rows <- list()
  k <- 1
  for (i in seq_len(nrow(L))) {
    for (j in seq_len(ncol(L))) {
      rows[[k]] <- data.frame(
        Code = countries$Code[i],
        Country = countries$Country[i],
        Criterion = criteria$Criterion[j],
        Description = criteria$Description[j],
        Lower = round_out(L[i, j]),
        Center = round_out(M[i, j]),
        Upper = round_out(U[i, j]),
        stringsAsFactors = FALSE
      )
      k <- k + 1
    }
  }
  names(rows) <- NULL
  out <- do.call(rbind, rows)
  names(out)[5:7] <- paste0(value_prefix, c("_Lower", "_Center", "_Upper"))
  out
}

alpha_cut_tfn <- make_long_tfn_table(topsis$L, topsis$M, topsis$U, "AlphaCut")
normalized_tfn <- make_long_tfn_table(topsis$R_L, topsis$R_M, topsis$R_U, "Normalized")
weighted_tfn <- make_long_tfn_table(topsis$V_L, topsis$V_M, topsis$V_U, "WeightedNormalized")

input_lpi_center <- data.frame(
  Code = countries$Code,
  Country = countries$Country,
  t(center_matrix),
  stringsAsFactors = FALSE,
  check.names = FALSE
)
colnames(input_lpi_center)[3:8] <- paste0(criteria$Criterion, "_", criteria$Description)

input_lpi_delta <- data.frame(
  Code = countries$Code,
  Country = countries$Country,
  t(delta_matrix),
  stringsAsFactors = FALSE,
  check.names = FALSE
)
colnames(input_lpi_delta)[3:8] <- paste0(criteria$Criterion, "_Delta")

fuzzy_weights <- data.frame(
  Criterion = criteria$Criterion,
  Description = criteria$Description,
  Type = criteria$Type,
  Weight_Lower = round_out(topsis$W_L),
  Weight_Center = round_out(topsis$W_M),
  Weight_Upper = round_out(topsis$W_U),
  stringsAsFactors = FALSE
)

ideal_solutions <- data.frame(
  Criterion = criteria$Criterion,
  Description = criteria$Description,
  FPIS_Lower = round_out(topsis$FPIS[, 1]),
  FPIS_Center = round_out(topsis$FPIS[, 2]),
  FPIS_Upper = round_out(topsis$FPIS[, 3]),
  FNIS_Lower = round_out(topsis$FNIS[, 1]),
  FNIS_Center = round_out(topsis$FNIS[, 2]),
  FNIS_Upper = round_out(topsis$FNIS[, 3]),
  stringsAsFactors = FALSE
)

distances_cc <- data.frame(
  Code = countries$Code,
  Country = countries$Country,
  D_plus = round_out(topsis$d_plus),
  D_minus = round_out(topsis$d_minus),
  Closeness_Coefficient = round_out(topsis$cc),
  Fuzzy_TOPSIS_rank = topsis$rank,
  stringsAsFactors = FALSE
)

benchmark_table <- data.frame(
  Code = countries$Code,
  Country = countries$Country,
  FES_MADM_II_score = round_out(fes_score),
  FES_rank = fes_rank,
  Fuzzy_TOPSIS_CC = round_out(topsis$cc),
  Fuzzy_TOPSIS_rank = topsis$rank,
  DeltaRank = topsis$rank - fes_rank,
  Abs_DeltaRank = abs(topsis$rank - fes_rank),
  stringsAsFactors = FALSE
)

fes_avg_rank <- rank_desc_avg(fes_score)
topsis_avg_rank <- rank_desc_avg(topsis$cc)

kendall_counts <- function(x, y) {
  n <- length(x)
  concordant <- 0
  discordant <- 0
  tie_x_only <- 0
  tie_y_only <- 0
  tie_both <- 0
  pair_rows <- list()
  k <- 1

  for (i in 1:(n - 1)) {
    for (j in (i + 1):n) {
      dx <- sign(x[i] - x[j])
      dy <- sign(y[i] - y[j])

      is_conc <- 0
      is_disc <- 0
      is_tx <- 0
      is_ty <- 0
      is_tb <- 0

      if (dx == 0 && dy == 0) {
        tie_both <- tie_both + 1
        is_tb <- 1
      } else if (dx == 0 && dy != 0) {
        tie_x_only <- tie_x_only + 1
        is_tx <- 1
      } else if (dx != 0 && dy == 0) {
        tie_y_only <- tie_y_only + 1
        is_ty <- 1
      } else if (dx == dy) {
        concordant <- concordant + 1
        is_conc <- 1
      } else {
        discordant <- discordant + 1
        is_disc <- 1
      }

      pair_rows[[k]] <- data.frame(
        Pair_i = countries$Code[i],
        Pair_j = countries$Code[j],
        FES_rank_i = x[i],
        FES_rank_j = x[j],
        TOPSIS_rank_i = y[i],
        TOPSIS_rank_j = y[j],
        Concordant = is_conc,
        Discordant = is_disc,
        Tie_FES_only = is_tx,
        Tie_TOPSIS_only = is_ty,
        Tie_both = is_tb,
        stringsAsFactors = FALSE
      )
      k <- k + 1
    }
  }

  denom <- sqrt((concordant + discordant + tie_x_only) *
                  (concordant + discordant + tie_y_only))
  tau_b <- ifelse(denom > 0, (concordant - discordant) / denom, NA_real_)

  list(
    concordant = concordant,
    discordant = discordant,
    tie_x_only = tie_x_only,
    tie_y_only = tie_y_only,
    tie_both = tie_both,
    tau_b = tau_b,
    pairs = do.call(rbind, pair_rows)
  )
}

kendall <- kendall_counts(fes_rank, topsis$rank)

rank_concordance <- data.frame(
  Indicator = c(
    "Spearman rank correlation",
    "Kendall rank correlation (tau-b)",
    "Alternatives with identical rank",
    "Mean absolute rank difference",
    "Maximum absolute rank difference",
    "Concordant pairs",
    "Discordant pairs",
    "Ties in FES rank only",
    "Ties in TOPSIS rank only",
    "Ties in both rankings"
  ),
  Value = round_out(c(
    cor(fes_avg_rank, topsis_avg_rank, method = "pearson"),
    kendall$tau_b,
    sum(benchmark_table$DeltaRank == 0),
    mean(benchmark_table$Abs_DeltaRank),
    max(benchmark_table$Abs_DeltaRank),
    kendall$concordant,
    kendall$discordant,
    kendall$tie_x_only,
    kendall$tie_y_only,
    kendall$tie_both
  )),
  stringsAsFactors = FALSE
)

manuscript_values <- data.frame(
  Field = c(
    "Spearman rho",
    "Kendall tau-b",
    "Identical ranks",
    "Mean absolute rank difference",
    "Maximum absolute rank difference",
    "Fuzzy TOPSIS CC - Y1",
    "Fuzzy TOPSIS CC - Y2",
    "Fuzzy TOPSIS CC - Y3",
    "Fuzzy TOPSIS CC - Y4",
    "Fuzzy TOPSIS CC - Y5",
    "Fuzzy TOPSIS CC - Y6",
    "Fuzzy TOPSIS CC - Y7",
    "Fuzzy TOPSIS CC - Y8",
    "Fuzzy TOPSIS CC - Y9",
    "Fuzzy TOPSIS CC - Y10",
    "Fuzzy TOPSIS CC - Y11",
    "Fuzzy TOPSIS CC - Y12",
    "Fuzzy TOPSIS CC - Y13"
  ),
  Value = round_out(c(
    rank_concordance$Value[1],
    rank_concordance$Value[2],
    rank_concordance$Value[3],
    rank_concordance$Value[4],
    rank_concordance$Value[5],
    topsis$cc
  )),
  stringsAsFactors = FALSE
)

# -----------------------------
# 5. Console report
# -----------------------------

cat("\nFuzzy TOPSIS benchmark completed successfully.\n")
cat(sprintf("Alpha-cut: %.1f\n", alpha))
cat("\nBenchmark table:\n")
print(transform(benchmark_table,
                FES_MADM_II_score = round_display(FES_MADM_II_score),
                Fuzzy_TOPSIS_CC = round_display(Fuzzy_TOPSIS_CC)))
cat("\nRank-concordance indicators:\n")
print(rank_concordance)

# -----------------------------
# 6. Excel export with static calculated values
# -----------------------------

if (EXPORT_XLSX) {
  output_list <- list(
    README = data.frame(
      Field = c("Script", "Version", "Alpha-cut", "Method", "Distance", "Excel output"),
      Value = c(
        "FES-MADM II fuzzy TOPSIS benchmark",
        "1.1.0",
        alpha,
        "Benefit-type fuzzy TOPSIS with alpha-cut triangular fuzzy data and fuzzy subjective weights",
        "Vertex distance between triangular fuzzy numbers",
        "Static values only; all calculations are performed in R; no Excel formulas are written"
      ),
      stringsAsFactors = FALSE
    ),
    Input_LPI_Center = input_lpi_center,
    Input_LPI_Delta = input_lpi_delta,
    Fuzzy_Weights = fuzzy_weights,
    AlphaCut_TFN = alpha_cut_tfn,
    Normalized_TFN = normalized_tfn,
    Weighted_TFN = weighted_tfn,
    Ideal_Solutions = ideal_solutions,
    Distances_CC = distances_cc,
    Fuzzy_TOPSIS_Benchmark = benchmark_table,
    Rank_Concordance = rank_concordance,
    Kendall_Pairs = kendall$pairs,
    Manuscript_Values = manuscript_values
  )

  output_file <- file.path(OUTPUT_DIR, paste0(OUTPUT_PREFIX, ".xlsx"))
  written_file <- safe_write_xlsx(output_list, output_file)
  cat(sprintf("\nExcel file written: %s\n", written_file))
}

# -----------------------------
# 7. Optional plot export
# -----------------------------

if (EXPORT_PLOT && requireNamespace("ggplot2", quietly = TRUE)) {
  p <- ggplot2::ggplot(benchmark_table,
                       ggplot2::aes(x = FES_rank, y = Fuzzy_TOPSIS_rank)) +
    ggplot2::geom_abline(intercept = 0, slope = 1, linetype = "dashed") +
    ggplot2::geom_point(size = 3) +
    ggplot2::geom_text(ggplot2::aes(label = Code), vjust = -0.7, size = 3.8) +
    ggplot2::scale_x_reverse(breaks = 1:13, limits = c(13.5, 0.5)) +
    ggplot2::scale_y_reverse(breaks = 1:13, limits = c(13.5, 0.5)) +
    ggplot2::labs(
      title = "Rank Concordance: FES-MADM II vs Fuzzy TOPSIS",
      subtitle = sprintf("Spearman rho = %.3f; Kendall tau-b = %.3f",
                         rank_concordance$Value[1], rank_concordance$Value[2]),
      x = "FES-MADM II rank at alpha = 0.5 (1 = best)",
      y = "Fuzzy TOPSIS rank (1 = best)"
    ) +
    ggplot2::theme_minimal(base_size = 13)

  plot_file <- file.path(OUTPUT_DIR, paste0(OUTPUT_PREFIX, "_Rank_Concordance.png"))
  ggplot2::ggsave(
    filename = plot_file,
    plot = p,
    width = 8.5,
    height = 7.0,
    dpi = 600
  )
  cat(sprintf("Plot written: %s\n", normalizePath(plot_file, winslash = "/", mustWork = FALSE)))
}
