###############################################################################
# FES-MADM II - Standalone Figure Generator
# Revised manuscript figure set, excluding Figure 1 (workflow diagram)
#
# Purpose:
#   - Produces Figures 2-13 directly in the RStudio Plots pane/history.
#   - All data are embedded in this script. No Excel or external data files are required.
#   - Optional PNG export can be enabled by setting SAVE_FIGURES <- TRUE.
#   - Dense line/scatter/slope labels are automatically repelled to reduce overlap.
#
# Recommended use:
#   1. Open this file in RStudio.
#   2. Adjust DEVICE_WIDTH and DEVICE_HEIGHT only if you later export figures.
#   3. Source the script.
#   4. All figures are generated in one run and remain available in the Plots pane history.
###############################################################################

# -----------------------------------------------------------------------------
# 0. User controls
# -----------------------------------------------------------------------------
RUN_ALL_ON_SOURCE      <- TRUE   # Set FALSE if you want to call figures manually.
OPEN_NEW_DEVICE        <- FALSE  # FALSE sends all figures to the RStudio Plots pane/history.
PAUSE_BETWEEN_FIGURES  <- FALSE  # FALSE produces all figures in one run, without prompts.
SAVE_FIGURES           <- FALSE  # TRUE saves PNGs in OUTPUT_DIR.
OUTPUT_DIR             <- "FES_MADM_II_generated_figures"
DEVICE_WIDTH           <- 13
DEVICE_HEIGHT          <- 7.5
EXPORT_DPI             <- 600

# Publication readability controls.
# Increase/decrease these three values if the inserted Word figures need adjustment.
PLOT_BASE_SIZE         <- 15
VALUE_LABEL_SIZE       <- 3.7
SMALL_VALUE_LABEL_SIZE <- 3.35
POINT_SIZE             <- 3.0

# -----------------------------------------------------------------------------
# 1. Packages
# -----------------------------------------------------------------------------
required_packages <- c("ggplot2", "gridExtra", "grid", "ggrepel")
missing_packages <- required_packages[!vapply(required_packages, requireNamespace, logical(1), quietly = TRUE)]
if (length(missing_packages) > 0) {
  stop(
    "The following R packages are required but not installed: ",
    paste(missing_packages, collapse = ", "),
    "\nInstall them with: install.packages(c(",
    paste(sprintf('"%s"', missing_packages), collapse = ", "),
    "))"
  )
}

library(ggplot2)
library(gridExtra)
library(grid)
library(ggrepel)

# -----------------------------------------------------------------------------
# 2. Plot helpers
# -----------------------------------------------------------------------------
fmt3 <- function(x) sprintf("%.3f", x)

base_theme <- function(base_size = PLOT_BASE_SIZE) {
  theme_minimal(base_size = base_size) +
    theme(
      plot.title = element_text(face = "bold", hjust = 0.5, size = base_size + 3),
      plot.subtitle = element_text(hjust = 0.5, size = base_size),
      axis.title = element_text(face = "bold", size = base_size + 1),
      axis.text = element_text(size = base_size),
      axis.text.x = element_text(angle = 0, vjust = 0.5),
      axis.text.y = element_text(size = base_size),
      legend.position = "bottom",
      legend.title = element_blank(),
      legend.text = element_text(size = base_size - 1),
      strip.text = element_text(size = base_size + 1, face = "bold"),
      panel.grid.minor = element_blank(),
      plot.margin = margin(14, 14, 14, 14)
    )
}

# Non-overlapping value labels for dense line/scatter/slope plots.
# ggrepel automatically moves labels away from each other while keeping them
# associated with their points via subtle connector segments.
repel_value_labels <- function(mapping = aes(label = fmt3(Value)), size = VALUE_LABEL_SIZE, nudge_y = 0, nudge_x = 0, direction = "both") {
  ggrepel::geom_text_repel(
    mapping = mapping,
    size = size,
    show.legend = FALSE,
    box.padding = 0.22,
    point.padding = 0.16,
    min.segment.length = 0,
    segment.alpha = 0.45,
    segment.size = 0.25,
    max.overlaps = Inf,
    seed = 42,
    nudge_y = nudge_y,
    nudge_x = nudge_x,
    direction = direction
  )
}

open_device <- function(width = DEVICE_WIDTH, height = DEVICE_HEIGHT) {
  if (!OPEN_NEW_DEVICE) return(invisible(NULL))
  grDevices::dev.new(width = width, height = height, noRStudioGD = FALSE)
}

display_plot <- function(plot_object, figure_name, width = DEVICE_WIDTH, height = DEVICE_HEIGHT) {
  open_device(width, height)
  if (inherits(plot_object, "grob") || inherits(plot_object, "gtable")) {
    grid::grid.newpage()
    grid::grid.draw(plot_object)
  } else {
    print(plot_object)
  }

  if (SAVE_FIGURES) {
    if (!dir.exists(OUTPUT_DIR)) dir.create(OUTPUT_DIR, recursive = TRUE)
    file_png <- file.path(OUTPUT_DIR, paste0(figure_name, ".png"))
    ggplot2::ggsave(
      filename = file_png,
      plot = plot_object,
      width = width,
      height = height,
      dpi = EXPORT_DPI,
      units = "in",
      bg = "white"
    )
    message("Saved: ", normalizePath(file_png, winslash = "/", mustWork = FALSE))
  }

  if (PAUSE_BETWEEN_FIGURES && interactive()) {
    invisible(readline(prompt = paste0("Displayed ", figure_name, ". Press <Enter> for next figure...")))
  }
  invisible(plot_object)
}

rank_desc <- function(x) rank(-x, ties.method = "min")
rank_asc <- function(x) rank(x, ties.method = "min")

# -----------------------------------------------------------------------------
# 3. Embedded data
# -----------------------------------------------------------------------------

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
  stringsAsFactors = FALSE
)

# Figure 2 / Table 8: baseline alternative scores at alpha = 0.5
alt_alpha05 <- data.frame(
  Code = paste0("Y", 1:13),
  Fuzzy_Lower = c(0.076, 0.073, 0.073, 0.071, 0.069, 0.064, 0.069, 0.066, 0.071, 0.066, 0.059, 0.072, 0.046),
  Fuzzy_Upper = c(0.089, 0.082, 0.081, 0.079, 0.077, 0.076, 0.077, 0.074, 0.084, 0.074, 0.068, 0.079, 0.060),
  Crisp       = c(0.083, 0.078, 0.077, 0.075, 0.073, 0.070, 0.073, 0.070, 0.078, 0.070, 0.063, 0.075, 0.053),
  Rank        = c(1, 2, 4, 5, 7, 9, 7, 9, 2, 9, 12, 5, 13),
  stringsAsFactors = FALSE
)
alt_alpha05 <- merge(alt_alpha05, countries, by = "Code", sort = FALSE)
alt_alpha05$Code <- factor(alt_alpha05$Code, levels = paste0("Y", 1:13))

# Figure 3 / Table 9: subjective, objective and integrated weights at alpha = 0.5
weights_alpha05 <- data.frame(
  Criterion = paste0("X", 1:6),
  SBJ_Lower = rep(0.142, 6),
  SBJ_Upper = rep(0.192, 6),
  SBJ_Crisp = rep(0.167, 6),
  OBJ_Lower = c(0.201, 0.197, 0.088, 0.178, 0.144, 0.077),
  OBJ_Upper = c(0.244, 0.259, 0.150, 0.188, 0.154, 0.120),
  OBJ_Crisp = c(0.223, 0.228, 0.119, 0.183, 0.149, 0.098),
  INT_Lower = c(0.219, 0.222, 0.100, 0.169, 0.138, 0.086),
  INT_Upper = c(0.227, 0.232, 0.134, 0.201, 0.163, 0.107),
  INT_Crisp = c(0.223, 0.227, 0.117, 0.185, 0.151, 0.097),
  stringsAsFactors = FALSE
)
weights_alpha05 <- merge(weights_alpha05, criteria, by = "Criterion", sort = FALSE)
weights_alpha05$Criterion <- factor(weights_alpha05$Criterion, levels = paste0("X", 1:6))

# Figure 4 / Table 10: Integrated Criteria Importance at alpha = 0.5
ici_alpha05 <- data.frame(
  Criterion = paste0("X", 1:6),
  Fuzzy_Lower = c(0.807, 0.820, 0.367, 0.622, 0.510, 0.319),
  Fuzzy_Upper = c(0.839, 0.858, 0.497, 0.744, 0.602, 0.397),
  Crisp       = c(0.823, 0.839, 0.432, 0.683, 0.556, 0.358),
  stringsAsFactors = FALSE
)
ici_alpha05$Criterion <- factor(ici_alpha05$Criterion, levels = paste0("X", 1:6))

# Figure 5 / Table 11: entropy measures at alpha = 0.5
entropy_alpha05 <- data.frame(
  Measure = c("S(X,Y)", "S(X)", "S(Y)", "I(X;Y)", "S(Y|X)", "I(Y|X)"),
  Fuzzy_Lower = c(5.873, 2.426, 3.401, 0.000, 3.446, 0.000),
  Fuzzy_Upper = c(6.539, 2.602, 3.694, 0.000, 3.937, 0.000),
  Crisp       = c(6.206, 2.514, 3.548, 0.000, 3.692, 0.000),
  stringsAsFactors = FALSE
)
entropy_alpha05$Measure <- factor(entropy_alpha05$Measure, levels = entropy_alpha05$Measure)

# Figure 6 / Table 12: entropy-based diagnostic indices at alpha = 0.5
indices_alpha05 <- data.frame(
  Index = c("NMI", "ADI", "CES", "CSF", "NMGI"),
  Fuzzy_Lower = c(0.000, 0.002, 0.000, 0.000, 0.000),
  Fuzzy_Upper = c(0.000, 0.081, 0.248, 0.000, 0.072),
  Crisp       = c(0.000, 0.041, 0.124, 0.000, 0.036),
  stringsAsFactors = FALSE
)
indices_alpha05$Index <- factor(indices_alpha05$Index, levels = indices_alpha05$Index)

# Figure 7 / Table 13: alternative scores across alpha-cuts
alt_alpha <- data.frame(
  Code = paste0("Y", 1:13),
  a0   = c(0.080, 0.075, 0.074, 0.072, 0.070, 0.067, 0.070, 0.067, 0.075, 0.068, 0.061, 0.073, 0.051),
  a05  = c(0.083, 0.078, 0.077, 0.075, 0.073, 0.070, 0.073, 0.070, 0.078, 0.070, 0.063, 0.075, 0.053),
  a1   = c(0.088, 0.083, 0.082, 0.080, 0.078, 0.075, 0.078, 0.075, 0.083, 0.075, 0.067, 0.080, 0.056),
  stringsAsFactors = FALSE
)
alt_alpha$Code <- factor(alt_alpha$Code, levels = paste0("Y", 1:13))

# Figure 8 / Tables 14-15: integrated weights and ICI across alpha-cuts
xint_alpha <- data.frame(
  Criterion = paste0("X", 1:6),
  a0  = c(0.226, 0.228, 0.125, 0.176, 0.148, 0.098),
  a05 = c(0.223, 0.227, 0.117, 0.185, 0.151, 0.097),
  a1  = c(0.221, 0.226, 0.116, 0.188, 0.151, 0.098),
  stringsAsFactors = FALSE
)
xint_alpha$Criterion <- factor(xint_alpha$Criterion, levels = paste0("X", 1:6))

ici_alpha <- data.frame(
  Criterion = paste0("X", 1:6),
  a0  = c(0.834, 0.840, 0.460, 0.650, 0.546, 0.360),
  a05 = c(0.823, 0.839, 0.432, 0.683, 0.556, 0.358),
  a1  = c(0.816, 0.835, 0.428, 0.693, 0.559, 0.361),
  stringsAsFactors = FALSE
)
ici_alpha$Criterion <- factor(ici_alpha$Criterion, levels = paste0("X", 1:6))

# Figure 9 / Table 16: entropy measures across alpha-cuts
entropy_alpha <- data.frame(
  Measure = c("S(X,Y)", "S(X)", "S(Y)", "S(Y|X)"),
  a0  = c(6.201, 2.510, 3.458, 3.690),
  a05 = c(6.206, 2.514, 3.548, 3.692),
  a1  = c(6.212, 2.520, 3.693, 3.692),
  stringsAsFactors = FALSE
)
entropy_alpha$Measure <- factor(entropy_alpha$Measure, levels = entropy_alpha$Measure)

# Figure 10 / Table 17: diagnostic indices across alpha-cuts
indices_alpha <- data.frame(
  Index = c("NMI", "ADI", "CES", "CSF", "NMGI"),
  a0  = c(0.000, 0.066, 0.204, 0.000, 0.059),
  a05 = c(0.000, 0.041, 0.124, 0.000, 0.036),
  a1  = c(0.000, 0.002, 0.001, 0.000, 0.001),
  stringsAsFactors = FALSE
)
indices_alpha$Index <- factor(indices_alpha$Index, levels = indices_alpha$Index)

# Figures 11-12 / Tables 18-19: LPI vs FES-MADM II comparison
comparison_lpi_fes <- data.frame(
  Code = c("Y1", "Y2", "Y9", "Y3", "Y12", "Y4", "Y7", "Y5", "Y10", "Y8", "Y6", "Y11", "Y13"),
  Country = c(
    "Singapore", "Germany", "Canada", "Netherlands", "United Arab Emirates", "Japan",
    "France", "United States", "China", "Italy", "United Kingdom", "India", "South Africa"
  ),
  LPI_score = c(4.317, 4.067, 4.050, 4.033, 3.983, 3.917, 3.850, 3.817, 3.700, 3.700, 3.683, 3.367, 2.800),
  LPI_rank = c(1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 11, 12, 13),
  FES_score = c(0.083, 0.078, 0.078, 0.077, 0.075, 0.075, 0.073, 0.073, 0.070, 0.070, 0.070, 0.063, 0.053),
  FES_rank = c(1, 2, 2, 4, 5, 5, 7, 7, 9, 9, 9, 12, 13),
  stringsAsFactors = FALSE
)
comparison_lpi_fes$DeltaRank <- comparison_lpi_fes$FES_rank - comparison_lpi_fes$LPI_rank
comparison_lpi_fes$Status <- ifelse(comparison_lpi_fes$DeltaRank < 0, "Improved",
                                    ifelse(comparison_lpi_fes$DeltaRank > 0, "Declined", "Unchanged"))
comparison_lpi_fes$LPI_norm <- 100 * (comparison_lpi_fes$LPI_score - min(comparison_lpi_fes$LPI_score)) /
  (max(comparison_lpi_fes$LPI_score) - min(comparison_lpi_fes$LPI_score))
comparison_lpi_fes$FES_norm <- 100 * (comparison_lpi_fes$FES_score - min(comparison_lpi_fes$FES_score)) /
  (max(comparison_lpi_fes$FES_score) - min(comparison_lpi_fes$FES_score))

# Figure 13 / Tables 20-21: fuzzy TOPSIS benchmark
benchmark_topsis <- data.frame(
  Code = paste0("Y", 1:13),
  Country = countries$Country,
  FES_score = c(0.083, 0.078, 0.077, 0.075, 0.073, 0.070, 0.073, 0.070, 0.078, 0.070, 0.063, 0.075, 0.053),
  FES_rank  = c(1, 2, 4, 5, 7, 9, 7, 9, 2, 9, 12, 5, 13),
  TOPSIS_CC = c(0.835, 0.755, 0.744, 0.695, 0.656, 0.597, 0.674, 0.609, 0.739, 0.607, 0.476, 0.725, 0.281),
  TOPSIS_rank = c(1, 2, 3, 6, 8, 11, 7, 9, 4, 10, 12, 5, 13),
  stringsAsFactors = FALSE
)
benchmark_topsis$DeltaRank <- benchmark_topsis$TOPSIS_rank - benchmark_topsis$FES_rank
benchmark_topsis$Status <- ifelse(benchmark_topsis$DeltaRank == 0, "Identical rank", "Rank shift")

# -----------------------------------------------------------------------------
# 4. Small data reshaping helpers
# -----------------------------------------------------------------------------
to_long_three <- function(df, id_col, value_cols, labels) {
  out <- do.call(rbind, lapply(seq_along(value_cols), function(k) {
    data.frame(
      ID = df[[id_col]],
      Series = labels[k],
      Value = df[[value_cols[k]]],
      stringsAsFactors = FALSE
    )
  }))
  names(out)[names(out) == "ID"] <- id_col
  out
}

alpha_long <- function(df, id_col) {
  out <- rbind(
    data.frame(ID = df[[id_col]], Alpha = "α=0",   Value = df$a0,  stringsAsFactors = FALSE),
    data.frame(ID = df[[id_col]], Alpha = "α=0.5", Value = df$a05, stringsAsFactors = FALSE),
    data.frame(ID = df[[id_col]], Alpha = "α=1",   Value = df$a1,  stringsAsFactors = FALSE)
  )
  names(out)[names(out) == "ID"] <- id_col
  out$Alpha <- factor(out$Alpha, levels = c("α=0", "α=0.5", "α=1"))
  out
}

# -----------------------------------------------------------------------------
# 5. Figure functions
# -----------------------------------------------------------------------------

fig2 <- function(show = TRUE) {
  bars <- to_long_three(alt_alpha05, "Code", c("Fuzzy_Lower", "Fuzzy_Upper"), c("Fuzzy lower", "Fuzzy upper"))
  bars$Code <- factor(bars$Code, levels = paste0("Y", 1:13))

  p <- ggplot() +
    geom_col(data = bars, aes(x = Code, y = Value, fill = Series), position = position_dodge(width = 0.75), width = 0.65) +
    geom_line(data = alt_alpha05, aes(x = Code, y = Crisp, group = 1, colour = "Crisp"), linewidth = 1.0) +
    geom_point(data = alt_alpha05, aes(x = Code, y = Crisp, colour = "Crisp"), size = POINT_SIZE) +
    ggrepel::geom_text_repel(data = alt_alpha05, aes(x = Code, y = Crisp, label = fmt3(Crisp)),
                           size = VALUE_LABEL_SIZE, show.legend = FALSE, max.overlaps = Inf, seed = 42,
                           box.padding = 0.22, point.padding = 0.16, min.segment.length = 0) +
    scale_y_continuous(limits = c(0, 0.10), breaks = seq(0, 0.10, 0.01)) +
    labs(title = "Figure 2. FES-MADM II fuzzy alternative scores at α = 0.5", x = "Alternative", y = "Score") +
    base_theme() +
    theme(axis.text.x = element_text(angle = 0))
  if (show) display_plot(p, "fig2_alternative_scores_alpha05")
  invisible(p)
}

fig3 <- function(show = TRUE) {
  # Cleaner panel-based layout:
  # Instead of placing nine long component names on one x-axis, the figure is
  # split into three panels (subjective, objective, integrated). Each panel has
  # only Lower / Upper / Crisp on the x-axis, which prevents truncation in Word.
  long <- data.frame()
  for (crit in as.character(weights_alpha05$Criterion)) {
    row <- weights_alpha05[weights_alpha05$Criterion == crit, ]
    long <- rbind(long, data.frame(
      Criterion = crit,
      Weight_Set = factor(rep(c("Subjective weights xSBJ", "Objective weights xOBJ", "Integrated weights xINT"), each = 3),
                          levels = c("Subjective weights xSBJ", "Objective weights xOBJ", "Integrated weights xINT")),
      Bound = factor(rep(c("Lower", "Upper", "Crisp"), times = 3), levels = c("Lower", "Upper", "Crisp")),
      Value = c(row$SBJ_Lower, row$SBJ_Upper, row$SBJ_Crisp,
                row$OBJ_Lower, row$OBJ_Upper, row$OBJ_Crisp,
                row$INT_Lower, row$INT_Upper, row$INT_Crisp),
      stringsAsFactors = FALSE
    ))
  }
  long$Criterion <- factor(long$Criterion, levels = paste0("X", 1:6))
  long$BoundNum <- as.numeric(long$Bound)

  # Manually stack labels at each panel/bound combination. This is more reliable
  # than automatic repulsion when several values are identical or nearly identical.
  crit_offsets_x <- c(-0.22, -0.13, -0.04, 0.04, 0.13, 0.22)
  names(crit_offsets_x) <- levels(long$Criterion)
  long$LabelX <- long$BoundNum + crit_offsets_x[as.character(long$Criterion)]
  long$LabelY <- NA_real_

  for (ws in levels(long$Weight_Set)) {
    for (bd in levels(long$Bound)) {
      idx <- which(long$Weight_Set == ws & long$Bound == bd)
      sub <- long[idx, ]
      ord <- order(-sub$Value, as.character(sub$Criterion))
      idx_ord <- idx[ord]
      top_base <- max(long$Value[idx]) + 0.030
      step <- 0.0125
      long$LabelY[idx_ord] <- top_base - step * (seq_along(idx_ord) - 1)
    }
  }

  p <- ggplot(long, aes(x = BoundNum, y = Value, group = Criterion, colour = Criterion)) +
    geom_line(linewidth = 0.95) +
    geom_point(size = POINT_SIZE) +
    geom_segment(aes(xend = LabelX, yend = LabelY),
                 linewidth = 0.25, alpha = 0.55, show.legend = FALSE) +
    geom_label(aes(x = LabelX, y = LabelY, label = fmt3(Value), fill = Criterion),
               size = SMALL_VALUE_LABEL_SIZE, label.size = 0.12,
               label.padding = grid::unit(0.08, "lines"),
               show.legend = FALSE, colour = "black", alpha = 0.94) +
    facet_wrap(~ Weight_Set, nrow = 1) +
    scale_x_continuous(breaks = 1:3, labels = c("Lower", "Upper", "Crisp"), limits = c(0.65, 3.35)) +
    scale_y_continuous(limits = c(0.045, 0.315), breaks = seq(0.05, 0.30, 0.05), expand = expansion(mult = c(0.02, 0.02))) +
    labs(title = "Figure 3. Subjective, objective and integrated criteria weights at α = 0.5", x = NULL, y = "Weight") +
    base_theme() +
    theme(axis.text.x = element_text(angle = 0, hjust = 0.5),
          legend.position = "bottom",
          panel.spacing.x = grid::unit(1.1, "lines"))
  if (show) display_plot(p, "fig3_weights_alpha05", width = 14.5, height = 8.0)
  invisible(p)
}

fig4 <- function(show = TRUE) {
  long <- to_long_three(ici_alpha05, "Criterion", c("Fuzzy_Lower", "Fuzzy_Upper", "Crisp"), c("ICI fuzzy lower", "ICI fuzzy upper", "ICI crisp"))
  long$Criterion <- factor(long$Criterion, levels = paste0("X", 1:6))

  p <- ggplot(long, aes(x = Criterion, y = Value, fill = Series)) +
    geom_col(position = position_dodge(width = 0.75), width = 0.65) +
    geom_text(aes(label = fmt3(Value)), position = position_dodge(width = 0.75), vjust = -0.45, size = VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0, 1.0), breaks = seq(0, 1.0, 0.1)) +
    labs(title = "Figure 4. Integrated Criteria Importance at α = 0.5", x = "Criterion", y = "ICI") +
    base_theme()
  if (show) display_plot(p, "fig4_ici_alpha05")
  invisible(p)
}

fig5 <- function(show = TRUE) {
  long <- to_long_three(entropy_alpha05, "Measure", c("Fuzzy_Lower", "Fuzzy_Upper", "Crisp"), c("Fuzzy lower", "Fuzzy upper", "Crisp"))
  long$Measure <- factor(long$Measure, levels = levels(entropy_alpha05$Measure))

  p <- ggplot(long, aes(x = Measure, y = Value, fill = Series)) +
    geom_col(position = position_dodge(width = 0.75), width = 0.65) +
    geom_text(aes(label = fmt3(Value)), position = position_dodge(width = 0.75), vjust = -0.4, size = VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0, 7.2), breaks = seq(0, 7, 1)) +
    labs(title = "Figure 5. Entropy structure at α = 0.5", x = "Measure", y = "Bits") +
    base_theme()
  if (show) display_plot(p, "fig5_entropy_alpha05")
  invisible(p)
}

fig6 <- function(show = TRUE) {
  long <- to_long_three(indices_alpha05, "Index", c("Fuzzy_Lower", "Fuzzy_Upper", "Crisp"), c("Fuzzy lower", "Fuzzy upper", "Crisp"))
  long$Index <- factor(long$Index, levels = levels(indices_alpha05$Index))

  p <- ggplot(long, aes(x = Index, y = Value, fill = Series)) +
    geom_col(position = position_dodge(width = 0.75), width = 0.65) +
    geom_text(aes(label = fmt3(Value)), position = position_dodge(width = 0.75), vjust = -0.45, size = VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0, 0.30), breaks = seq(0, 0.30, 0.05)) +
    labs(title = "Figure 6. Entropy-based diagnostic indices at α = 0.5", x = "Index", y = "Index value") +
    base_theme()
  if (show) display_plot(p, "fig6_indices_alpha05")
  invisible(p)
}

fig7 <- function(show = TRUE) {
  long <- alpha_long(alt_alpha, "Code")
  long$Code <- factor(long$Code, levels = paste0("Y", 1:13))

  p <- ggplot(long, aes(x = Code, y = Value, group = Alpha, colour = Alpha)) +
    geom_line(linewidth = 1.0) +
    geom_point(size = POINT_SIZE) +
    repel_value_labels(aes(label = fmt3(Value)), size = SMALL_VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0.045, 0.096), breaks = seq(0.045, 0.095, 0.005)) +
    labs(title = "Figure 7. Defuzzified alternative scores across α-cuts", x = "Alternative", y = "Crisp score") +
    base_theme()
  if (show) display_plot(p, "fig7_alternative_scores_across_alpha")
  invisible(p)
}

fig8 <- function(show = TRUE) {
  xint_long <- alpha_long(xint_alpha, "Criterion")
  xint_long$Criterion <- factor(xint_long$Criterion, levels = paste0("X", 1:6))
  ici_long <- alpha_long(ici_alpha, "Criterion")
  ici_long$Criterion <- factor(ici_long$Criterion, levels = paste0("X", 1:6))

  # Figure 8 contains very close curves. The labels are therefore placed in
  # ordered mini-stacks at each criterion, with connector lines to the actual
  # points. This makes the values readable even after insertion into Word.
  prepare_fig8_labels <- function(df, top_offset, step) {
    df$Xnum <- as.numeric(df$Criterion)
    df$Label <- fmt3(df$Value)
    df$LabelX <- NA_real_
    df$LabelY <- NA_real_
    alpha_offsets <- c("α=0" = -0.20, "α=0.5" = 0.00, "α=1" = 0.20)

    for (crit in levels(df$Criterion)) {
      idx <- which(df$Criterion == crit)
      sub <- df[idx, ]
      ord <- order(-sub$Value, as.character(sub$Alpha))
      idx_ord <- idx[ord]
      base <- max(df$Value[idx]) + top_offset
      df$LabelY[idx_ord] <- base - step * (seq_along(idx_ord) - 1)
      df$LabelX[idx_ord] <- df$Xnum[idx_ord] + alpha_offsets[as.character(df$Alpha[idx_ord])]
    }
    df
  }

  xint_plot <- prepare_fig8_labels(xint_long, top_offset = 0.026, step = 0.020)
  ici_plot  <- prepare_fig8_labels(ici_long,  top_offset = 0.085, step = 0.065)

  p1 <- ggplot(xint_plot, aes(x = Xnum, y = Value, group = Alpha, colour = Alpha)) +
    geom_line(linewidth = 1.0) +
    geom_point(size = POINT_SIZE) +
    geom_segment(aes(xend = LabelX, yend = LabelY),
                 linewidth = 0.22, alpha = 0.55, show.legend = FALSE) +
    geom_label(aes(x = LabelX, y = LabelY, label = Label, colour = Alpha),
               size = SMALL_VALUE_LABEL_SIZE, fill = "white", alpha = 0.94,
               label.size = 0.12, label.padding = grid::unit(0.08, "lines"),
               show.legend = FALSE) +
    scale_x_continuous(breaks = 1:6, labels = paste0("X", 1:6), limits = c(0.68, 6.32)) +
    scale_y_continuous(limits = c(0.055, 0.275), breaks = seq(0.08, 0.26, 0.04), expand = expansion(mult = c(0.02, 0.03))) +
    labs(title = "Integrated weights xINT", x = "Criterion", y = "Weight") +
    base_theme(base_size = PLOT_BASE_SIZE) +
    theme(legend.position = "bottom")

  p2 <- ggplot(ici_plot, aes(x = Xnum, y = Value, group = Alpha, colour = Alpha)) +
    geom_line(linewidth = 1.0) +
    geom_point(size = POINT_SIZE) +
    geom_segment(aes(xend = LabelX, yend = LabelY),
                 linewidth = 0.22, alpha = 0.55, show.legend = FALSE) +
    geom_label(aes(x = LabelX, y = LabelY, label = Label, colour = Alpha),
               size = SMALL_VALUE_LABEL_SIZE, fill = "white", alpha = 0.94,
               label.size = 0.12, label.padding = grid::unit(0.08, "lines"),
               show.legend = FALSE) +
    scale_x_continuous(breaks = 1:6, labels = paste0("X", 1:6), limits = c(0.68, 6.32)) +
    scale_y_continuous(limits = c(0.240, 0.960), breaks = seq(0.30, 0.90, 0.10), expand = expansion(mult = c(0.02, 0.03))) +
    labs(title = "Integrated Criteria Importance (ICI)", x = "Criterion", y = "ICI") +
    base_theme(base_size = PLOT_BASE_SIZE) +
    theme(legend.position = "bottom")

  grob <- gridExtra::arrangeGrob(
    p1, p2, ncol = 1,
    top = grid::textGrob("Figure 8. Evolution of xINT and ICI across α-cuts", gp = grid::gpar(fontface = "bold", fontsize = PLOT_BASE_SIZE + 4))
  )
  if (show) display_plot(grob, "fig8_xint_ici_across_alpha", width = 14.0, height = 10.5)
  invisible(grob)
}

fig9 <- function(show = TRUE) {
  long <- alpha_long(entropy_alpha, "Measure")
  long$Measure <- factor(long$Measure, levels = levels(entropy_alpha$Measure))

  p <- ggplot(long, aes(x = Measure, y = Value, fill = Alpha)) +
    geom_col(position = position_dodge(width = 0.75), width = 0.65) +
    geom_text(aes(label = fmt3(Value)), position = position_dodge(width = 0.75), vjust = -0.4, size = VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0, 7.2), breaks = seq(0, 7, 1)) +
    labs(title = "Figure 9. Sensitivity of entropy measures to α-cut level", x = "Measure", y = "Bits") +
    base_theme()
  if (show) display_plot(p, "fig9_entropy_sensitivity")
  invisible(p)
}

fig10 <- function(show = TRUE) {
  long <- alpha_long(indices_alpha, "Index")
  long$Index <- factor(long$Index, levels = levels(indices_alpha$Index))

  p <- ggplot(long, aes(x = Index, y = Value, fill = Alpha)) +
    geom_col(position = position_dodge(width = 0.75), width = 0.65) +
    geom_text(aes(label = fmt3(Value)), position = position_dodge(width = 0.75), vjust = -0.45, size = VALUE_LABEL_SIZE) +
    scale_y_continuous(limits = c(0, 0.23), breaks = seq(0, 0.22, 0.02)) +
    labs(title = "Figure 10. Sensitivity of diagnostic indices to α-cut level", x = "Index", y = "Index value") +
    base_theme()
  if (show) display_plot(p, "fig10_indices_sensitivity")
  invisible(p)
}

fig11 <- function(show = TRUE) {
  long <- rbind(
    data.frame(Code = comparison_lpi_fes$Code, Country = comparison_lpi_fes$Country, Method = "LPI composite", Rank = comparison_lpi_fes$LPI_rank, Status = comparison_lpi_fes$Status, stringsAsFactors = FALSE),
    data.frame(Code = comparison_lpi_fes$Code, Country = comparison_lpi_fes$Country, Method = "FES-MADM II @ α=0.5", Rank = comparison_lpi_fes$FES_rank, Status = comparison_lpi_fes$Status, stringsAsFactors = FALSE)
  )
  long$Method <- factor(long$Method, levels = c("LPI composite", "FES-MADM II @ α=0.5"))

  p <- ggplot(long, aes(x = Method, y = Rank, group = Code, colour = Status)) +
    geom_line(linewidth = 0.9, alpha = 0.9) +
    geom_point(size = POINT_SIZE) +
    ggrepel::geom_text_repel(data = subset(long, Method == "LPI composite"), aes(label = Code),
                           nudge_x = -0.10, direction = "y", hjust = 1, size = VALUE_LABEL_SIZE,
                           show.legend = FALSE, max.overlaps = Inf, seed = 42,
                           box.padding = 0.25, point.padding = 0.18, min.segment.length = 0) +
    ggrepel::geom_text_repel(data = subset(long, Method == "FES-MADM II @ α=0.5"), aes(label = Code),
                           nudge_x = 0.10, direction = "y", hjust = 0, size = VALUE_LABEL_SIZE,
                           show.legend = FALSE, max.overlaps = Inf, seed = 42,
                           box.padding = 0.25, point.padding = 0.18, min.segment.length = 0) +
    scale_y_reverse(breaks = 1:13, limits = c(13.5, 0.5)) +
    coord_cartesian(xlim = c(0.75, 2.25), clip = "off") +
    labs(title = "Figure 11. Comparative ranking: LPI composite vs FES-MADM II", x = NULL, y = "Rank (1 = best)") +
    base_theme() +
    theme(plot.margin = margin(12, 50, 12, 50))
  if (show) display_plot(p, "fig11_lpi_vs_fes_slopegraph", width = 9, height = 7)
  invisible(p)
}

fig12 <- function(show = TRUE) {
  p <- ggplot(comparison_lpi_fes, aes(x = LPI_norm, y = FES_norm, colour = Status)) +
    geom_abline(intercept = 0, slope = 1, linetype = "dashed", alpha = 0.6) +
    geom_point(size = VALUE_LABEL_SIZE) +
    ggrepel::geom_text_repel(aes(label = Code), size = VALUE_LABEL_SIZE, show.legend = FALSE,
                           max.overlaps = Inf, seed = 42, box.padding = 0.25,
                           point.padding = 0.18, min.segment.length = 0) +
    scale_x_continuous(limits = c(-5, 105), breaks = seq(0, 100, 20), labels = function(x) paste0(x, "%")) +
    scale_y_continuous(limits = c(-5, 105), breaks = seq(0, 100, 20), labels = function(x) paste0(x, "%")) +
    labs(
      title = "Figure 12. Relationship between LPI composite and FES-MADM II scores",
      x = "Normalized LPI composite score",
      y = "Normalized FES-MADM II score @ α = 0.5"
    ) +
    base_theme()
  if (show) display_plot(p, "fig12_lpi_fes_scatter", width = 8, height = 7)
  invisible(p)
}

fig13 <- function(show = TRUE) {
  # Concordance plot: each point compares the rank assigned by FES-MADM II
  # with the corresponding rank assigned by fuzzy TOPSIS. The dashed 45-degree
  # line denotes exact rank agreement. Both axes are reversed so that rank 1
  # (best) is placed at the upper-right corner, matching the interpretation
  # used in the manuscript text.
  plot_data <- benchmark_topsis
  plot_data$Code <- factor(plot_data$Code, levels = paste0("Y", 1:13))

  p <- ggplot(plot_data, aes(x = FES_rank, y = TOPSIS_rank)) +
    geom_abline(intercept = 0, slope = 1, linetype = "dashed", linewidth = 0.75, colour = "#2C7FB8") +
    geom_point(size = POINT_SIZE + 0.4, colour = "#2C7FB8") +
    ggrepel::geom_text_repel(
      aes(label = Code),
      size = VALUE_LABEL_SIZE + 0.2,
      colour = "black",
      seed = 42,
      max.overlaps = Inf,
      box.padding = 0.28,
      point.padding = 0.18,
      min.segment.length = 0,
      segment.alpha = 0.45,
      segment.size = 0.25,
      show.legend = FALSE
    ) +
    scale_x_reverse(breaks = 1:13, limits = c(13.5, 0.5)) +
    scale_y_reverse(breaks = 1:13, limits = c(13.5, 0.5)) +
    coord_fixed(ratio = 1) +
    labs(
      title = "Figure 13. Rank concordance: FES-MADM II vs fuzzy TOPSIS",
      subtitle = "Dashed line indicates exact rank agreement; Spearman ρ = 0.982 and Kendall τ = 0.934",
      x = "FES-MADM II rank (α = 0.5; 1 = best)",
      y = "Fuzzy TOPSIS rank (1 = best)"
    ) +
    base_theme(base_size = PLOT_BASE_SIZE) +
    theme(
      panel.border = element_rect(colour = "black", fill = NA, linewidth = 0.7),
      plot.margin = margin(12, 18, 12, 18)
    )
  if (show) display_plot(p, "fig13_fuzzy_topsis_rank_concordance", width = 8.5, height = 7.5)
  invisible(p)
}

# -----------------------------------------------------------------------------
# 6. Run all figures together in the RStudio Plots pane/history
# -----------------------------------------------------------------------------
plot_all_to_rstudio <- function() {
  # Store every figure in the global environment so each one can be reprinted
  # manually, e.g. print(FES_FIGURES$Figure_07), after resizing the RStudio plot pane.
  FES_FIGURES <<- list(
    Figure_02 = fig2(show = FALSE),
    Figure_03 = fig3(show = FALSE),
    Figure_04 = fig4(show = FALSE),
    Figure_05 = fig5(show = FALSE),
    Figure_06 = fig6(show = FALSE),
    Figure_07 = fig7(show = FALSE),
    Figure_08 = fig8(show = FALSE),
    Figure_09 = fig9(show = FALSE),
    Figure_10 = fig10(show = FALSE),
    Figure_11 = fig11(show = FALSE),
    Figure_12 = fig12(show = FALSE),
    Figure_13 = fig13(show = FALSE)
  )

  for (nm in names(FES_FIGURES)) {
    display_plot(FES_FIGURES[[nm]], figure_name = nm)
  }

  message("All figures (2-13) have been generated in the RStudio Plots pane/history.")
  message("They are also stored in the list object FES_FIGURES for manual reprinting.")
  invisible(FES_FIGURES)
}

# -----------------------------------------------------------------------------
# 7. Optional: save all figures as PNG files
# -----------------------------------------------------------------------------
save_all_figures <- function(output_dir = OUTPUT_DIR, dpi = EXPORT_DPI) {
  old_save <- SAVE_FIGURES
  old_pause <- PAUSE_BETWEEN_FIGURES
  old_device <- OPEN_NEW_DEVICE
  assign("SAVE_FIGURES", TRUE, envir = .GlobalEnv)
  assign("PAUSE_BETWEEN_FIGURES", FALSE, envir = .GlobalEnv)
  assign("OPEN_NEW_DEVICE", FALSE, envir = .GlobalEnv)
  assign("OUTPUT_DIR", output_dir, envir = .GlobalEnv)
  assign("EXPORT_DPI", dpi, envir = .GlobalEnv)

  on.exit({
    assign("SAVE_FIGURES", old_save, envir = .GlobalEnv)
    assign("PAUSE_BETWEEN_FIGURES", old_pause, envir = .GlobalEnv)
    assign("OPEN_NEW_DEVICE", old_device, envir = .GlobalEnv)
  }, add = TRUE)

  fig2(show = TRUE)
  fig3(show = TRUE)
  fig4(show = TRUE)
  fig5(show = TRUE)
  fig6(show = TRUE)
  fig7(show = TRUE)
  fig8(show = TRUE)
  fig9(show = TRUE)
  fig10(show = TRUE)
  fig11(show = TRUE)
  fig12(show = TRUE)
  fig13(show = TRUE)
  invisible(TRUE)
}

if (RUN_ALL_ON_SOURCE) {
  plot_all_to_rstudio()
}
