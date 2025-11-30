library(shiny)
library(shinythemes)
library(readxl)
library(writexl)
library(ggplot2)
library(dplyr)
library(DT)
library(gridExtra)
library(reshape2)

round3 <- function(x) round(x, 3)

clamp01 <- function(x) pmin(pmax(x, 0), 1)

log2safe <- function(x, eps = 1e-15) {
  ifelse(x > eps, log2(x), 0)
}

fixFuzzyPair <- function(L, U) {
  for (i in seq_along(L)) {
    if (L[i] > U[i]) {
      tmp <- L[i]
      L[i] <- U[i]
      U[i] <- tmp
    }
  }
  list(L = L, U = U)
}

measure_entropy_alt <- function(vec) {
  val <- 0
  for (a in vec) {
    if (a > 0) val <- val - a * log2safe(a)
  }
  val
}

measure_jointEntropy <- function(pXY) {
  sVal <- 0
  for (px in pXY) {
    if (px > 0) sVal <- sVal - px * log2safe(px)
  }
  sVal
}

measure_condEntropy_altGivenCrit <- function(pXY, xCrit, eps = 1e-15) {
  M <- nrow(pXY); N <- ncol(pXY)
  sumVal <- 0
  for (i in 1:M) {
    rowSum <- sum(pXY[i, ])
    if (rowSum > eps) {
      tmpH <- 0
      for (j in 1:N) {
        pYx <- pXY[i, j] / rowSum
        if (pYx > 0) tmpH <- tmpH - pYx * log2safe(pYx)
      }
      sumVal <- sumVal + xCrit[i] * tmpH
    }
  }
  sumVal
}

fesMadmFull <- function(alpha, DC, DD, WC, WD, CT, eps = 1e-15, shiftVal = 1) {
  if (nrow(DC) != nrow(DD)) stop("DC and DD must have same number of rows.")
  if (nrow(WC) != nrow(WD)) stop("WC and WD must have same number of rows.")
  if (nrow(DC) != nrow(WC) || nrow(DC) != nrow(CT)) {
    stop("DC, WC and CT must have same number of rows.")
  }
  
  M <- nrow(DC)
  N <- ncol(DC)
  
  perfLower <- DC - (1 - alpha) * DD
  perfUpper <- DC + alpha * DD
  
  normLower <- matrix(0, M, N)
  normUpper <- matrix(0, M, N)
  for (i in 1:M) {
    rowL <- perfLower[i, ]
    rowU <- perfUpper[i, ]
    ctype <- toupper(as.character(CT[i, 1]))
    
    if (ctype == "B") {
      theMax <- max(rowU)
      if (theMax <= 0) {
        shiftNeeded <- abs(theMax) + shiftVal
        rowL <- rowL + shiftNeeded
        rowU <- rowU + shiftNeeded
        theMax <- max(rowU)
      }
      theMax <- max(theMax, eps)
      normLower[i, ] <- rowL / theMax
      normUpper[i, ] <- rowU / theMax
      
    } else if (ctype == "C") {
      theMin <- min(rowL)
      if (theMin <= 0) {
        shiftNeeded <- abs(theMin) + shiftVal
        rowL <- rowL + shiftNeeded
        rowU <- rowU + shiftNeeded
        theMin <- min(rowL)
      }
      theMin <- max(theMin, eps)
      for (j in 1:N) {
        normLower[i, j] <- theMin / (rowU[j] + eps)
        normUpper[i, j] <- theMin / (rowL[j] + eps)
      }
      fixNorm <- fixFuzzyPair(normLower[i, ], normUpper[i, ])
      normLower[i, ] <- fixNorm$L
      normUpper[i, ] <- fixNorm$U
    } else {
      stop(paste("Invalid Criterion Type at row", i, "- must be 'B' or 'C'."))
    }
  }
  
  probLower <- matrix(0, M, N)
  probUpper <- matrix(0, M, N)
  for (i in 1:M) {
    sL <- sum(normLower[i, ]) + eps
    sU <- sum(normUpper[i, ]) + eps
    probLower[i, ] <- normLower[i, ] / sL
    probUpper[i, ] <- normUpper[i, ] / sU
  }
  
  wL <- WC - (1 - alpha) * WD
  wU <- WC + alpha * WD
  wL[wL < 0] <- 0
  wU[wU < 0] <- 0
  fixSBJ <- fixFuzzyPair(wL, wU)
  wL <- fixSBJ$L; wU <- fixSBJ$U
  
  hLower <- numeric(M)
  hUpper <- numeric(M)
  for (i in 1:M) {
    pL <- probLower[i, ]
    pU <- probUpper[i, ]
    hLower[i] <- measure_entropy_alt(pL) / log2(N)
    hUpper[i] <- measure_entropy_alt(pU) / log2(N)
  }
  hLower[hLower < 0] <- 0
  hUpper[hUpper < 0] <- 0
  fixh <- fixFuzzyPair(hLower, hUpper)
  hLower <- clamp01(fixh$L)
  hUpper <- clamp01(fixh$U)
  
  dLower <- 1 - hUpper
  dUpper <- 1 - hLower
  fixd <- fixFuzzyPair(dLower, dUpper)
  dLower <- clamp01(fixd$L)
  dUpper <- clamp01(fixd$U)
  
  sumDL <- sum(dLower) + eps
  sumDU <- sum(dUpper) + eps
  xObjL <- dLower / sumDL
  xObjU <- dUpper / sumDU
  fixObj <- fixFuzzyPair(xObjL, xObjU)
  xObjL <- clamp01(fixObj$L)
  xObjU <- clamp01(fixObj$U)
  
  denomL <- sum(wL * xObjL) + eps
  denomU <- sum(wU * xObjU) + eps
  xIntL <- (wL * xObjL) / denomL
  xIntU <- (wU * xObjU) / denomU
  fixInt <- fixFuzzyPair(xIntL, xIntU)
  xIntL <- clamp01(fixInt$L)
  xIntU <- clamp01(fixInt$U)
  
  altScoreLower_raw <- numeric(N)
  altScoreUpper_raw <- numeric(N)
  for (j in 1:N) {
    sumL <- 0; sumU <- 0
    for (i in 1:M) {
      sumL <- sumL + probLower[i, j] * xIntL[i]
      sumU <- sumU + probUpper[i, j] * xIntU[i]
    }
    altScoreLower_raw[j] <- sumL
    altScoreUpper_raw[j] <- sumU
  }
  altScoreLower <- pmin(altScoreLower_raw, altScoreUpper_raw)
  altScoreUpper <- pmax(altScoreLower_raw, altScoreUpper_raw)
  den_alt <- sum(altScoreUpper)
  if (den_alt <= 0) den_alt <- eps
  altScoreLower <- altScoreLower / den_alt
  altScoreUpper <- altScoreUpper / den_alt
  
  altMid <- (altScoreLower + altScoreUpper) / 2
  
  wDefSBJ <- (wL + wU) / 2
  
  xObjMid <- (xObjL + xObjU) / 2
  so <- sum(xObjMid); if (so <= 0) so <- eps
  xObjMid <- xObjMid / so
  
  xIntMid <- (xIntL + xIntU) / 2
  si <- sum(xIntMid); if (si <= 0) si <- eps
  xIntMid <- xIntMid / si
  
  SY_L_raw <- measure_entropy_alt(altScoreLower)
  SY_U_raw <- measure_entropy_alt(altScoreUpper)
  SY_L_raw <- max(SY_L_raw, 0)
  SY_U_raw <- max(SY_U_raw, 0)
  fixSY <- fixFuzzyPair(SY_L_raw, SY_U_raw)
  SY_L <- fixSY$L; SY_U <- fixSY$U
  SY_C <- (SY_L + SY_U) / 2
  
  SX_L_raw <- measure_entropy_alt(xIntL)
  SX_U_raw <- measure_entropy_alt(xIntU)
  SX_L_raw <- max(SX_L_raw, 0)
  SX_U_raw <- max(SX_U_raw, 0)
  fixSX <- fixFuzzyPair(SX_L_raw, SX_U_raw)
  SX_L <- fixSX$L; SX_U <- fixSX$U
  SX_C <- (SX_L + SX_U) / 2
  
  pXY_L <- matrix(0, M, N)
  for (i in 1:M) for (j in 1:N) pXY_L[i, j] <- xIntL[i] * probLower[i, j]
  SXY_L_raw <- measure_jointEntropy(as.vector(pXY_L))
  
  pXY_U <- matrix(0, M, N)
  for (i in 1:M) for (j in 1:N) pXY_U[i, j] <- xIntU[i] * probUpper[i, j]
  SXY_U_raw <- measure_jointEntropy(as.vector(pXY_U))
  
  SXY_L_raw <- max(SXY_L_raw, 0)
  SXY_U_raw <- max(SXY_U_raw, 0)
  fixSXY <- fixFuzzyPair(SXY_L_raw, SXY_U_raw)
  SXY_L <- fixSXY$L; SXY_U <- fixSXY$U
  SXY_C <- (SXY_L + SXY_U) / 2
  
  SYX_L_raw <- measure_condEntropy_altGivenCrit(probLower, xIntL)
  SYX_U_raw <- measure_condEntropy_altGivenCrit(probUpper, xIntU)
  SYX_L_raw <- max(SYX_L_raw, 0)
  SYX_U_raw <- max(SYX_U_raw, 0)
  fixSYX <- fixFuzzyPair(SYX_L_raw, SYX_U_raw)
  SYX_L <- fixSYX$L
  SYX_U <- fixSYX$U
  SYX_C <- (SYX_L + SYX_U) / 2
  
  IXY_L_raw <- SX_L + SY_L - SXY_L
  IXY_U_raw <- SX_U + SY_U - SXY_U
  IXY_L_raw <- max(IXY_L_raw, 0)
  IXY_U_raw <- max(IXY_U_raw, 0)
  fixI <- fixFuzzyPair(IXY_L_raw, IXY_U_raw)
  IXY_L <- fixI$L
  IXY_U <- fixI$U
  IXY_C <- (IXY_L + IXY_U) / 2
  
  SYX_mu_L <- numeric(M)
  SYX_mu_U <- numeric(M)
  for (i in 1:M) {
    rowL <- probLower[i, ]
    rowU <- probUpper[i, ]
    sL <- sum(rowL); sU <- sum(rowU)
    if (sL > eps) {
      pL <- rowL / sL
      SYX_mu_L[i] <- measure_entropy_alt(pL)
    } else {
      SYX_mu_L[i] <- 0
    }
    if (sU > eps) {
      pU <- rowU / sU
      SYX_mu_U[i] <- measure_entropy_alt(pU)
    } else {
      SYX_mu_U[i] <- 0
    }
  }
  fixSYXmu <- fixFuzzyPair(SYX_mu_L, SYX_mu_U)
  SYX_mu_L <- fixSYXmu$L
  SYX_mu_U <- fixSYXmu$U
  SYX_mu_C <- (SYX_mu_L + SYX_mu_U) / 2
  
  J_L_val <- clamp01(max(SY_L - SYX_U, 0))
  J_U_val <- clamp01(max(SY_U - SYX_L, 0))
  fixJ <- fixFuzzyPair(J_L_val, J_U_val)
  J_Xmu_Y_L <- rep(fixJ$L, M)
  J_Xmu_Y_U <- rep(fixJ$U, M)
  J_Xmu_Y_C <- rep((fixJ$L + fixJ$U) / 2, M)
  
  CES_L <- clamp01(mean(J_Xmu_Y_L))
  CES_U <- clamp01(mean(J_Xmu_Y_U))
  fixCES <- fixFuzzyPair(CES_L, CES_U)
  CES_L <- fixCES$L; CES_U <- fixCES$U
  CES_C <- (CES_L + CES_U) / 2
  
  NMI_L <- if (SY_L > 0) clamp01(IXY_L / SY_L) else 0
  NMI_U <- if (SY_U > 0) clamp01(IXY_U / SY_U) else 0
  fixNMI <- fixFuzzyPair(NMI_L, NMI_U)
  NMI_L <- fixNMI$L; NMI_U <- fixNMI$U
  NMI_C <- (NMI_L + NMI_U) / 2
  
  Nlog <- log2(N)
  ADI_L <- clamp01(1 - (SY_L / Nlog))
  ADI_U <- clamp01(1 - (SY_U / Nlog))
  fixADI <- fixFuzzyPair(ADI_L, ADI_U)
  ADI_L <- fixADI$L; ADI_U <- fixADI$U
  ADI_C <- (ADI_L + ADI_U) / 2
  
  CSF_L <- if (SY_L > 0) clamp01(1 - (SYX_L / SY_L)) else 0
  CSF_U <- if (SY_U > 0) clamp01(1 - (SYX_U / SY_U)) else 0
  fixCSF <- fixFuzzyPair(CSF_L, CSF_U)
  CSF_L <- fixCSF$L; CSF_U <- fixCSF$U
  CSF_C <- (CSF_L + CSF_U) / 2
  
  sumIndices_L <- sum(c(NMI_L, CES_L, CSF_L, ADI_L)) + eps
  p_j_L <- c(NMI_L, CES_L, CSF_L, ADI_L) / sumIndices_L
  
  sumIndices_U <- sum(c(NMI_U, CES_U, CSF_U, ADI_U)) + eps
  p_j_U <- c(NMI_U, CES_U, CSF_U, ADI_U) / sumIndices_U
  
  k <- 1 / log(4)
  E_j_L <- -k * p_j_U * log2safe(p_j_U)
  E_j_U <- -k * p_j_L * log2safe(p_j_L)
  E_j_L[!is.finite(E_j_L)] <- 0
  E_j_U[!is.finite(E_j_U)] <- 0
  
  d_j_L <- clamp01(1 - E_j_U)
  d_j_U <- clamp01(1 - E_j_L)
  
  sum_dj_L <- sum(d_j_L) + eps
  sum_dj_U <- sum(d_j_U) + eps
  w_j_L <- d_j_L / sum_dj_L
  w_j_U <- d_j_U / sum_dj_U
  
  NMGI_L_raw <- sum(w_j_L * c(NMI_L, CES_L, CSF_L, ADI_L))
  NMGI_U_raw <- sum(w_j_U * c(NMI_U, CES_U, CSF_U, ADI_U))
  NMGI_L_raw <- clamp01(NMGI_L_raw)
  NMGI_U_raw <- clamp01(NMGI_U_raw)
  fixNMGI <- fixFuzzyPair(NMGI_L_raw, NMGI_U_raw)
  NMGI_L <- fixNMGI$L
  NMGI_U <- fixNMGI$U
  NMGI_C <- (NMGI_L + NMGI_U) / 2
  
  ICI_L <- xIntL * SYX_mu_L
  ICI_U <- xIntU * SYX_mu_U
  fixICI <- fixFuzzyPair(ICI_L, ICI_U)
  ICI_L <- fixICI$L
  ICI_U <- fixICI$U
  ICI_Def <- (ICI_L + ICI_U) / 2
  
  list(
    M = M, N = N,
    altScoreLower = round3(altScoreLower),
    altScoreUpper = round3(altScoreUpper),
    altDef        = round3(altMid),
    wLower = round3(wL),
    wUpper = round3(wU),
    wDefSBJ = round3(wDefSBJ),
    xObjLower = round3(xObjL),
    xObjUpper = round3(xObjU),
    xObjDef   = round3(xObjMid),
    xIntLower = round3(xIntL),
    xIntUpper = round3(xIntU),
    xIntDef   = round3(xIntMid),
    hLower = round3(hLower),
    hUpper = round3(hUpper),
    dLower = round3(dLower),
    dUpper = round3(dUpper),
    SXY_L = round3(SXY_L), SXY_U = round3(SXY_U), SXY_C = round3(SXY_C),
    SX_L  = round3(SX_L),  SX_U  = round3(SX_U),  SX_C  = round3(SX_C),
    SY_L  = round3(SY_L),  SY_U  = round3(SY_U),  SY_C  = round3(SY_C),
    IXY_L = round3(IXY_L), IXY_U = round3(IXY_U), IXY_C = round3(IXY_C),
    SYX_L = round3(SYX_L), SYX_U = round3(SYX_U), SYX_C = round3(SYX_C),
    J_Xmu_Y_L = round3(J_Xmu_Y_L),
    J_Xmu_Y_U = round3(J_Xmu_Y_U),
    J_Xmu_Y_C = round3(J_Xmu_Y_C),
    CES_L = round3(CES_L), CES_U = round3(CES_U), CES_C = round3(CES_C),
    CSF_L = round3(CSF_L), CSF_U = round3(CSF_U), CSF_C = round3(CSF_C),
    ADI_L = round3(ADI_L), ADI_U = round3(ADI_U), ADI_C = round3(ADI_C),
    NMI_L = round3(NMI_L), NMI_U = round3(NMI_U), NMI_C = round3(NMI_C),
    NMGI_L = round3(NMGI_L), NMGI_U = round3(NMGI_U), NMGI_C = round3(NMGI_C),
    ICI_L   = round3(ICI_L),
    ICI_U   = round3(ICI_U),
    ICI_Def = round3(ICI_Def)
  )
}

ui <- fluidPage(
  theme = shinytheme("slate"),
  
  tags$head(
    tags$style(HTML("
      table.dataTable tbody td {
        color: #FFFFFF !important;
      }
      table.dataTable thead th {
        color: #FFFF00 !important;
      }
      .dataTables_wrapper .dataTables_length label,
      .dataTables_wrapper .dataTables_filter label,
      .dataTables_wrapper .dataTables_info {
        color: #FFFF00 !important;
      }
      .dataTables_wrapper .dataTables_paginate .paginate_button {
        color: #FFFFFF !important;
        background-color: #222222 !important;
      }
      .dataTables_wrapper .dataTables_length select,
      .dataTables_wrapper .dataTables_filter input {
        background-color: #FFFFFF !important;
        color: #000000 !important;
      }
      .shiny-text-output, .shiny-html-output,
      h4, label, .control-label {
        color: #FFFF00 !important;
      }
      .btn {
        color: #FFFFFF !important;
      }
    "))
  ),
  
  titlePanel("FES-MADM II: Fuzzy Entropy-based Multi-Attribute Decision Making"),
  
  navbarPage(
    title = "FES-MADM II", id = "tabs",
    
    tabPanel("1. Instructions",
             fluidRow(
               column(12,
                      h3("How to Use"),
                      tags$ul(
                        tags$li("Step 1: Import data and verify all sheets."),
                        tags$li("Step 2: Choose an α-cut and run the main computation."),
                        tags$li("Step 3: Inspect fuzzy & crisp scores for alternatives and criteria."),
                        tags$li("Step 4: Examine entropy measures and indices."),
                        tags$li("Step 5: Use sensitivity analysis (α, Δμν, Δxμ^(SBJ), B/C) if needed."),
                        tags$li("Step 6: Export all results to Excel.")
                      ),
                      hr(),
                      h4("Notation Table (FES-MADM II)"),
                      DTOutput("tableNotation")
               )
             )
    ),
    
    tabPanel("2. Data Import",
             sidebarLayout(
               sidebarPanel(
                 fileInput("fileExcel", "Upload Excel:", accept = c(".xls", ".xlsx")),
                 numericInput("sheetCenter", "Sheet # Data (Center ξμν):", 1, min = 1),
                 numericInput("sheetDelta",  "Sheet # Data (Δμν):",         2, min = 1),
                 numericInput("sheetWCenter","Sheet # SBJ Weights (Center xμ^SBJ):", 3, min = 1),
                 numericInput("sheetWDelta", "Sheet # SBJ Weights (Δxμ^SBJ):",       4, min = 1),
                 numericInput("sheetType",   "Sheet # Crit.Type (Cost/Benefit):",    5, min = 1),
                 numericInput("sheetAlpha",  "Sheet # α-cuts (optional):",          6, min = 1),
                 actionButton("loadData", "Load Data", class = "btn-primary")
               ),
               mainPanel(
                 h4("Preview: Data (Central ξμν)"),        DTOutput("tableCenter"),
                 h4("Preview: Data (Δμν)"),               DTOutput("tableDelta"),
                 h4("Preview: SBJ Weights (Center xμ^SBJ)"),DTOutput("tableWCenter"),
                 h4("Preview: SBJ Weights (Δxμ^SBJ)"),    DTOutput("tableWDelta"),
                 h4("Preview: Criteria Type"),            DTOutput("tableType"),
                 h4("Preview: α-cuts (if provided)"),     DTOutput("tableAlpha")
               )
             )
    ),
    
    tabPanel("3. Alternatives & Criteria Results",
             sidebarLayout(
               sidebarPanel(
                 sliderInput("alphaSliderMain", "Select α-cut (main run):",
                             min = 0, max = 1, value = 0.5, step = 0.1),
                 actionButton("computeFESMADM", "Compute FES-MADM II", class = "btn-success")
               ),
               mainPanel(
                 tabsetPanel(
                   tabPanel("Alternatives Results", DTOutput("tableAltResults")),
                   tabPanel("Criteria Weights Results",
                            h4("Subjective Weights x̃μ^SBJ,a (Lower / Upper / Crisp)"),
                            DTOutput("tableSBJ"),
                            hr(),
                            h4("Objective Weights x̃μ^OBJ,a (Lower / Upper / Crisp)"),
                            DTOutput("tableOBJ"),
                            hr(),
                            h4("Integrated Weights x̃μ^INT,a (Lower / Upper / Crisp)"),
                            DTOutput("tableINT")
                   ),
                   tabPanel("Integrated Criteria Importance (ICI)", DTOutput("tableICI"))
                 )
               )
             )
    ),
    
    tabPanel("4. Entropy Measures & Indices",
             fluidRow(
               column(6, h4("Entropy Measures (Lower / Upper / Crisp)"), DTOutput("tableEntropy")),
               column(6, h4("Entropy-based Indices (Lower / Upper / Crisp)"),  DTOutput("tableIndices"))
             )
    ),
    
    tabPanel("5. Plots",
             sidebarLayout(
               sidebarPanel(
                 helpText("Crisp plots for the main α-cut (as used in the last computation)."),
                 hr(),
                 h4("Compare SBJ, OBJ, INT Weights"),
                 checkboxInput("showSBJ", "Show Subjective (SBJ)", value = TRUE),
                 checkboxInput("showOBJ", "Show Objective (OBJ)", value = TRUE),
                 checkboxInput("showINT", "Show Integrated (INT)", value = TRUE)
               ),
               mainPanel(
                 tabsetPanel(
                   tabPanel("Alternative Scores", plotOutput("plotAltScores")),
                   tabPanel("Criteria Weights",
                            h4("a) Crisp xμ^SBJ"),  plotOutput("plotWeightsSBJ"),
                            hr(),
                            h4("b) Crisp xμ^OBJ"),  plotOutput("plotWeightsOBJ"),
                            hr(),
                            h4("c) Crisp xμ^INT"),  plotOutput("plotWeightsINT"),
                            hr(),
                            h4("d) SBJ vs OBJ vs INT"), plotOutput("plotWeightsCompare")
                   ),
                   tabPanel("Integrated Criteria Importance (ICI)", plotOutput("plotICIbar")),
                   tabPanel("Entropy Measures",                      plotOutput("plotEntropyMeasures")),
                   tabPanel("Entropy Indices",                       plotOutput("plotEntropyIndices"))
                 )
               )
             )
    ),
    
    tabPanel("6. Sensitivity Analysis",
             sidebarLayout(
               sidebarPanel(
                 sliderInput("alphaSliderSens", "Select α for Sensitivity:",
                             min = 0, max = 1, value = 0.5, step = 0.1),
                 numericInput("rowDelta", "Row # for Δμν:", 1, min = 1),
                 numericInput("colDelta", "Col # for Δμν:", 1, min = 1),
                 numericInput("valDelta", "New Δμν:", 0, step = 0.1),
                 actionButton("applyDelta", "Apply Δμν"),
                 hr(),
                 numericInput("rowWDelta", "Criterion # for Δxμ^SBJ:", 1, min = 1),
                 numericInput("valWDelta", "New Δxμ^SBJ:", 0, step = 0.1),
                 actionButton("applyWDelta", "Apply Δxμ^SBJ"),
                 hr(),
                 numericInput("critTypeIndex", "Criterion # toggle B/C:", 1, min = 1),
                 actionButton("toggleBC", "Toggle B/C"),
                 hr(),
                 actionButton("runSensitivity", "Re-run with Changes", class = "btn-warning")
               ),
               mainPanel(
                 h4("Sensitivity Analysis Results (α as selected above)"),
                 DTOutput("tableSensitivityAlt"),
                 plotOutput("plotSensitivityAll")
               )
             )
    ),
    
    tabPanel("7. Analytical Computations",
             fluidRow(
               column(12,
                      h4("Interval-based Entropy & Weights (main α-cut)"),
                      DTOutput("tableAnalysisFull")
               )
             )
    ),
    
    tabPanel("8. Download Results",
             fluidRow(
               column(3,
                      tags$div(
                        style = "text-align:center;",
                        tags$img(
                          src = "https://cdn.thecollector.com/wp-content/uploads/2024/07/thinker-auguste-rodin-what-so-special.jpg?width=1400&quality=70",
                          width = "160px", height = "160px",
                          style = "border-radius:50%; border:2px solid black;",
                          title = "The Thinker, Auguste Rodin (1902)"
                        ),
                        tags$p(style = "font-style:italic; margin-top:10px; font-size:14px;",
                               "Decisions shape the future; clarity shapes decisions."
                        ),
                        tags$p(style = "margin-top:5px; font-size:12px; text-align:justify;",
                               "The Thinker, created by Auguste Rodin in 1902, symbolises the reflective, entropic reasoning at the heart of FES-MADM II."
                        ),
                        downloadButton("downloadAll", "Download FESMADM2_Results.xlsx",
                                       class = "btn-primary", style = "margin-top:15px;")
                      )
               ),
               column(9,
                      h3("Summary of Results (main α-cut)"),
                      uiOutput("summaryResults")
               )
             )
    )
  )
)

server <- function(input, output, session) {
  
  dataCenter <- reactiveVal(NULL)
  dataDelta  <- reactiveVal(NULL)
  wCenter    <- reactiveVal(NULL)
  wDelta     <- reactiveVal(NULL)
  critType   <- reactiveVal(NULL)
  alphaCuts  <- reactiveVal(NULL)
  
  alpha_main_used <- reactiveVal(0.5)
  alpha_sens_used <- reactiveVal(0.5)
  
  output$tableNotation <- renderDT({
    df <- data.frame(
      Symbol = c("ξμν","Δμν","xμ^SBJ","Δxμ^SBJ","xμ^OBJ","xμ^INT",
                 "S(X,Y)","S(X)","S(Y)","I(X;Y)","S(Y|X)",
                 "NMI","ADI","CES","CSF","NMGI","ICI"),
      Meaning = c(
        "Central performance of criterion μ on alternative ν",
        "Fuzzy deviation (uncertainty) of that performance",
        "Subjective weight (central value)",
        "Fuzzy deviation of the subjective weight",
        "Objective weight from fuzzy diversification degree",
        "Integrated weight combining subjective & objective views",
        "Joint entropy of criteria and alternatives (bits)",
        "Entropy of the criteria distribution (bits)",
        "Entropy of the alternatives distribution (bits)",
        "Mutual information between criteria and alternatives (bits)",
        "Conditional entropy of alternatives given criteria (bits)",
        "Normalized Mutual Information",
        "Alternatives Distinction Index",
        "Criteria Effectiveness Score",
        "Conditional Stability Factor",
        "Net Mutual Growth Index",
        "Integrated Criteria Importance"
      )
    )
    datatable(df, options = list(pageLength = 20), rownames = FALSE)
  })
  
  observeEvent(input$loadData, {
    req(input$fileExcel)
    
    fixNum <- function(df) {
      mat <- apply(df, 2, function(x) as.numeric(as.character(x)))
      mat[is.na(mat)] <- 0
      as.data.frame(mat)
    }
    
    dc <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetCenter, col_names = FALSE)),
      error = function(e) { showNotification("Error reading Data (Center ξμν).", type="error"); NULL }
    )
    dd <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetDelta,  col_names = FALSE)),
      error = function(e) { showNotification("Error reading Data (Δμν).", type="error"); NULL }
    )
    wc <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetWCenter, col_names = FALSE)),
      error = function(e) { showNotification("Error reading SBJ Weights (Center).", type="error"); NULL }
    )
    wd <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetWDelta,  col_names = FALSE)),
      error = function(e) { showNotification("Error reading SBJ Weights (Δ).", type="error"); NULL }
    )
    ct <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetType,   col_names = FALSE)),
      error = function(e) { showNotification("Error reading Crit.Type sheet.", type="error"); NULL }
    )
    ac <- tryCatch(
      as.data.frame(read_excel(input$fileExcel$datapath,
                               sheet = input$sheetAlpha,  col_names = FALSE)),
      error = function(e) NULL
    )
    
    if (is.null(dc) || is.null(dd) || is.null(wc) || is.null(wd) || is.null(ct)) return()
    
    dataCenter(fixNum(dc))
    dataDelta(fixNum(dd))
    wCenter(fixNum(wc))
    wDelta(fixNum(wd))
    critType(as.data.frame(lapply(ct, function(x) toupper(as.character(x)))))
    if (!is.null(ac)) alphaCuts(fixNum(ac))
    
    showNotification("Data loaded successfully!", type = "message")
  })
  
  output$tableCenter  <- renderDT({ req(dataCenter()); datatable(dataCenter(), options=list(pageLength=5)) })
  output$tableDelta   <- renderDT({ req(dataDelta());  datatable(dataDelta(),  options=list(pageLength=5)) })
  output$tableWCenter <- renderDT({ req(wCenter());    datatable(wCenter(),   options=list(pageLength=5)) })
  output$tableWDelta  <- renderDT({ req(wDelta());     datatable(wDelta(),    options=list(pageLength=5)) })
  output$tableType    <- renderDT({ req(critType());   datatable(critType(),  options=list(pageLength=5)) })
  output$tableAlpha   <- renderDT({ req(alphaCuts());  datatable(alphaCuts(), options=list(pageLength=5)) })
  
  fesResMain <- eventReactive(input$computeFESMADM, {
    req(dataCenter(), dataDelta(), wCenter(), wDelta(), critType())
    DC <- as.matrix(dataCenter())
    DD <- as.matrix(dataDelta())
    WC <- as.matrix(wCenter())
    WD <- as.matrix(wDelta())
    CT <- as.matrix(critType())
    alpha_main_used(input$alphaSliderMain)
    fesMadmFull(alpha_main_used(), DC, DD, WC, WD, CT)
  })
  
  output$tableAltResults <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Alternative = paste0("Y", seq_len(r$N)),
      Lower = r$altScoreLower,
      Upper = r$altScoreUpper,
      Crisp = r$altDef,
      check.names = FALSE
    ) %>% arrange(desc(Crisp))
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableSBJ <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion   = paste0("X", seq_len(r$M)),
      Lower = r$wLower,
      Upper = r$wUpper,
      Crisp = r$wDefSBJ,
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableOBJ <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion   = paste0("X", seq_len(r$M)),
      Lower = r$xObjLower,
      Upper = r$xObjUpper,
      Crisp = r$xObjDef,
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableINT <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion   = paste0("X", seq_len(r$M)),
      Lower = r$xIntLower,
      Upper = r$xIntUpper,
      Crisp = r$xIntDef,
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableICI <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion   = paste0("X", seq_len(r$M)),
      Lower = r$ICI_L,
      Upper = r$ICI_U,
      Crisp = r$ICI_Def,
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableEntropy <- renderDT({
    r <- fesResMain(); req(r)
    infoProp_L <- ifelse(r$SY_L > 0, clamp01(1 - r$SYX_L / r$SY_L), NA)
    infoProp_U <- ifelse(r$SY_U > 0, clamp01(1 - r$SYX_U / r$SY_U), NA)
    infoProp_C <- ifelse(!is.na(infoProp_L) & !is.na(infoProp_U),
                         (infoProp_L + infoProp_U)/2, NA)
    
    df <- data.frame(
      Measure     = c("S(X,Y)", "S(X)", "S(Y)", "I(X;Y)", "S(Y|X)", "I(Y|X)"),
      Lower = c(r$SXY_L, r$SX_L, r$SY_L, r$IXY_L, r$SYX_L, infoProp_L),
      Upper = c(r$SXY_U, r$SX_U, r$SY_U, r$IXY_U, r$SYX_U, infoProp_U),
      Crisp = c(r$SXY_C, r$SX_C, r$SY_C, r$IXY_C, r$SYX_C, infoProp_C),
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$tableIndices <- renderDT({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Index       = c("NMI", "ADI", "CES", "CSF", "NMGI"),
      Lower = c(r$NMI_L, r$ADI_L, r$CES_L, r$CSF_L, r$NMGI_L),
      Upper = c(r$NMI_U, r$ADI_U, r$CES_U, r$CSF_U, r$NMGI_U),
      Crisp = c(r$NMI_C, r$ADI_C, r$CES_C, r$CSF_C, r$NMGI_C),
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$plotAltScores <- renderPlot({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Alternative = paste0("Y", 1:r$N),
      Score = as.numeric(r$altDef)
    ) %>% arrange(desc(Score))
    
    ggplot(df, aes(x = reorder(Alternative, -Score), y = Score)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Score)), vjust = -0.5, size = 3) +
      labs(title = sprintf("Alternative Scores p*ν (Crisp) @ α = %.3f", alpha_main_used()),
           x = "Alternative", y = "Score") +
      theme_minimal()
  })
  
  output$plotWeightsSBJ <- renderPlot({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion = paste0("X", 1:r$M),
      Weight = as.numeric(r$wDefSBJ)
    ) %>% arrange(desc(Weight))
    
    ggplot(df, aes(x = reorder(Criterion, -Weight), y = Weight)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3) +
      labs(title = "Subjective Weights xμ^SBJ (Crisp)",
           x = "Criterion", y = "Weight") +
      theme_minimal()
  })
  
  output$plotWeightsOBJ <- renderPlot({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion = paste0("X", 1:r$M),
      Weight = as.numeric(r$xObjDef)
    ) %>% arrange(desc(Weight))
    
    ggplot(df, aes(x = reorder(Criterion, -Weight), y = Weight)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3) +
      labs(title = "Objective Weights xμ^OBJ (Crisp)",
           x = "Criterion", y = "Weight") +
      theme_minimal()
  })
  
  output$plotWeightsINT <- renderPlot({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion = paste0("X", 1:r$M),
      Weight = as.numeric(r$xIntDef)
    ) %>% arrange(desc(Weight))
    
    ggplot(df, aes(x = reorder(Criterion, -Weight), y = Weight)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3) +
      labs(title = "Integrated Weights xμ^INT (Crisp)",
           x = "Criterion", y = "Weight") +
      theme_minimal()
  })
  
  output$plotWeightsCompare <- renderPlot({
    r <- fesResMain(); req(r)
    SBJ <- as.numeric(r$wDefSBJ); SBJ[is.na(SBJ)] <- 0
    OBJ <- as.numeric(r$xObjDef); OBJ[is.na(OBJ)] <- 0
    INT <- as.numeric(r$xIntDef); INT[is.na(INT)] <- 0
    
    df <- data.frame(
      Criterion = paste0("X", 1:r$M),
      SBJ = SBJ, OBJ = OBJ, INT = INT
    )
    df_melt <- melt(df, id.vars = "Criterion",
                    variable.name = "Type", value.name = "Weight")
    
    df_melt_filtered <- df_melt %>%
      filter((Type == "SBJ" & input$showSBJ) |
               (Type == "OBJ" & input$showOBJ) |
               (Type == "INT" & input$showINT))
    
    if (nrow(df_melt_filtered) == 0) {
      ggplot() + annotate("text", x = 0.5, y = 0.5,
                          label = "No Weights Selected", size = 6) +
        theme_void()
    } else {
      ggplot(df_melt_filtered,
             aes(x = Criterion, y = Weight, colour = Type, group = Type)) +
        geom_line(size = 1) +
        geom_point(size = 3) +
        geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3, colour = "black") +
        labs(title = sprintf("xμ^SBJ, xμ^OBJ, xμ^INT (Crisp) @ α = %.3f",
                             alpha_main_used()),
             x = "Criterion", y = "Weight", colour = "Type") +
        theme_minimal()
    }
  })
  
  output$plotICIbar <- renderPlot({
    r <- fesResMain(); req(r)
    df <- data.frame(
      Criterion = paste0("X", 1:r$M),
      Weight = as.numeric(r$ICI_Def)
    ) %>% arrange(desc(Weight))
    
    ggplot(df, aes(x = reorder(Criterion, -Weight), y = Weight)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3) +
      labs(title = sprintf("Integrated Criteria Importance Iμ^a (Crisp) @ α = %.3f",
                           alpha_main_used()),
           x = "Criterion", y = "ICI") +
      theme_minimal()
  })
  
  output$plotEntropyMeasures <- renderPlot({
    r <- fesResMain(); req(r)
    infoProp_C <- ifelse(r$SY_C > 0, clamp01(1 - r$SYX_C / r$SY_C), NA)
    CrispVec <- c(r$SXY_C, r$SX_C, r$SY_C, r$IXY_C, r$SYX_C, infoProp_C)
    
    df <- data.frame(
      Measure = c("S(X,Y)", "S(X)", "S(Y)", "I(X;Y)", "S(Y|X)", "I(Y|X)"),
      Value   = round3(CrispVec)
    )
    
    ggplot(df, aes(x = Measure, y = Value)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = Value), vjust = -0.5, size = 3) +
      labs(title = sprintf("Entropy Measures (Crisp) @ α = %.3f", alpha_main_used()),
           x = "Measure", y = "Bits") +
      theme_minimal()
  })
  
  output$plotEntropyIndices <- renderPlot({
    r <- fesResMain(); req(r)
    CrispIdx <- c(r$NMI_C, r$ADI_C, r$CES_C, r$CSF_C, r$NMGI_C)
    df <- data.frame(
      Index = c("NMI", "ADI", "CES", "CSF", "NMGI"),
      Value = round3(CrispIdx)
    ) %>% arrange(desc(Value))
    
    ggplot(df, aes(x = reorder(Index, -Value), y = Value)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = Value), vjust = -0.5, size = 3) +
      labs(title = sprintf("Entropy Indices (Crisp) @ α = %.3f", alpha_main_used()),
           x = "Index", y = "[0,1]") +
      theme_minimal()
  })
  
  observeEvent(input$applyDelta, {
    dd <- dataDelta(); req(dd)
    i <- input$rowDelta; j <- input$colDelta
    if (i <= nrow(dd) && j <= ncol(dd)) {
      dd[i, j] <- as.numeric(input$valDelta)
      dataDelta(dd)
      showNotification(paste("Updated Δ[", i, ",", j, "] =", round3(dd[i, j])), type = "message")
    } else {
      showNotification("Invalid row/column for Δμν!", type = "error")
    }
  })
  
  observeEvent(input$applyWDelta, {
    wd <- wDelta(); req(wd)
    i <- input$rowWDelta
    if (i <= nrow(wd)) {
      wd[i, 1] <- as.numeric(input$valWDelta)
      wDelta(wd)
      showNotification(paste("Updated Δxμ^SBJ for criterion", i, "=", round3(wd[i, 1])),
                       type = "message")
    } else {
      showNotification("Invalid row for Δxμ^SBJ!", type = "error")
    }
  })
  
  observeEvent(input$toggleBC, {
    ct <- critType(); req(ct)
    i <- input$critTypeIndex
    if (i <= nrow(ct)) {
      oldVal <- toupper(as.character(ct[i, 1]))
      newVal <- ifelse(oldVal == "B", "C", "B")
      ct[i, 1] <- newVal
      critType(ct)
      showNotification(paste("Toggled criterion", i, "from", oldVal, "to", newVal),
                       type = "message")
    } else {
      showNotification("Invalid row for toggling B/C!", type = "error")
    }
  })
  
  fesResSens <- eventReactive(input$runSensitivity, {
    req(dataCenter(), dataDelta(), wCenter(), wDelta(), critType())
    DC <- as.matrix(dataCenter())
    DD <- as.matrix(dataDelta())
    WC <- as.matrix(wCenter())
    WD <- as.matrix(wDelta())
    CT <- as.matrix(critType())
    alpha_sens_used(input$alphaSliderSens)
    fesMadmFull(alpha_sens_used(), DC, DD, WC, WD, CT)
  })
  
  observeEvent(input$runSensitivity, {
    if (!is.null(fesResSens())) {
      showNotification("Sensitivity re-run completed.", type = "message")
    } else {
      showNotification("Sensitivity re-run failed.", type = "error")
    }
  })
  
  output$tableSensitivityAlt <- renderDT({
    r <- fesResSens(); req(r)
    df <- data.frame(
      Alternative = paste0("Y", 1:r$N),
      Lower = r$altScoreLower,
      Upper = r$altScoreUpper,
      Crisp = r$altDef,
      check.names = FALSE
    ) %>% arrange(desc(Crisp))
    
    datatable(df, options = list(pageLength = 10), rownames = FALSE) |>
      formatRound(columns = 2:4, digits = 3)
  })
  
  output$plotSensitivityAll <- renderPlot({
    r <- fesResSens(); req(r)
    
    dfW <- data.frame(
      Criterion = paste0("X", 1:r$M),
      Weight = as.numeric(r$xIntDef)
    ) %>% arrange(desc(Weight))
    p1 <- ggplot(dfW, aes(x = reorder(Criterion, -Weight), y = Weight)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Weight)), vjust = -0.5, size = 3) +
      labs(title = sprintf("Integrated Weights xμ^INT (Crisp) @ α = %.3f",
                           alpha_sens_used()),
           x = "Criterion", y = "Weight") +
      theme_minimal()
    
    dfA <- data.frame(
      Alternative = paste0("Y", 1:r$N),
      Score = as.numeric(r$altDef)
    ) %>% arrange(desc(Score))
    p2 <- ggplot(dfA, aes(x = reorder(Alternative, -Score), y = Score)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = round3(Score)), vjust = -0.5, size = 3) +
      labs(title = sprintf("Alternative Scores p*ν (Crisp) @ α = %.3f",
                           alpha_sens_used()),
           x = "Alternative", y = "Score") +
      theme_minimal()
    
    CrispIdx <- c(r$NMI_C, r$ADI_C, r$CES_C, r$CSF_C, r$NMGI_C)
    dfI <- data.frame(
      Index = c("NMI", "ADI", "CES", "CSF", "NMGI"),
      Value = round3(CrispIdx)
    ) %>% arrange(desc(Value))
    p3 <- ggplot(dfI, aes(x = reorder(Index, -Value), y = Value)) +
      geom_bar(stat = "identity") +
      geom_text(aes(label = Value), vjust = -0.5, size = 3) +
      labs(title = sprintf("Entropy Indices (Crisp) @ α = %.3f",
                           alpha_sens_used()),
           x = "Index", y = "[0,1]") +
      theme_minimal()
    
    grid.arrange(p1, p2, p3, ncol = 3)
  })
  
  output$tableAnalysisFull <- renderDT({
    r <- fesResMain(); req(r)
    M <- r$M
    df <- data.frame(
      Criterion  = paste0("X", seq_len(M)),
      h_Lower    = r$hLower,
      h_Upper    = r$hUpper,
      d_Lower    = r$dLower,
      d_Upper    = r$dUpper,
      SBJ_Lower  = r$wLower,
      SBJ_Upper  = r$wUpper,
      OBJ_Lower  = r$xObjLower,
      OBJ_Upper  = r$xObjUpper,
      INT_Lower  = r$xIntLower,
      INT_Upper  = r$xIntUpper,
      check.names = FALSE
    )
    datatable(df, options = list(pageLength = 20), rownames = FALSE) |>
      formatRound(columns = 2:11, digits = 3)
  })
  
  output$downloadAll <- downloadHandler(
    filename = function() "FESMADM2_Results.xlsx",
    content = function(file) {
      r <- fesResMain(); req(r)
      M <- r$M; N <- r$N
      
      infoProp_L <- ifelse(r$SY_L > 0, clamp01(1 - r$SYX_L / r$SY_L), NA)
      infoProp_U <- ifelse(r$SY_U > 0, clamp01(1 - r$SYX_U / r$SY_U), NA)
      infoProp_C <- ifelse(!is.na(infoProp_L) & !is.na(infoProp_U),
                           (infoProp_L + infoProp_U)/2, NA)
      
      df_alts <- data.frame(
        Alternative = paste0("Y", 1:N),
        Lower = r$altScoreLower,
        Upper = r$altScoreUpper,
        Crisp = r$altDef,
        check.names = FALSE
      )
      df_sbj <- data.frame(
        Criterion   = paste0("X", 1:M),
        Lower = r$wLower,
        Upper = r$wUpper,
        Crisp = r$wDefSBJ,
        check.names = FALSE
      )
      df_obj <- data.frame(
        Criterion   = paste0("X", 1:M),
        Lower = r$xObjLower,
        Upper = r$xObjUpper,
        Crisp = r$xObjDef,
        check.names = FALSE
      )
      df_int <- data.frame(
        Criterion   = paste0("X", 1:M),
        Lower = r$xIntLower,
        Upper = r$xIntUpper,
        Crisp = r$xIntDef,
        check.names = FALSE
      )
      df_ici <- data.frame(
        Criterion   = paste0("X", 1:M),
        Lower = r$ICI_L,
        Upper = r$ICI_U,
        Crisp = r$ICI_Def,
        check.names = FALSE
      )
      df_entropy <- data.frame(
        Measure     = c("S(X,Y)", "S(X)", "S(Y)", "I(X;Y)", "S(Y|X)", "I(Y|X)"),
        Lower = c(r$SXY_L, r$SX_L, r$SY_L, r$IXY_L, r$SYX_L, infoProp_L),
        Upper = c(r$SXY_U, r$SX_U, r$SY_U, r$IXY_U, r$SYX_U, infoProp_U),
        Crisp       = c(r$SXY_C, r$SX_C, r$SY_C, r$IXY_C, r$SYX_C, infoProp_C),
        check.names = FALSE
      )
      df_indices <- data.frame(
        Index       = c("NMI", "ADI", "CES", "CSF", "NMGI"),
        Lower = c(r$NMI_L, r$ADI_L, r$CES_L, r$CSF_L, r$NMGI_L),
        Upper = c(r$NMI_U, r$ADI_U, r$CES_U, r$CSF_U, r$NMGI_U),
        Crisp = c(r$NMI_C, r$ADI_C, r$CES_C, r$CSF_C, r$NMGI_C),
        check.names = FALSE
      )
      
      write_xlsx(list(
        Alternatives      = df_alts,
        SubjectiveWeights = df_sbj,
        ObjectiveWeights  = df_obj,
        IntegratedWeights = df_int,
        ICI               = df_ici,
        Entropy           = df_entropy,
        Indices           = df_indices
      ), path = file)
    }
  )
  
  output$summaryResults <- renderUI({
    r <- fesResMain(); req(r)
    
    alpha_val <- alpha_main_used()
    
    altIndices <- which(r$altDef == max(r$altDef))
    altStr  <- paste0("Y", altIndices, collapse = ", ")
    critInd <- which(r$ICI_Def == max(r$ICI_Def))
    critStr <- paste0("X", critInd,  collapse = ", ")
    
    infoProp <- ifelse(r$SY_C > 0, clamp01(1 - (r$SYX_C / r$SY_C)), NA)
    
    generateDetailedEntropyInsights <- function(SXY, SX, SY, IXY, SYX,
                                                NMI, ADI, CES, CSF, NMGI) {
      insights <- c()
      
      if (SXY > 1.5) {
        insights <- c(insights,
                      "<li>High joint entropy S(X,Y) indicates rich informational diversity across criteria and alternatives.</li>")
      } else {
        insights <- c(insights,
                      "<li>Relatively low S(X,Y) suggests a more concentrated information structure, with fewer dominant patterns.</li>")
      }
      
      if (SX > 1.0) {
        insights <- c(insights,
                      "<li>The criteria entropy S(X) points to a balanced distribution of importance across criteria, supporting robustness.</li>")
      } else {
        insights <- c(insights,
                      "<li>Lower S(X) reveals that a small subset of criteria dominates the weighting structure.</li>")
      }
      
      if (SY > 1.0) {
        insights <- c(insights,
                      "<li>The alternatives entropy S(Y) confirms meaningful differentiation among options, enabling clear ranking.</li>")
      } else {
        insights <- c(insights,
                      "<li>Limited S(Y) indicates weak discrimination among alternatives, making the decision more ambiguous.</li>")
      }
      
      if (IXY > 0.5) {
        insights <- c(insights,
                      "<li>Mutual information I(X;Y) is high, i.e. criteria jointly explain a substantial portion of the variability in alternative scores.</li>")
      } else {
        insights <- c(insights,
                      "<li>I(X;Y) remains modest, implying that part of the variability in alternatives is not captured by the selected criteria.</li>")
      }
      
      if (SYX < 0.5) {
        insights <- c(insights,
                      "<li>Conditional entropy S(Y|X) is low, so residual uncertainty about alternatives after conditioning on criteria is limited.</li>")
      } else {
        insights <- c(insights,
                      "<li>Higher S(Y|X) means that even after incorporating the criteria, considerable uncertainty in alternative ranking persists.</li>")
      }
      
      if (NMI > 0.7) {
        insights <- c(insights,
                      "<li>Normalized Mutual Information (NMI) close to one reflects a very strong mapping from criteria space to alternative ranking.</li>")
      } else {
        insights <- c(insights,
                      "<li>Moderate NMI values indicate that explanatory power is spread and some criteria–alternative relations remain weak.</li>")
      }
      
      if (ADI > 0.8) {
        insights <- c(insights,
                      "<li>A high Alternatives Distinction Index (ADI) confirms that the model clearly separates alternatives.</li>")
      } else {
        insights <- c(insights,
                      "<li>Lower ADI values signal that alternative profiles are partially overlapping, which may require additional criteria or refined data.</li>")
      }
      
      if (CES > 0.7) {
        insights <- c(insights,
                      "<li>Criteria Effectiveness Score (CES) highlights that the criteria jointly reduce uncertainty in a highly efficient manner.</li>")
      } else {
        insights <- c(insights,
                      "<li>CES suggests that some criteria contribute marginally and could be candidates for re-specification or exclusion.</li>")
      }
      
      if (CSF > 0.75) {
        insights <- c(insights,
                      "<li>The Conditional Stability Factor (CSF) signifies a stable decision configuration, robust to local perturbations.</li>")
      } else {
        insights <- c(insights,
                      "<li>A lower CSF points to a more fragile configuration in which small changes in inputs may alter the ranking.</li>")
      }
      
      if (NMGI > 0.8) {
        insights <- c(insights,
                      "<li>Net Mutual Growth Index (NMGI) close to one indicates a highly coherent and information-efficient decision system.</li>")
      } else {
        insights <- c(insights,
                      "<li>NMGI shows that, although the system is functional, there is still room for improving criteria selection or data quality.</li>")
      }
      
      paste("<ul>", paste(insights, collapse = ""), "</ul>")
    }
    
    tags$table(
      style = "width:100%; border-collapse:collapse; border: 1px solid black;",
      tags$tr(
        tags$th(colspan = 2,
                style = "text-align:left; padding:8px; border:1px solid black;
                         background-color:orange; color:#000; font-weight:bold; font-size:18px;",
                "Metric")
      ),
      tags$tr(
        tags$td(style="padding:8px; border:1px solid black;", strong("Selected α-cut")),
        tags$td(style="padding:8px; border:1px solid black;", sprintf("%.3f", alpha_val))
      ),
      tags$tr(
        tags$td(style="padding:8px; border:1px solid black;", strong("Optimal Alternative")),
        tags$td(style="padding:8px; border:1px solid black;",
                paste0(altStr, " (Crisp score p*ν: ", sprintf("%.3f", max(r$altDef)), ")"))
      ),
      tags$tr(
        tags$td(style="padding:8px; border:1px solid black;", strong("Most Significant Criterion (ICI)")),
        tags$td(style="padding:8px; border:1px solid black;",
                paste0(critStr, " (ICI: ", sprintf("%.3f", max(r$ICI_Def)), ")"))
      ),
      tags$tr(
        tags$th(colspan = 2,
                style = "text-align:left; padding:8px; border:1px solid black;
                         background-color:orange; color:#000; font-weight:bold; font-size:18px;",
                "Key Entropic Indices (Crisp)")
      ),
      tags$tr(tags$td("S(X,Y)"), tags$td(sprintf("%.3f", r$SXY_C))),
      tags$tr(tags$td("S(X)"),   tags$td(sprintf("%.3f", r$SX_C))),
      tags$tr(tags$td("S(Y)"),   tags$td(sprintf("%.3f", r$SY_C))),
      tags$tr(tags$td("I(X;Y)"), tags$td(sprintf("%.3f", r$IXY_C))),
      tags$tr(tags$td("S(Y|X)"), tags$td(sprintf("%.3f", r$SYX_C))),
      tags$tr(tags$td("I(Y|X)"),
              tags$td(ifelse(is.na(infoProp), "NA", sprintf("%.3f", infoProp)))),
      tags$tr(tags$td("NMI"),   tags$td(sprintf("%.3f", r$NMI_C))),
      tags$tr(tags$td("ADI"),   tags$td(sprintf("%.3f", r$ADI_C))),
      tags$tr(tags$td("CES"),   tags$td(sprintf("%.3f", r$CES_C))),
      tags$tr(tags$td("CSF"),   tags$td(sprintf("%.3f", r$CSF_C))),
      tags$tr(tags$td("NMGI"),  tags$td(sprintf("%.3f", r$NMGI_C))),
      tags$tr(
        tags$th(colspan = 2,
                style = "text-align:left; padding:8px; border:1px solid black;
                         background-color:orange; color:#000; font-weight:bold; font-size:18px;",
                "Detailed Insights")
      ),
      tags$tr(
        tags$td(colspan = 2,
                style = "padding:8px; border:1px solid black; text-align:justify;",
                HTML(generateDetailedEntropyInsights(
                  SXY = r$SXY_C,
                  SX  = r$SX_C,
                  SY  = r$SY_C,
                  IXY = r$IXY_C,
                  SYX = r$SYX_C,
                  NMI = r$NMI_C,
                  ADI = r$ADI_C,
                  CES = r$CES_C,
                  CSF = r$CSF_C,
                  NMGI = r$NMGI_C
                )))
      )
    )
  })
}

shinyApp(ui = ui, server = server)
