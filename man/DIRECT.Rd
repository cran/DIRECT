\name{DIRECT}
\alias{DIRECT}
\alias{direct}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Bayesian Clustering with the Dirichlet-Process Prior
}
\description{
A Bayesian clustering method for multivariate data, e.g., replicated time-course microarray gene expression data.  This method uses a mixture random-effects model that decomposes the total variability in the data into within-cluster variability, variability across experimental conditions (e.g., time points), and variability in replicates (i.e., residual variability).  It also uses a Dirichlet-process prior to induce a distribution on the number of clusters as well as clustering.  Metropolis-Hastings Markov chain Monte Carlo procedures are used for parameter estimation.
}
\usage{
DIRECT (data, data.name = "Output", 
        SKIP = 0, nTime, times = 1:nTime, 
        c.curr, 
        uWICluster = 1, uTSampling = 1, uResidual = 1, 
        meanVec = rep(0, nTime), meanMT1 = 0, sdMT1 = 0.2, 
        meanMTProc = 0, sdMTProc = 0.5, uSDT1 = 0.2, uSDProc = 1, 
        shapeBetaProc = 0.5, rateBetaProc = 0.5, 
        PAR.INIT = TRUE, 
        sdWICluster.curr = 0.5, sdTSampling.curr = 0.5, 
        sdResidual.curr = 0.5, alpha.curr = 0.01, 
        alpha.prior.shape = 0.01, alpha.prior.rate = 1, 
        WICluster.prop.sd = 0.2, TSampling.prop.sd = 0.2, 
        Residual.prop.sd = 0.2, alpha.prop.sd = 0.2, 
        nIter, burn.in, step.size, nRepeat = 1, nResample, 
        seed.value, 
        RNORM.METHOD = c("chol", "eigen", "svd"), 
        SAMPLE.C = c("FRBT", "Neal"), 
        PRIOR.MODEL = c("none", "OU", "BM", "BMdrift"), 
        ALPHA.METHOD = c("Gibbs", "MH"), 
        RELABEL.THRESHOLD = 0.01, 
        OUTPUT.CLUST.SIZE = FALSE, PRINT = FALSE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{data}{
An \eqn{N \times JR} matrix of continuous values, or a data frame containing such a matrix.  \eqn{N} is the number if items, \eqn{J} the number of time points (or experimental conditions) and \eqn{R} the number of replicates.  Each row contains values for Replicates 1 through \eqn{R} under Condition 1, values for Replicates 1 through \eqn{R} under Condition 2, and so on.
}
  \item{data.name}{
A character string used as the prefix of output files.  
}
  \item{SKIP}{
Number of columns in \code{data} to be skipped when processing the data.
}
  \item{nTime}{
Number of time points (or experimental conditions).
}
  \item{times}{
An integer vector of length \code{nTime}, indicating times (or experimental conditions).
}
  \item{c.curr}{
An integer vector of length \eqn{N}, indicating initial cluster assignments for items 1 through \eqn{N}.  
}
  \item{uWICluster}{
Upper bound of the uniform prior assigned to the standard deviation of within-cluster variability.  The lower bound of the uniform prior is 0.
}
  \item{uTSampling}{
Upper bound of the uniform prior assigned to the standard deviation of variability due to sampling across time points (or experimental conditions).  The lower bound of the uniform prior is 0.
}
  \item{uResidual}{
Upper bound of the uniform prior assigned to the standard deviation of residual variability (i.e., variability across replicates).  The lower bound of the uniform prior is 0.
}
  \item{meanVec}{
Prior mean vector of length \code{nTime}.  Required if \code{PRIOR.MODEL="none"}.
}
  \item{meanMT1}{
Prior mean (scalar) of the mean at the first time point.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").
}
  \item{sdMT1}{
A positive scalar.  Prior standard deviation (scalar) of the mean at the first time point.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").
}
  \item{meanMTProc}{
Prior mean (scalar) of the mean across time points.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").  Set to 0 if \code{PRIOR.MODEL="BM"}.
}
  \item{sdMTProc}{
A positive scalar.  Prior standard deviation (scalar) of the mean across time points.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").
}
  \item{uSDT1}{
The upper bound of the uniform prior assigned to the standard deviation at the first time point.  The lower bound of the uniform prior is 0.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").  
}
  \item{uSDProc}{
The upper bound of the uniform prior assigned to the standard deviation across time points.  The lower bound of the uniform prior is 0.  Required if \code{PRIOR.MODEL} is one of the stochastic processes ("OU", "BM" and "BMdrift").  
}
  \item{shapeBetaProc}{
A positive scalar.  The shape parameter in the beta prior for the mean-reverting rate in an Ornstein-Uhlenbeck process.  Required if \code{PRIOR.MODEL="OU"}.
}
  \item{rateBetaProc}{
A positive scalar.  The rate parameter in the beta prior for the mean-reverting rate in an Ornstein-Uhlenbeck process.  Required if \code{PRIOR.MODEL="OU"}.
}
  \item{PAR.INIT}{
Logical value.  Generate initial values for the standard deviations of the three types of variability if TRUE.  Use the input values otherwise.
}
  \item{sdWICluster.curr}{
A positive scalar.  Initial value of the standard deviation of the within-cluster variability.  Ignored if \code{PAR.INIT=TRUE}.
}
  \item{sdTSampling.curr}{
A positive scalar.  Initial value of the standard deviation of the variability across time points.  Ignored if \code{PAR.INIT=TRUE}.
}
  \item{sdResidual.curr}{
A positive scalar.  Initial value of the standard deviation of the residual variability (i.e., variability across replicates).  Ignored if \code{PAR.INIT=TRUE}.
}
  \item{alpha.curr}{
A positive scalar.  Initial value of \eqn{\alpha}, the concentration parameter of the Dirichlet-process prior.
}
  \item{alpha.prior.shape}{
A positive scalar.  The shape parameter in the beta prior for \eqn{\alpha}, the concentration parameter of the Dirichlet-process prior.
}
  \item{alpha.prior.rate}{
A positive scalar.  The rate parameter in the beta prior for \eqn{\alpha}, the concentration parameter of the Dirichlet-process prior.
}
  \item{WICluster.prop.sd}{
A positive scalar.  The standard deviation in the proposal distribution (normal) for the standard deviation of the within-cluster variability.
}
  \item{TSampling.prop.sd}{
A positive scalar.  The standard deviation in the proposal distribution (normal) for the standard deviation of the variability across time points.
}
  \item{Residual.prop.sd}{
A positive scalar.  The standard deviation in the proposal distribution (normal) for the standard deviation of the residual variability (i.e., variability across replicates).
}
  \item{alpha.prop.sd}{
A positive scalar.  The standard deviation in the proposal distribution (normal) for \eqn{\alpha}, the concentration parameter of the Dirichlet-process prior.  Ignored if \code{ALPHA.METHOD="Gibbs"}.
}
  \item{nIter}{
The number of MCMC iterations.
}
  \item{burn.in}{
A value in (0,1) indicating the percentage of the MCMC iterations to be used as burn-in and be discarded in posterior inference.
}
  \item{step.size}{
An integer indicating the number of MCMC iterations to be skipped between two recorded MCMC samples.
}
  \item{nRepeat}{
An integer \eqn{\geq 1} indicating the number of times to update the cluster memberships for all items.  Useful only when \code{SAMPLE.C="Neal"}.
}
  \item{nResample}{
An integer \eqn{\geq 1} indicating the number of resamples to draw to estimate the posterior mixing proportions.  
}
  \item{seed.value}{
A positive value used in random number generation.
}
  \item{RNORM.METHOD}{
Method to compute the determinant of the covariance matrix in the calculation of the multivariate normal density.  Required.  Method choices are: "chol" for Choleski decomposition, "eigen" for eigenvalue decomposition, and "svd" for singular value decomposition.
}
  \item{SAMPLE.C}{
Method to update cluster memberships.  Required.  Method choices are: "FRBT" for the Metropolis-Hastings sampler based on a discrete uniform proposal distribution developed in Fu, Russell, Bray and Tavare, and "Neal" for the Metropolis-Hastings sampler developed in Neal (2000).
}
  \item{PRIOR.MODEL}{
Model to generate realizations of the mean vector of a mixture component.  Required.  Choices are: "none" for not assuming a stochastic process and using a zero vector, "OU" for an Ornstein-Uhlenbeck process (a.k.a. the mean-reverting process), "BM" for a Brown motion (without drift), and "BMdrift" for a Brownian motion with drift.
}
  \item{ALPHA.METHOD}{
Method to update \eqn{\alpha}, the concentration parameter of the Dirichlet-process prior.  Required.  Choices are: "Gibbs" for a Gibbs sampler developed in Escobar and West (1995), and "MH" for a Metropolis-Hastings sampler.
}
  \item{RELABEL.THRESHOLD}{
A positive scalar.  Used to determine whether the optimization in the relabeling algorithm has converged.  
}
  \item{OUTPUT.CLUST.SIZE}{
If TRUE, output cluster sizes in MCMC iterations into an external file *_mcmc_size.out.
}
  \item{PRINT}{
If TRUE, print intermediate values during an MCMC run onto the screen.  Used for debugging with small data sets.  
}
}
\details{
DIRECT is a mixture model-based clustering method.  It consists of two major steps: 
\enumerate{
  \item MCMC sampling.  DIRECT generates MCMC samples of assignments to mixture components (number of components implicitly generated; written into external file *_mcmc_cs.out) and component-specific parameters (written into external file *_mcmc_pars.out), which include mean vectors and standard deviations of three types of variability.  
  \item Posterior inference, which further consists of two steps: 
  \enumerate{
    \item Resampling: DIRECT estimates posterior allocation probability matrix (written into external file *_mcmc_probs.out).
    \item Relabeling: DIRECT deals with label-switching by estimating optimal labels of mixture components (written into external file *_mcmc_perms.out), implementing 
Algorithm 2 in Stephens (2000).
  }
}

The arguments required to set up a DIRECT run can be divided into five categories: 
\enumerate{
  \item Data-related, such as \code{data}, \code{times} and so on.
  \item Initial values of parameters, including \code{c.curr}, \code{sdWICluster.curr}, \code{sdTSampling.curr}, \code{sdResidual.curr} and \code{alpha.curr}.
  \item Values used to specify prior distributions, such as \code{uWICluster}, \code{meanMT1}, \code{rateBetaProc}, \code{alpha.prior.shape} and so on.
  \item Standard deviation used in the proposal distributions for parameters of interest.  A normal distribution whose mean is the current value and whose standard deviation is user-specified is used as the proposal.  Reflection is used if the proposal is outside the range (e.g., (0,1)) for the parameter.
  \item Miscellaneous arguments for MCMC configuration, for model choices and for output choices.
}

The user may set up multiple runs with different initial values or values in the prior distributions, and compare the clustering results to check whether the MCMC run has mixed well and whether the inference is sensitive to initial values or priors.  If the data are informative enough, initial values and priors should lead to consistent clustering results.
}
\value{
At least four files are generated during a DIRECT run and placed under the current working directory:
\enumerate{
  \item *_mcmc_cs.out: Generated from MCMC sampling.  Each row contains an MCMC sample of assignments of items to mixture components, or cluster memberships if a component is defined as a cluster, as well as \eqn{\alpha}, the concentration parameter in the Dirichlet-process prior.
  \item *_mcmc_pars.out: Generated from MCMC sampling.  Each row contains an MCMC sample of parameters specific to a mixture component.  Multiple rows may come from the same MCMC iteration.
  \item *_mcmc_probs.out: Generated from resampling in posterior inference.  File contains a matrix of \eqn{HN \times K}, which is \eqn{H} posterior allocation probability matrices stacked up, each matrix of \eqn{N \times K}, where \eqn{H} is the number of recorded MCMC samples, \eqn{N} the number of items and \eqn{K} the inferred number of mixture components.
  \item *_mcmc_perms.out: Generated from relabeling in posterior inference.  Each row contains an inferred permutation (relabel) of labels of mixture components.
}

If argument \code{OUTPUT.CLUST.SIZE=TRUE}, the fifth file *_mcmc_size.out is also generated, which contains the cluster sizes of each recorded MCMC sample.
}
\references{
Escobar, M. D. and West, M. (1995) Bayesian density estimation and inference using mixtures. Journal of the American Statistical Association, 90: 577-588. 

Fu, A. Q., Russell, S., Bray, S. and Tavare, S. (2013) Bayesian clustering of replicated time-course gene expression data with weak signals. The Annals of Applied Statistics. 7(3) 1334-1361.

Stephens, M. (2000) Dealing with label switching in mixture models. Journal of the Royal Statistical Society, Series B, 62: 795-809.

Neal, R. M. (2000) Markov chain sampling methods for Dirichlet process mixture models. Journal of Computational and Graphical Statistics, 9: 249-265. 
}
\author{
Audrey Q. Fu
}
\note{
\code{DIRECT} calls the following functions adapted or directly taken from other R packages: \code{\link{dMVNorm}}, \code{\link{rMVNorm}} and \code{\link{rDirichlet}}.  See documentation of each function for more information.
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
\code{\link{DPMCMC}} for the MCMC sampler under the Dirichlet-process prior.

\code{\link{resampleClusterProb}} for resampling of posterior allocation probability matrix in posterior inference.

\code{\link{relabel}} for relabeling in posterior inference.

\code{\link{summaryDIRECT}} for processing MCMC estimates for clustering.

\code{\link{simuDataREM}} for simulating data under the mixture random-effects model.
}
\examples{
\dontrun{
# Load replicated time-course gene expression data
# Use only first 50 genes for test run
data (tc.data)
data = tc.data[1:50,]
times = c(0,5,10,15,20,25,30,35,40,50,60,70,80,90,100,110,120,150)
nGene = nrow (data)
nTime=length (times)
SKIP = 2

# Initial values and MCMC specs
c.curr = rep (1, nGene)    # start with a single cluster
alpha.curr = 0.01

alpha.prior.shape = 1/nGene
alpha.prior.rate = 1

SAMPLE.C.METHOD="FRBT"    # method for sampling cluster memberships
PRIOR.MODEL = "OU"       # prior model for generating mean vector
ALPHA.METHOD = "MH"      # method for sampling concentration parameter
RELABEL.THRESHOLD=0.01   # stopping criterion used in relabeling algorithm

nIter=10
burn.in=0
step.size=1
nResample=2
seed.value = 12

data.name="tmp"          # prefix of output files

# Run DIRECT
# This is a short run that takes less than a minute
# All output files will be under current working directory
DIRECT (data=data, data.name=data.name, SKIP=SKIP, nTime=nTime, times=times, 
    c.curr=c.curr, PAR.INIT=TRUE, alpha.curr=alpha.curr, 
    alpha.prior.shape=alpha.prior.shape, 
    alpha.prior.rate=alpha.prior.rate, 
    nIter=nIter, burn.in=burn.in, step.size=step.size, 
    nResample=nResample, seed.value=seed.value, 
    RNORM.METHOD="svd", SAMPLE.C=SAMPLE.C.METHOD, 
    PRIOR.MODEL=PRIOR.MODEL, ALPHA.METHOD=ALPHA.METHOD, 
    RELABEL.THRESHOLD=RELABEL.THRESHOLD)

# Process MCMC samples from DIRECT
data.name="tmp"          # prefix of output files
tmp.summary = summaryDIRECT (data.name)

# Plot clustering results
# Clustered mean profiles
plotClustersMean (data, tmp.summary, SKIP=2, times=times)
par (mfrow=c(1,1))
# Posterior estimates of standard deviations 
# of three types of variability in each cluster
plotClustersSD (tmp.summary, nTime=18)
# PCA plot of the posterior allocation probability matrix
plotClustersPCA (data$GeneName, tmp.summary)
}
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{cluster}
\keyword{models}
\keyword{multivariate}
\keyword{ts}
