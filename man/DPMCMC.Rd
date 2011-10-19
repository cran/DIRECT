\name{DPMCMC}
\alias{DPMCMC}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Dirichlet Process-Based Markov Chain Monte Carlo (MCMC) Sampler for Mixture Model-Based Clustering
}
\description{
The MCMC sampler for \code{\link{DIRECT}}.  In each MCMC iteration, the function updates cluster memberships for all items, allowing for changes in the number of clusters (mixture components).  This update implements a Metropolis-Hastings (MH) sampler developed in Fu, Russell, Bray and Tavare, and an MH sampler developed in Neal (2000).  It also updates parameters specific to each mixture components via MH sampling.  Parameters of interest include the mean vector and standard deviations of the three types of variability.  Additionally, it updates \eqn{\alpha}, the concentration parameter in the Dirichlet-process prior, allowing for Gibbs (Escobar and West, 1995) and MH sampling.  
}
\usage{
DPMCMC(file.mcmc.cs, file.mcmc.pars, file.mcmc.probs, file.size, 
       data, SKIP, nTime, times, c.curr, par.prior, 
       PAR.INIT = FALSE, 
       sdWICluster.curr = 0.5, sdTSampling.curr = 0.5, 
       sdResidual.curr = 0.5, alpha.curr, 
       alpha.prior.shape, alpha.prior.rate, sd.prop, 
       nIter, burn.in, step.size, nRepeat = 1, nResample, seed.value, 
       RNORM.METHOD = c("chol", "eigen", "svd"), 
       SAMPLE.C = c("FRBT", "Neal"), 
       PRIOR.MODEL = c("none", "OU", "BM", "BMdrift"), 
       ALPHA.METHOD = c("Gibbs", "MH"), 
       OUTPUT.CLUST.SIZE = FALSE, PRINT = FALSE)
}
\arguments{
  \item{file.mcmc.cs}{
A character string in quotation marks indicating the output filename for cluster memberships and \eqn{\alpha}.
}
  \item{file.mcmc.pars}{
A character string in quotation marks indicating the output filename for MCMC samples of parameters specific to mixture components.
}
  \item{file.mcmc.probs}{
A character string in quotation marks indicating the output filename for posterior allocation probability matrices from the resampling step.
}
  \item{file.size}{
A character string in quotation marks indicating the output filename for cluster sizes.
}
  \item{data}{
An \eqn{N \times JR} matrix of continuous values, or a data frame containing such a matrix.  \eqn{N} is the number if items, \eqn{J} the number of time points (or experimental conditions) and \eqn{R} the number of replicates.  Each row contains values for Replicates 1 through \eqn{R} under Condition 1, values for Replicates 1 through \eqn{R} under Condition 2, and so on.
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
  \item{par.prior}{
A list that contains parameters of the prior distributions.  It has the following format: \code{par.prior = list (uWICluster=???, uTSampling=???, uResidual=???, mean=???, meanMT1=???, sdMT1=???, meanMTProc=???, sdMTProc=???, uSDT1=???, uSDProc=???, shapeBetaProc=???, rateBetaProc=???)}.  See \code{\link{DIRECT}} for possible values of the list components.
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
  \item{sd.prop}{
A list that contains standard deviations in the proposal distributions for some key parameters.  It has the following format: \code{sd.prop=list (WICluster=???, TSampling=???, Residual=???, alpha=???)}.  ??? needs to be filled in with positive values.  See \code{\link{DIRECT}}.
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
  \item{OUTPUT.CLUST.SIZE}{
If TRUE, output cluster sizes in MCMC iterations into an external file *_mcmc_size.out.
}
  \item{PRINT}{
If TRUE, print intermediate values during an MCMC run onto the screen.  Used for debugging for small data sets.  
}
}
\details{
The MCMC sampling step in \code{\link{DIRECT}} is accomplished with \code{DPMCMC}.  \code{DPMCMC} generates MCMC samples of assignments to mixture components (number of components implicitly generated; written into external file *_mcmc_cs.out) and component-specific parameters (written into external file *_mcmc_pars.out), which include mean vectors and standard deviations of three types of variability.  
}
\value{
At least two files are generated by \code{DPMCMC} and placed under the current working directory:
\enumerate{
  \item *_mcmc_cs.out: Generated from MCMC sampling.  Each row contains an MCMC sample of assignments of items to mixture components, or cluster memberships if a component is defined as a cluster, as well as \eqn{\alpha}, the concentration parameter in the Dirichlet-process prior.
  \item *_mcmc_pars.out: Generated from MCMC sampling.  Each row contains an MCMC sample of parameters specific to a mixture component.  Multiple rows may come from the same MCMC iteration.
}

If argument \code{OUTPUT.CLUST.SIZE=TRUE}, an additional file *_mcmc_size.out is also generated, which contains the cluster sizes of each recorded MCMC sample.
}
\references{
Escobar, M. D. and West, M. (1995) Bayesian density estimation and inference using mixtures. Journal of the American Statistical Association, 90: 577-588. 

Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. Bayesian clustering with the Dirichlet-process prior.  

Neal, R. M. (2000) Markov chain sampling methods for Dirichlet process mixture models. Journal of Computational and Graphical Statistics, 9: 249-265. 
}
\author{
Audrey Q. Fu
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
\code{\link{DIRECT}}, which calls \code{DPMCMC}.
}
\examples{
## See example in DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
