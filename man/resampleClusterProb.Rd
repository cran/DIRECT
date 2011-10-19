\name{resampleClusterProb}
\alias{resampleClusterProb}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Resampling to Estimate Posterior Allocation Probability Matrix 
}
\description{
The resampling method as part of the posterior inference under \code{\link{DIRECT}}.  It uses stored MCMC samples to generate realizations of the allocation probability matrix, and writes the realizations to a user-specified external file.
}
\usage{
resampleClusterProb(file.out, ts, nitem, ntime, nrep, 
    pars.mcmc, cs.mcmc, alpha.mcmc, nstart, nres)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{file.out}{
Name of file containing samples of posterior allocation probability matrix.
}
  \item{ts}{
A \code{nitem}-by-\code{ntime}-by-\code{nrep} array of data.
}
  \item{nitem}{
Number of items.
}
  \item{ntime}{
Number of time points.
}
  \item{nrep}{
Number of replicates.
}
  \item{pars.mcmc}{
A matrix or data frame of MCMC samples of mean vectors and random effects stored in file *_mcmc_pars.out, one of the output files from \code{\link{DPMCMC}}.
}
  \item{cs.mcmc}{
A matrix or data frame of MCMC samples of assignments of mixture components stored in file *_mcmc_cs.out, one of the output files from \code{\link{DPMCMC}}.
}
  \item{alpha.mcmc}{
A vector of MCMC samples of \eqn{\alpha}, the concentration parameter in the Dirichlet-process prior, stored in the last column of file *_mcmc_cs.out, one of the output files from \code{\link{DPMCMC}}.
}
  \item{nstart}{
Starting from which recorded MCMC sample.
}
  \item{nres}{
How many times to draw resamples?  Multiple samples are averaged.
}
}
\value{
Samples of the allocation probability matrix are written to file *_mcmc_probs.out.  This file contains a large matrix of \eqn{HN \times K}, which is \eqn{H} posterior allocation probability matrices stacked up, each individual matrix of \eqn{N \times K}, where \eqn{H} is the number of recorded MCMC samples, \eqn{N} the number of items and \eqn{K} the inferred number of mixture components.}
\references{
Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. Bayesian clustering with the Dirichlet-process prior.  
}
\author{
Audrey Q. Fu
}
\note{
\code{resampleClusterProb} calls the following functions adapted or directly taken from existing R functions:
\itemize{
  \item \code{dMVNorm} is adapted from \code{dmvnorm} by Friedrich Leisch and Fabian Scheipl in package \code{mvtnorm}.
  \item \code{rMVNorm} is adapted from \code{rmvnorm} by Friedrich Leisch and Fabian Scheipl in package \code{mvtnorm}.
  \item \code{rDirichlet} is taken from \code{rdirichlet} by Gregory R. Warnes, Ben Bolker and Ian Wilson in package \code{gregmisc}.
  \item \code{dDirichlet} is based on \code{ddirichlet} by Gregory R. Warnes, Ben Bolker and Ian Wilson in package \code{gregmisc}.
}
}
\seealso{
\code{\link{DIRECT}} for the complete method.

\code{\link{DPMCMC}} for the MCMC sampler under the Dirichlet-process prior.

\code{\link{relabel}} for relabeling in posterior inference.
}
\examples{
## See example for DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
