\name{DIRECT-package}
\alias{DIRECT-package}
%\alias{DIRECT}
\docType{package}
\title{Bayesian Clustering of Multivariate Data with the Dirichlet-Process Prior}
\description{This package implements the Bayesian clustering method in Fu et al. (2013).  It also contains a simulation function to generate data under the random-effects mixture model presented in this paper, as well as summary and plotting functions to process MCMC samples and display the clustering results.  Replicated time-course microarray gene expression data analyzed in this paper are in \code{tc.data}.}
\details{This package three sets of functions.
\itemize{
  \item Functions \code{\link{DIRECT}} and others for clustering data.  They estimate the number of clusters and infers the partition for multivariate data, e.g., replicated time-course microarray gene expression data.  The clustering method involves a random-effects mixture model that decomposes the total variability in the data into within-cluster variability, variability across experimental conditions (e.g., time points), and variability in replicates (i.e., residual variability).  The clustering method uses a Dirichlet-process prior to induce a distribution on the number of clusters as well as clustering.  It uses Metropolis-Hastings Markov chain Monte Carlo for parameter estimation.  To estimate the posterior allocation probability matrix while dealing with the label-switching problem, there is a two-step posterior inference procedure involving resampling and relabeling.
  \item Functions for processing MCMC samples and plotting the clustering results.
  \item Functions for simulating data under the random-effects mixture model.
}

See \code{\link{DIRECT}} for details on using the function for clustering.

See \code{\link{summaryDIRECT}}, which points to other related plotting functions, for details on how to process MCMC samples and display clustering results.

See \code{\link{simuDataREM}}, which points to other related functions, for simulating data under the random-effects mixture model.
}
\author{
Audrey Qiuyan Fu

Maintainer: Audrey Q. Fu <audreyqyfu@gmail.com>
}
\references{
Fu, A. Q., Russell, S., Bray, S. and Tavare, S. (2013) Bayesian clustering of replicated time-course gene expression data with weak signals. The Annals of Applied Statistics. 7(3) 1334-1361.
}
%~~ Optionally other standard keywords, one per line, from file KEYWORDS in the R documentation directory ~~
\keyword{ package }
\seealso{
\code{\link{DIRECT}} for the clustering method.

\code{\link{summaryDIRECT}} for processing MCMC estimates for clustering.

\code{\link{simuDataREM}} for simulating data under the mixture random-effects model.
}
\examples{
## See examples in DIRECT and simuDataREM.
}