\name{plotClustersSD}
\alias{plotClustersSD}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Plotting Posterior Estimates of Cluster-Specific Random Effects 
}
\description{
Function \code{plotClustersSD} displays in a single plot the posterior estimates of cluster-specific standard deviations of the three types of variability (random effects) under the DIRECT model.  See figures in Fu, Russell, Bray and Tavare.
}
\usage{
plotClustersSD(data.summary, nTime, ...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{data.summary}{
The list generated from \code{\link{summaryDIRECT}} that contains processed posterior estimates.
}
  \item{nTime}{
Number of time points (or experimental conditions).
}
  \item{\dots}{
Additional arguments for \code{plot}.
}
}
\value{
None.
}
\references{
Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. Bayesian clustering with the Dirichlet-process prior.  
}
\author{
Audrey Q. Fu
}
\seealso{
\code{\link{summaryDIRECT}} for processing MCMC estimates for clustering and generating the list \code{data.summary} used here.

\code{\link{plotClustersPCA}}, \code{\link{plotClustersPCA}}, \code{\link{plotSimulation}}.
}
\examples{
## See example in DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
