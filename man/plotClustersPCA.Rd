\name{plotClustersPCA}
\alias{plotClustersPCA}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
PCA Plot for Posterior Allocation Probability Matrix
}
\description{
Function \code{plotClustersPCA} generates a Principal Components Analysis (PCA) plot for the posterior mean estimate of allocation probability matrix.  The first two principal components are used.  See figures in Fu, Russell, Bray and Tavare.
}
\usage{
plotClustersPCA(item.names, data.summary, 
    PCA.label.adj = -0.01, ...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{item.names}{
A vector of character strings, indicating how each item should be labeled in the PCA plot.
}
  \item{data.summary}{
The list generated from \code{\link{summaryDIRECT}} that contains processed posterior estimates.
}
  \item{PCA.label.adj}{
A scalar to be added to the coordinates of \code{item.names} for better display.
}
  \item{\dots}{
Additional arguments for \code{plot}.
}
}
\details{
The PCA plot produced here displays the uncertainty in the inferred clustering.  Each inferred cluster is shown with a distinct color.  The closer two clusters are in the PCA plot, the higher the level of uncertainty in inferring these two clusters.
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

\code{\link{plotClustersMean}}, \code{\link{plotClustersSD}}, \code{\link{plotSimulation}}.
}
\examples{
## See example in DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
