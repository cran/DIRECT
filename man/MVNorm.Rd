\name{MVNorm}
\alias{rMVNorm}
\alias{dMVNorm}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
The Multivariate Normal Distribution
}
\description{
Functions to compute the density of a multivariate normal distribution and to generate random realizations from such a distribution.
}
\usage{
dMVNorm (x, mean, sigma, log = FALSE)
rMVNorm (n, mean = rep(0, nrow(sigma)), sigma = diag(length(mean)),
         method=c("eigen", "svd", "chol"))
}
%- maybe also 'usage' for other objects documented here.
\arguments{
 \item{x}{Vector or matrix of quantiles. If \code{x} is a matrix, each
   row is taken to be a quantile.}
 \item{n}{Number of realizations.}
 \item{mean}{Mean vector, default is \code{rep(0, length = ncol(x))}.}
 \item{sigma}{Covariance matrix, default is \code{diag(ncol(x))}.}
 \item{log}{Logical; if \code{TRUE}, densities are log-transformed.}
 \item{method}{Matrix decomposition used to determine the matrix root of
  \code{sigma}, possible methods are eigenvalue decomposition
	(\code{"eigen"}, default), singular value decomposition
	(\code{"svd"}), and Cholesky decomposition (\code{"chol"}).}
}
\value{
\code{rMVNorm} returns a vector of the same length as \code{mean} if \code{n}=1, or a matrix with each row being an independent realization otherwise.
}
\author{
The code for both functions is taken from similar functions written by Friedrich Leisch and Fabian Scheipl in R package \code{mvtnorm}.  Audrey Q. Fu modified \code{dMVNorm} to use a different method to compute the matrix determinants.
}
\examples{
\dontrun{
x <- rMVNorm (10, mean=rep(0,3), method="svd")
dMVNorm (x, mean=rep(0,3), log=TRUE)
}
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
