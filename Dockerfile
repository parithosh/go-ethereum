# Build Go compiler container
FROM golang:1.24-alpine AS builder
RUN apk add --no-cache gcc musl-dev linux-headers git bash

# Get Go fork and build it.
RUN git clone --branch modexpfix https://github.com/GottfriedHerold/go-modexp /go-modexp
WORKDIR /go-modexp/src
RUN ./make.bash

# Build Geth.
ADD . /go-ethereum
RUN cd /go-ethereum && /go-modexp/bin/go run build/ci.go install -static ./cmd/geth

# Pull Geth into a second stage deploy alpine container
FROM alpine:latest

RUN apk add --no-cache ca-certificates
COPY --from=builder /go-ethereum/build/bin/geth /usr/local/bin/

EXPOSE 8545 8546 30303 30303/udp
ENTRYPOINT ["geth"]

# Add some metadata labels to help programmatic image consumption
ARG COMMIT=""
ARG VERSION=""
ARG BUILDNUM=""

LABEL commit="$COMMIT" version="$VERSION" buildnum="$BUILDNUM"
