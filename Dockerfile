# Use a base image with C++ and development tools
FROM ubuntu:22.04

# Set non-interactive mode for apt
ENV DEBIAN_FRONTEND=noninteractive

# Install required dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    git \
    libboost-all-dev \
    libgmp-dev \
    libpthread-stubs0-dev \
    gcc \
    g++ \
    python3 \
    python3-pip \
    && apt-get clean

# Create a symlink for python
RUN ln -s /usr/bin/python3 /usr/bin/python

# Clone the aeval repository and check out the specified branch
RUN git clone https://github.com/a-hamza-r/aeval.git /aeval && \
    cd /aeval && \
    git checkout equiv-check-sc-dev

# Build the project
WORKDIR /aeval
RUN mkdir build && cd build && \
    cmake ../ && \
    cmake --build . && \
    cmake /aeval && \
    make -j$(nproc) equiv-check

# Set the entrypoint to the build directory
WORKDIR /aeval/build

# Default command
CMD ["/bin/bash"]

