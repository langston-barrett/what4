CXX      ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable
SRCS     := BaseRange.cpp StridedWrappedRange.cpp main.cpp
OBJS     := $(SRCS:.cpp=.o)
TARGET   := sasi-precision

$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -I. -c -o $@ $<

clean:
	rm -f $(OBJS) $(TARGET)

.PHONY: clean
