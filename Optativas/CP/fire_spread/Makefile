# Compiladores
NVCC ?= nvcc
CXX ?= g++

# Flags
NVCCFLAGS = -O3 --use_fast_math -Xcompiler "-Wall -Wextra -Werror -fopenmp"
CXXFLAGS = -O3 -Wall -Wextra -Werror -fopenmp
INCLUDE = -I./src
NVCCCMD = $(NVCC) $(NVCCFLAGS) $(INCLUDE)

# Archivos fuente y objetos
cu_sources := $(wildcard ./src/*.cu)
cpp_sources := $(wildcard ./src/*.cpp)
cu_objects := $(cu_sources:./src/%.cu=./src/%.o)
cpp_objects := $(cpp_sources:./src/%.cpp=./src/%.o)
objects := $(cu_objects) $(cpp_objects)
headers := $(wildcard ./src/*.cuh)

# Ejecutables
mains = graphics/burned_probabilities_data graphics/fire_animation_data

# Regla por defecto
all: $(mains)

# Compilar .cu con nvcc
./src/%.o: ./src/%.cu $(headers)
	$(NVCCCMD) -c $< -o $@

# Compilar .cpp con g++
./src/%.o: ./src/%.cpp $(headers)
	$(CXX) $(CXXFLAGS) -I./src -c $< -o $@

# Linkear ejecutables con nvcc (para que maneje correctamente CUDA libs)
$(mains): %: %.cpp $(objects) $(headers)
	$(NVCCCMD) $< $(objects) -o $@

# Descargar datos
data.zip:
	wget https://cs.famaf.unc.edu.ar/~nicolasw/data.zip

data: data.zip
	unzip data.zip

clean:
	rm -f $(cu_objects) $(cpp_objects) $(mains)

.PHONY: all clean data
