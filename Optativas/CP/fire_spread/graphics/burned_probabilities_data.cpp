#include <iostream>
#include <string>
#include <fstream>

#include "ignition_cells.hpp"
#include "landscape.hpp"
#include "many_simulations.hpp"
#include "spread_functions.cuh"

#define DISTANCE 30.0f
#define ELEVATION_MEAN 1163.3f
#define ELEVATION_SD 399.5f
#define UPPER_LIMIT 0.5f
#ifndef N_REPLICATES
#define N_REPLICATES 100
#endif
#define FILENAME "graphics/simdata/burned_probabilities_data.txt"

int main(int argc, char* argv[]) {
  try {

    // check if the number of arguments is correct
    if (argc != 3) {
      std::cerr << "Usage: " << argv[0] << " <landscape_file_prefix> <output_filename_suffix>" << std::endl;
      return EXIT_FAILURE;
    }

    // read the landscape file prefix
    std::string landscape_file_prefix = argv[1];
    std::string output_filename_suffix = argv[2];

    // read the landscape
    LandscapeSoA landscape(landscape_file_prefix + "-metadata.csv", landscape_file_prefix + "-landscape.csv");

    // read the ignition cells
    IgnitionCells ignition_cells =
        read_ignition_cells(landscape_file_prefix + "-ignition_points.csv");

    SimulationParams params = {
      0.0f, 0.5f, 0.2f, 0.2f, 0.2f, 0.2f, 0.2f, 0.2f, 0.2f
    };

    Matrix<size_t> burned_amounts = burned_amounts_per_cell(
        landscape, ignition_cells, params, DISTANCE, ELEVATION_MEAN, ELEVATION_SD, UPPER_LIMIT, N_REPLICATES, output_filename_suffix
    );
    // Abrir el archivo de salida y crear la cadena con información
    std::ofstream outputFile(FILENAME);
    outputFile << "Landscape size: " << landscape.width << " " << landscape.height << std::endl;
    outputFile << "Simulations: " << N_REPLICATES << std::endl;
    // Escribir los valores de burned_amounts en el archivo
    for (size_t i = 0; i < landscape.height; i++) {
        for (size_t j = 0; j < landscape.width; j++) {
            if (j != 0) {
                outputFile << " ";
            }
            outputFile << burned_amounts[{j, i}];
        }
        outputFile << std::endl;
    }
    // Cerrar archivo de salida
    outputFile.close();
  } catch (std::runtime_error& e) {
    std::cerr << "ERROR: " << e.what() << std::endl;
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}