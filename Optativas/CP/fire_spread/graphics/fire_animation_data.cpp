#include <iostream>
#include <random>
#include <fstream>

#include "fires.hpp"
#include "ignition_cells.hpp"
#include "landscape.hpp"
#include "many_simulations.hpp"
#include "spread_functions.cuh"

#define DISTANCE 30
#define ELEVATION_MEAN 1163.3
#define ELEVATION_SD 399.5
#define UPPER_LIMIT 0.75
#ifndef N_REPLICATES
#define N_REPLICATES 100
#endif
#define FILENAME "graphics/simdata/fire_animation_data.txt"
#define PERF_FILENAME "graphics/simdata/fire_animation_perf_data.txt"

// main function reading command line arguments
int main(int argc, char* argv[]) {
  try {

    // check if the number of arguments is correct
    if (argc != 2) {
      std::cerr << "Usage: " << argv[0] << " <landscape_file_prefix>" << std::endl;
      return EXIT_FAILURE;
    }

    // read the landscape file prefix
    std::string landscape_file_prefix = argv[1];

    // read the landscape
    LandscapeSoA landscape(landscape_file_prefix + "-metadata.csv", landscape_file_prefix + "-landscape.csv");

    // read the ignition cells
    IgnitionCells ignition_cells =
        read_ignition_cells(landscape_file_prefix + "-ignition_points.csv");

    SimulationParams params = {
      0, 0.5, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2
    };

    double min_metric = 1e15;
    double max_metric = 0;
    double total_time_taken = 0;
    int n_row = landscape.height;
    int n_col = landscape.width;
    Fire fire = empty_fire(n_row, n_col);
    for (size_t i = 0; i < N_REPLICATES; i++) {
      Fire fire = simulate_fire(
        landscape, n_row, n_col, ignition_cells, params, DISTANCE, ELEVATION_MEAN, ELEVATION_SD, i, UPPER_LIMIT
      );
      double time_taken = fire.time_taken;
      double metric = fire.processed_cells / (time_taken * 1e6);
      total_time_taken += time_taken;
      min_metric = std::min(min_metric, metric);
      max_metric = std::max(max_metric, metric);
    }

    std::cout << "  SIMULATION PERFORMANCE DATA" << std::endl;
    std::cout << "* Total time taken: " << total_time_taken << " seconds" << std::endl;
    std::cout << "* Average time: " << total_time_taken / N_REPLICATES << " seconds" << std::endl;
    std::cout << "* Min metric: " << min_metric << " cells/nanosec processed" << std::endl;
    std::cout << "* Max metric: " << max_metric << " cells/nanosec processed" << std::endl;

    // Guardamos data de la performance para graficar
    std::ofstream perfOutputFile(PERF_FILENAME, std::ios::app);
    perfOutputFile << landscape.width * landscape.height << ", " << min_metric << ", " << max_metric << ", " << total_time_taken << std::endl;
    perfOutputFile.close();

    // Abrir el archivo de salida y crear la cadena con información
    std::ofstream outputFile(FILENAME);
    outputFile << "Landscape size: " << landscape.width << " " << landscape.height << std::endl;
    size_t step = 0;
    size_t i = 0;
    for (size_t j : fire.burned_ids_steps) {
      if (i >= j) {
        continue;
      }
      outputFile << "Step " << step << ":" << std::endl;
      for (; i < j; i++) {
        outputFile << fire.burned_ids_0[i] << " " << fire.burned_ids_1[i] << std::endl;
      }
      step++;
    }
    outputFile.close();
  } catch (std::runtime_error& e) {
    std::cerr << "ERROR: " << e.what() << std::endl;
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
