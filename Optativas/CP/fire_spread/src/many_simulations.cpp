#include "many_simulations.hpp"

#include <iostream>
#include <cmath>
#include <fstream>
#include <algorithm>
#include <numeric>
#include "fires.hpp"

#define PERF_FILENAME "graphics/simdata/burned_probabilities_perf_data_"

Matrix<size_t> burned_amounts_per_cell(
    const LandscapeSoA& landscape, const std::vector<std::pair<size_t, size_t>>& ignition_cells,
    SimulationParams params, float distance, float elevation_mean, float elevation_sd,
    float upper_limit, size_t n_replicates, std::string output_filename_suffix
) {
  size_t n_col = landscape.width;
  size_t n_row = landscape.height;

  Matrix<size_t> burned_amounts(n_col, n_row);
  float max_metric = 0.0f;
  float total_time_taken = 0.0f;

  for (size_t i = 0; i < n_replicates; i++) {
    Fire fire = simulate_fire(
      landscape, n_row, n_col, ignition_cells, params,
      distance, elevation_mean, elevation_sd, i, upper_limit
    );

    float metric = fire.processed_cells / (fire.time_taken * 1e6);
    
    max_metric = std::max(max_metric, metric);
    total_time_taken += fire.time_taken;

    for (size_t col = 0; col < n_col; col++) {
      for (size_t row = 0; row < n_row; row++) {
        if (fire.burned_layer[utils::INDEX(col, row, n_col)]) {
          burned_amounts[{col, row}] += 1;
        }
      }
    }
  }

  // Guardamos data de la performance para graficar
  std::ofstream outputFile(PERF_FILENAME + output_filename_suffix + ".txt", std::ios::app);
  outputFile << "1, " << n_col * n_row << ", " << max_metric << ", " << total_time_taken << std::endl;
  outputFile.close();

  std::cout << "  SIMULATION PERFORMANCE DATA" << std::endl;
  std::cout << "* Total time taken: " << total_time_taken << " seconds" << std::endl;
  std::cout << "* Average time per simulation: " << total_time_taken / n_replicates << " seconds" << std::endl;
  std::cout << "* Max metric: " << max_metric << " cells/nanosec processed" << std::endl;

  return burned_amounts;
}
