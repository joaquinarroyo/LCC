#pragma once

#include <vector>
#include <cstdint>

#include "fires.hpp"
#include "landscape.hpp"

struct SimulationParams {
  float independent_pred;
  float wind_pred;
  float elevation_pred;
  float slope_pred;
  float subalpine_pred;
  float wet_pred;
  float dry_pred;
  float fwi_pred;
  float aspect_pred;
};

// TODO: Ver de pasar landscape como const std::vector<Cell>&
Fire simulate_fire(
  LandscapeSoA landscape, size_t n_row, size_t n_col, const std::vector<std::pair<size_t, size_t>>& ignition_cells,
  SimulationParams params, float distance, float elevation_mean, float elevation_sd, int n_replicate, float upper_limit
);
