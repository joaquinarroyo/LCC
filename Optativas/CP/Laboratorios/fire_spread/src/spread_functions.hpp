#pragma once

#include <vector>

#include "fires.hpp"
#include "landscape.hpp"

struct SimulationParams {
  double independent_pred;
  double wind_pred;
  double elevation_pred;
  double slope_pred;
  double subalpine_pred;
  double wet_pred;
  double dry_pred;
  double fwi_pred;
  double aspect_pred;
};

Fire simulate_fire(
    const Landscape& landscape, const std::vector<std::pair<size_t, size_t>>& ignition_cells,
    SimulationParams params, double distance, double elevation_mean, double elevation_sd,
    double upper_limit
);
