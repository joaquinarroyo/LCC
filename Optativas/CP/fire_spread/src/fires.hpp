#pragma once

#include <cstddef>
#include <vector>
#include <cstdint>

#include "landscape.hpp"
#include "matrix.hpp"

struct Fire {
  size_t width;
  size_t height;
  unsigned int processed_cells; // number of cells processed in the simulation TODO: Revisar si usamos size_t o int
  double time_taken; // time spent in the simulation
  std::vector<int> burned_layer;
  std::vector<size_t> burned_ids_0;
  std::vector<size_t> burned_ids_1;
  // Positions in burned_ids where a new step starts, empty if the fire was not simulated
  std::vector<size_t> burned_ids_steps;
  bool operator==(const Fire& other) const {
    return 
      width == other.width && 
      height == other.height &&
      burned_layer == other.burned_layer && 
      burned_ids_0 == other.burned_ids_0 &&
      burned_ids_1 == other.burned_ids_1;
  }
};

Fire read_fire(size_t width, size_t height, std::string filename);

Fire empty_fire(size_t width, size_t height);

/* Type and function useful for comparing fires */

struct FireStats {
  size_t counts_veg_matorral;
  size_t counts_veg_subalpine;
  size_t counts_veg_wet;
  size_t counts_veg_dry;
};

FireStats get_fire_stats(const Fire& fire, const LandscapeSoA& landscape);

namespace utils {
  inline size_t INDEX(size_t x, size_t y, size_t width) {
    return x + y * width;
  }
}