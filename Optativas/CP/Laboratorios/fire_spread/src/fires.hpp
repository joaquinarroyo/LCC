#pragma once

#include <cstddef>
#include <vector>

#include "landscape.hpp"
#include "matrix.hpp"

struct Fire {
  size_t width;
  size_t height;

  Matrix<bool> burned_layer;

  std::vector<std::pair<size_t, size_t>> burned_ids;

  // Positions in burned_ids where a new step starts, empty if the fire was not simulated
  std::vector<size_t> burned_ids_steps;

  bool operator==(const Fire& other) const {
    return width == other.width && height == other.height &&
           burned_layer == other.burned_layer && burned_ids == other.burned_ids;
  }
};

Fire read_fire(size_t width, size_t height, std::string filename);

/* Type and function useful for comparing fires */

struct FireStats {
  size_t counts_veg_matorral;
  size_t counts_veg_subalpine;
  size_t counts_veg_wet;
  size_t counts_veg_dry;
};

FireStats get_fire_stats(const Fire& fire, const Landscape& landscape);
