#include "fires.hpp"

#include <fstream>

#include "landscape.hpp"
#include "matrix.hpp"


Fire read_fire(size_t width, size_t height, std::string filename) {

  std::ifstream burned_ids_file(filename);

  if (!burned_ids_file.is_open()) {
    throw std::runtime_error("Can't open landscape file");
  }

  CSVIterator loop(burned_ids_file);
  loop++;

  std::vector<int> burned_layer(width * height, false);
  std::vector<size_t> burned_ids_0;
  std::vector<size_t> burned_ids_1;

  for (; loop != CSVIterator(); ++loop) {
    if (loop->size() < 2) {
      throw std::runtime_error("Invalid fire file");
    }
    size_t x = atoi((*loop)[0].data());
    size_t y = atoi((*loop)[1].data());
    if (x >= width || y >= height) {
      throw std::runtime_error("Invalid fire file");
    }
    burned_layer[utils::INDEX(x, y, width)] = 1;
    burned_ids_0.push_back(x);
    burned_ids_1.push_back(y);
  }

  burned_ids_file.close();

  return { width, height, 0, 0, burned_layer, burned_ids_0, burned_ids_1, {} };
}

Fire empty_fire(size_t width, size_t height) {
  return { width, height, 0, 0, std::vector<int>(width * height), {}, {}, {} };
}

FireStats get_fire_stats(const Fire& fire, const LandscapeSoA& landscape) {

  FireStats stats = { 0, 0, 0, 0 };
  size_t n = fire.burned_ids_0.size();
  for (size_t i = 0; i < n; i++) {
    size_t x = fire.burned_ids_0[i];
    size_t y = fire.burned_ids_1[i];
    size_t idx = utils::INDEX(x, y, landscape.width);

    if (landscape.vegetation_type[idx] == SUBALPINE) {
      stats.counts_veg_subalpine++;
    } else if (landscape.vegetation_type[idx] == WET) {
      stats.counts_veg_wet++;
    } else if (landscape.vegetation_type[idx] == DRY) {
      stats.counts_veg_dry++;
    } else {
      stats.counts_veg_matorral++;
    }
  }

  return stats;
}