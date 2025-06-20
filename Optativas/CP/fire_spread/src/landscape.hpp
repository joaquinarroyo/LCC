#pragma once

#include "csv.hpp"
#include "matrix.hpp"
#include <cstdint>

// enum of vegetation type between: matorral, subalpine, wet, dry
enum VegetationType {
  MATORRAL,
  SUBALPINE,
  WET,
  DRY
} __attribute__((packed)); // packed so that it takes only 1 byte

static_assert( sizeof(VegetationType) == 1 );

struct LandscapeSoA {
  size_t width, height;

  std::vector<float> elevation;
  std::vector<float> fwi;
  std::vector<float> aspect;
  std::vector<float> vegetation_type;
  std::vector<float> wind_dir;
  std::vector<uint8_t> burnable;

  LandscapeSoA(size_t width, size_t height);
  LandscapeSoA(std::string metadata_filename, std::string data_filename);

  ~LandscapeSoA() = default;
};


