#include "landscape.hpp"

#include <fstream>
#include <cstddef>
#include <string>
#include <vector>

LandscapeSoA::LandscapeSoA(size_t width, size_t height)
    : width(width), height(height),
      elevation(width * height),
      fwi(width * height),
      aspect(width * height),
      vegetation_type(width * height),
      wind_dir(width * height),
      burnable(width * height) {}

LandscapeSoA::LandscapeSoA(std::string metadata_filename, std::string data_filename)
    : width(0), height(0) {
  std::ifstream metadata_file(metadata_filename);

  if (!metadata_file.is_open()) {
    throw std::runtime_error("Can't open metadata file");
  }

  CSVIterator metadata_csv(metadata_file);
  ++metadata_csv;
  if (metadata_csv == CSVIterator() || (*metadata_csv).size() < 2) {
    throw std::runtime_error("Invalid metadata file");
  }

  width = atoi((*metadata_csv)[0].data());
  height = atoi((*metadata_csv)[1].data());

  // Inicializa los arrays SoA
  fwi.resize(width * height);
  aspect.resize(width * height);
  wind_dir.resize(width * height);
  elevation.resize(width * height);
  burnable.resize(width * height);
  vegetation_type.resize(width * height);

  metadata_file.close();

  std::ifstream landscape_file(data_filename);

  if (!landscape_file.is_open()) {
    throw std::runtime_error("Can't open landscape file");
  }

  CSVIterator loop_csv(landscape_file);
  ++loop_csv;

  for (size_t j = 0; j < height; j++) {
    for (size_t i = 0; i < width; i++, ++loop_csv) {
      if (loop_csv == CSVIterator() || (*loop_csv).size() < 8) {
        throw std::runtime_error("Invalid landscape file");
      }
      size_t idx = j * width + i;
      if (atoi((*loop_csv)[0].data()) == 1) {
        vegetation_type[idx] = SUBALPINE;
      } else if (atoi((*loop_csv)[1].data()) == 1) {
        vegetation_type[idx] = WET;
      } else if (atoi((*loop_csv)[2].data()) == 1) {
        vegetation_type[idx] = DRY;
      } else {
        vegetation_type[idx] = MATORRAL;
      }
      fwi[idx] = atof((*loop_csv)[3].data());
      aspect[idx] = atof((*loop_csv)[4].data());
      wind_dir[idx] = atof((*loop_csv)[5].data());
      elevation[idx] = atof((*loop_csv)[6].data());
      burnable[idx] = atoi((*loop_csv)[7].data());
    }
  }

  landscape_file.close();
}