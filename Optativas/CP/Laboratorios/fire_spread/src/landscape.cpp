#include "landscape.hpp"

#include <fstream>
#include <cstddef>
#include <string>

Landscape::Landscape(size_t width, size_t height)
    : width(width), height(height), cells(width, height) {}

Landscape::Landscape(std::string metadata_filename, std::string data_filename) : cells(0, 0) {
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

  cells = Matrix<Cell>(width, height);

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
      if (atoi((*loop_csv)[0].data()) == 1) {
        cells[{i, j}].vegetation_type = SUBALPINE;
      } else if (atoi((*loop_csv)[1].data()) == 1) {
        cells[{i, j}].vegetation_type = WET;
      } else if (atoi((*loop_csv)[2].data()) == 1) {
        cells[{i, j}].vegetation_type = DRY;
      } else {
        cells[{i, j}].vegetation_type = MATORRAL;
      }
      cells[{i, j}].fwi = atof((*loop_csv)[3].data());
      cells[{i, j}].aspect = atof((*loop_csv)[4].data());
      cells[{i, j}].wind_direction = atof((*loop_csv)[5].data());
      cells[{i, j}].elevation = atof((*loop_csv)[6].data());
      cells[{i, j}].burnable = atoi((*loop_csv)[7].data());
    }
  }

  landscape_file.close();
}

Cell Landscape::operator[](std::pair<size_t, size_t> index) const {
  return cells[index];
}

Cell& Landscape::operator[](std::pair<size_t, size_t> index) {
  return cells[index];
}
