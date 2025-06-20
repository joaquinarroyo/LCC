#include "ignition_cells.hpp"

#include <fstream>
#include <string>
#include <vector>

#include "csv.hpp"

IgnitionCells read_ignition_cells(std::string filename) {

  std::ifstream file(filename);

  if (!file.is_open()) {
    throw std::runtime_error("Can't open ignition cells file");
  }

  IgnitionCells ignition_cells;

  CSVIterator loop(file);
  loop++; // skip first line

  for (; loop != CSVIterator(); ++loop) {
    if (loop->size() < 2) {
      throw std::runtime_error("Invalid ignition cells file");
    }
    ignition_cells.push_back({ atoi((*loop)[0].data()), atoi((*loop)[1].data()) });
  }

  file.close();

  return ignition_cells;
}