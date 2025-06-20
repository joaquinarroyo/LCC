#pragma once

#include <string>
#include <vector>

typedef std::vector<std::pair<size_t, size_t>> IgnitionCells;

IgnitionCells read_ignition_cells(std::string filename);
