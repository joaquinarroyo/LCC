#pragma once

template <typename T> struct Matrix {
  size_t width;
  size_t height;

  Matrix(size_t width, size_t height) : width(width), height(height), elems(width * height){};

  const T operator[](std::pair<size_t, size_t> index) const {
    return elems[index.second * width + index.first];
  };

  T& operator[](std::pair<size_t, size_t> index) {
    return elems[index.second * width + index.first];
  };

  bool operator==(const Matrix& other) const {
    if (width != other.width || height != other.height) {
      return false;
    }

    for (size_t i = 0; i < width * height; i++) {
      if (elems[i] != other.elems[i]) {
        return false;
      }
    }

    return true;
  };

  std::vector<T> elems;
};

template <> struct Matrix<bool> {
  size_t width;
  size_t height;

  Matrix(size_t width, size_t height) : width(width), height(height), elems(width * height){};

  bool operator[](std::pair<size_t, size_t> index) const {
    return elems[index.second * width + index.first];
  };

  struct SmartReference {
    std::vector<bool>& values;
    size_t index;
    operator bool() const {
      return values[index];
    }
    SmartReference& operator=(bool const& other) {
      values[index] = other;
      return *this;
    }
  };

  SmartReference operator[](std::pair<size_t, size_t> index) {
    return SmartReference{ elems, index.second * width + index.first };
  }

  bool operator==(const Matrix& other) const {
    if (width != other.width || height != other.height) {
      return false;
    }

    for (size_t i = 0; i < width * height; i++) {
      if (elems[i] != other.elems[i]) {
        return false;
      }
    }

    return true;
  };

  std::vector<bool> elems;
};
