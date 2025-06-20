#!/bin/bash

if [ -z "$1" ]; then
  echo "Por favor, ingresa 'burned_probabilities' o 'fire_animation' como argumento"
  exit 1
fi

if [[ "$1" != "burned_probabilities" && "$1" != "fire_animation" ]]; then
  echo "Por favor, ingresa 'burned_probabilities' o 'fire_animation' como argumento"
  exit 1
fi

python3 ./graphics/generate_plots.py $1 "${@:2}"