#!/bin/bash

# Lista de data a procesar
data="1999_27j_S"
threads=(
  "2" "4" "6" "8" "10" "12"
)

if [ -z "$1" ]; then
  echo "Por favor, ingresa 'burned_probabilities' o 'fire_animation' como argumento"
  exit 1
fi

if [[ "$1" != "burned_probabilities" && "$1" != "fire_animation" ]]; then
  echo "Por favor, ingresa 'burned_probabilities' o 'fire_animation' como argumento"
  exit 1
fi

# Definir el programa por defecto
program="burned_probabilities_data"
if [ "$1" == "fire_animation" ]; then
  program="fire_animation_data"
fi

# Cantidad de repeticiones
reps=10
for rep in $(seq 1 $reps); do
  echo "Repetición $rep"
  i=0
  for thread in "${threads[@]}"; do
    export OMP_NUM_THREADS=$thread
    export OMP_PROC_BIND=spread
    export OMP_PLACES=threads
    echo "$i. Ejecutando $program sobre $data threads: $OMP_NUM_THREADS (Repetición $rep)"
    ./graphics/$program ./data/$data 2>&1 threads | tee ./stats/rep${rep}_${i}_${data}.txt
    i=$((i+1))
  done
done
