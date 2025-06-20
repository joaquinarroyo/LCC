// spread_functions.cuh y otras dependencias asumidas cargadas correctamente
#include "spread_functions.cuh"

#define _USE_MATH_DEFINES
#include <cmath>
#include <vector>
#include <omp.h>
#include <iostream>
#include <array>
#include <random>

#include "fires.hpp"
#include "landscape.hpp"

#include <cuda_runtime.h>
#include <curand_kernel.h>
#include <cuda_runtime_api.h>

struct DeviceBuffers {
    int* frontier_0;
    int* frontier_1;
    int* next_frontier_0;
    int* next_frontier_1;
    int* frontier_size;
    int* next_frontier_count;
    int* done_flag;
    int* burned_bin;
    int* iteration_map;
    unsigned int* processed_cells;

    float* elevation;
    float* fwi;
    float* aspect;
    float* wind_dir;
    float* vegetation_type;
    uint8_t* burnable;

    SimulationParams* d_params;
    curandState* rng_states;
};

struct FireKernelParams {
    const float* elevation;
    const float* fwi;
    const float* aspect;
    const float* wind_dir;
    const float* vegetation_type;
    const uint8_t* burnable;

    int* burned_bin;
    int width;
    int height;

    unsigned int* processed_cells;
    const SimulationParams* params;

    float distance;
    float upper_limit;
    float elevation_mean;
    float elevation_sd;
};

constexpr float PIf = 3.1415927f;
constexpr float h_angles[8] = {
    PIf * 3 / 4, PIf, PIf * 5 / 4, PIf / 2,
    PIf * 3 / 2, PIf / 4, 0, PIf * 7 / 4
};
constexpr int h_moves[8][2] = {
    { -1, -1 }, { -1, 0 }, { -1, 1 }, { 0, -1 },
    { 0, 1 }, { 1, -1 }, { 1, 0 }, { 1, 1 }
};
__constant__ float d_angles[8];
__constant__ int d_moves[8][2];


////////////////////////////////// DEVICE //////////////////////////////


__global__ void init_rng_kernel(curandState* states, int width, int height, int seed) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int total = width * height;
    if (tid < total) {
        int i = tid % width;
        int j = tid / width;
        unsigned long long cell_seed = seed ^ (i * 73856093) ^ (j * 19349663);
        curand_init(cell_seed, 0, 0, &states[tid]);
    }
}


__device__ void spread_probability(
    float burning_elevation,
    float burning_wind_direction,
    const float* elevations,
    const float* vegetation_types,
    const float* fwis,
    const float* aspects,
    const float* upper_limits,
    const SimulationParams* params,
    float distance,
    float elevation_mean,
    float elevation_sd,
    float* probs_out
) {
    float fwi_pred = params->fwi_pred;
    float aspect_pred = params->aspect_pred;
    float wind_pred = params->wind_pred;
    float elevation_pred = params->elevation_pred;
    float slope_pred = params->slope_pred;
    float independent_pred = params->independent_pred;
    for (int n = 0; n < 8; n++) {
        float slope_term = __sinf(atanf((elevations[n] - burning_elevation) / distance));
        float wind_term = __cosf(d_angles[n] - burning_wind_direction);
        float elev_term = (elevations[n] - elevation_mean) / elevation_sd;

        float linpred = independent_pred;

        if ((int)vegetation_types[n] == SUBALPINE) {
            linpred += params->subalpine_pred;
        } else if ((int)vegetation_types[n] == WET) {
            linpred += params->wet_pred;
        } else if ((int)vegetation_types[n] == DRY) {
            linpred += params->dry_pred;
        }

        linpred += fwi_pred * fwis[n];
        linpred += aspect_pred * aspects[n];
        linpred += wind_term * wind_pred + elev_term * elevation_pred + slope_term * slope_pred;

        probs_out[n] = upper_limits[n] / (1.0f + __expf(-linpred));
    }
}


__global__ void fire_persistent_kernel(
    FireKernelParams args,
    int* frontier_0, int* frontier_1,
    int* frontier_size,
    int* next_frontier_0, int* next_frontier_1,
    int* next_frontier_count,
    int* iteration_map,
    int iteration_tag,
    int* done_flag,
    curandState* rng_states
) {
    unsigned long long start = clock64();
    const float* elevation = args.elevation;
    const float* fwi = args.fwi;
    const float* aspect = args.aspect;
    const float* wind_dir = args.wind_dir;
    const float* vegetation_type = args.vegetation_type;
    const uint8_t* burnable = args.burnable;

    int* burned_bin = args.burned_bin;
    int width = args.width;
    int height = args.height;
    const SimulationParams* params = args.params;

    float distance = args.distance;
    float upper_limit = args.upper_limit;
    float elevation_mean = args.elevation_mean;
    float elevation_sd = args.elevation_sd;
    
    unsigned int local_processed_cells = 0;
    
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    while (!*done_flag) {
        int frontier_len = *frontier_size;

        for (int idx = tid; idx < frontier_len; idx += gridDim.x * blockDim.x) {
            int i = frontier_0[idx];
            int j = frontier_1[idx];
            int center_idx = j * width + i;

            curandState local_state = rng_states[center_idx];

            float elev_c = elevation[center_idx];
            float wind_c = wind_dir[center_idx];

            int n_coords_0[8], n_coords_1[8];
            int n_indices[8];
            uint8_t n_out_flags[8];
            float n_elev[8], n_fwi[8], n_asp[8], n_veg[8], n_burn[8], n_upper[8];

            for (int n = 0; n < 8; ++n) {
                int ni = i + d_moves[n][0];
                int nj = j + d_moves[n][1];
                n_coords_0[n] = ni;
                n_coords_1[n] = nj;

                if (ni < 0 || nj < 0 || ni >= width || nj >= height) {
                    n_out_flags[n] = 1;
                    n_indices[n] = 0;
                    n_elev[n] = n_fwi[n] = n_asp[n] = n_veg[n] = 0.0f;
                    n_burn[n] = 0;
                } else {
                    int n_idx = nj * width + ni;
                    n_out_flags[n] = 0;
                    n_indices[n] = n_idx;
                    n_elev[n] = elevation[n_idx];
                    n_fwi[n] = fwi[n_idx];
                    n_asp[n] = aspect[n_idx];
                    n_veg[n] = vegetation_type[n_idx];
                    n_burn[n] = burnable[n_idx];
                    if (!n_out_flags[n]) {
                        ++local_processed_cells;
                    }
                }

                uint8_t burnable_mask = (!burned_bin[n_indices[n]] && n_burn[n]);
                uint8_t valid_mask = !n_out_flags[n] && burnable_mask;
                n_upper[n] = valid_mask * upper_limit;
            }

            float n_probs[8];
            spread_probability(
                elev_c, wind_c,
                n_elev, n_veg, n_fwi, n_asp, n_upper,
                params, distance, elevation_mean, elevation_sd,
                n_probs
            );

            for (int n = 0; n < 8; ++n) {
                float rnd = curand_uniform(&local_state);
                if (rnd < n_probs[n]) {
                    if (n_indices[n] >= 0 && !n_out_flags[n] && n_burn[n]) {
                        if (atomicCAS(&iteration_map[n_indices[n]], 0, iteration_tag) == 0) {
                            burned_bin[n_indices[n]] = 1;
                            int pos = atomicAdd(next_frontier_count, 1);
                            next_frontier_0[pos] = n_coords_0[n];
                            next_frontier_1[pos] = n_coords_1[n];
                        }
                    }
                }
            }
            rng_states[center_idx] = local_state;
        }

        __syncthreads();

        if (tid == 0) {
            int count = *next_frontier_count;
            *frontier_size = count;
            *next_frontier_count = 0;
            *done_flag = (count == 0);
        }

        __syncthreads();

        int* tmp0 = frontier_0;
        int* tmp1 = frontier_1;
        frontier_0 = next_frontier_0;
        frontier_1 = next_frontier_1;
        next_frontier_0 = tmp0;
        next_frontier_1 = tmp1;
    }

    if (local_processed_cells)
        atomicAdd(args.processed_cells, local_processed_cells);
    unsigned long long end = clock64();
}


////////////////////////////// HOST //////////////////////////////


DeviceBuffers allocate_device_memory(size_t MAX_CELLS) {
    DeviceBuffers buf = {};
    cudaMalloc(&buf.frontier_0, MAX_CELLS * sizeof(int));
    cudaMalloc(&buf.frontier_1, MAX_CELLS * sizeof(int));
    cudaMalloc(&buf.next_frontier_0, MAX_CELLS * sizeof(int));
    cudaMalloc(&buf.next_frontier_1, MAX_CELLS * sizeof(int));
    cudaMalloc(&buf.frontier_size, sizeof(int));
    cudaMalloc(&buf.next_frontier_count, sizeof(int));
    cudaMalloc(&buf.done_flag, sizeof(int));
    cudaMalloc(&buf.burned_bin, MAX_CELLS * sizeof(int));
    cudaMalloc(&buf.processed_cells, sizeof(unsigned int));
    cudaMalloc(&buf.iteration_map, MAX_CELLS * sizeof(int));
    cudaMemset(buf.iteration_map, 0, MAX_CELLS * sizeof(int));

    cudaMalloc(&buf.elevation, MAX_CELLS * sizeof(float));
    cudaMalloc(&buf.fwi, MAX_CELLS * sizeof(float));
    cudaMalloc(&buf.aspect, MAX_CELLS * sizeof(float));
    cudaMalloc(&buf.wind_dir, MAX_CELLS * sizeof(float));
    cudaMalloc(&buf.vegetation_type, MAX_CELLS * sizeof(float));
    cudaMalloc(&buf.burnable, MAX_CELLS * sizeof(uint8_t));

    cudaMalloc(&buf.d_params, sizeof(SimulationParams));
    cudaMalloc(&buf.rng_states, MAX_CELLS * sizeof(curandState));

    return buf;
}


void copy_inputs_to_device(
    const LandscapeSoA& landscape,
    const std::vector<std::pair<size_t, size_t>>& ignition_cells,
    const SimulationParams& params,
    DeviceBuffers& buf,
    int n_col,
    size_t MAX_CELLS
) {
    // Convert ignition to burned_bin
    std::vector<int> burned_bin(MAX_CELLS, 0);
    std::vector<int> h_frontier_0(MAX_CELLS, -1);
    std::vector<int> h_frontier_1(MAX_CELLS, -1);

    for (size_t i = 0; i < ignition_cells.size(); ++i) {
        auto [x, y] = ignition_cells[i];
        h_frontier_0[i] = x;
        h_frontier_1[i] = y;
        burned_bin[utils::INDEX(x, y, n_col)] = 1;
    }

    int init_size = ignition_cells.size();

    cudaMemcpy(buf.frontier_0, h_frontier_0.data(), init_size * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.frontier_1, h_frontier_1.data(), init_size * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.frontier_size, &init_size, sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.burned_bin, burned_bin.data(), MAX_CELLS * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.elevation, landscape.elevation.data(), MAX_CELLS * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.fwi, landscape.fwi.data(), MAX_CELLS * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.aspect, landscape.aspect.data(), MAX_CELLS * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.wind_dir, landscape.wind_dir.data(), MAX_CELLS * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.vegetation_type, landscape.vegetation_type.data(), MAX_CELLS * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.burnable, landscape.burnable.data(), MAX_CELLS * sizeof(uint8_t), cudaMemcpyHostToDevice);
    cudaMemcpy(buf.d_params, &params, sizeof(SimulationParams), cudaMemcpyHostToDevice);

    cudaMemset(buf.next_frontier_count, 0, sizeof(int));
    cudaMemset(buf.done_flag, 0, sizeof(int));
    cudaMemset(buf.processed_cells, 0, sizeof(unsigned int));
}


void initialize_rng(DeviceBuffers& buf, int n_row, int n_col, int seed, int threads_per_block, int num_blocks) {
    init_rng_kernel<<<num_blocks, threads_per_block>>>(buf.rng_states, n_col, n_row, seed);
}


void launch_kernel(DeviceBuffers& buf, FireKernelParams& args, int threads_per_block, int num_blocks) {
    int iteration_tag = 1;
    fire_persistent_kernel<<<num_blocks, threads_per_block>>>(
        args,
        buf.frontier_0, buf.frontier_1, buf.frontier_size,
        buf.next_frontier_0, buf.next_frontier_1, buf.next_frontier_count,
        buf.iteration_map, iteration_tag,
        buf.done_flag, buf.rng_states
    );
    cudaDeviceSynchronize();
}


Fire copy_results_from_device(
    const DeviceBuffers& buf,
    size_t n_row,
    size_t n_col
) {
    size_t MAX_CELLS = n_row * n_col;

    std::vector<int> burned_bin(MAX_CELLS);
    cudaMemcpy(burned_bin.data(), buf.burned_bin, MAX_CELLS * sizeof(int), cudaMemcpyDeviceToHost);

    std::vector<size_t> ids_0, ids_1;
    for (size_t j = 0; j < n_row; ++j) {
        for (size_t i = 0; i < n_col; ++i) {
            if (burned_bin[utils::INDEX(i, j, n_col)]) {
                ids_0.push_back(i);
                ids_1.push_back(j);
            }
        }
    }

    unsigned int processed_cells;
    cudaMemcpy(&processed_cells, buf.processed_cells, sizeof(unsigned int), cudaMemcpyDeviceToHost);

    return Fire{
        n_col, n_row,
        processed_cells,
        0.0,
        burned_bin,
        ids_0, ids_1,
        { ids_0.size() }
    };
}


void free_device_memory(DeviceBuffers& buf) {
    cudaFree(buf.frontier_0); cudaFree(buf.frontier_1);
    cudaFree(buf.next_frontier_0); cudaFree(buf.next_frontier_1);
    cudaFree(buf.frontier_size); cudaFree(buf.next_frontier_count);
    cudaFree(buf.done_flag); cudaFree(buf.burned_bin);
    cudaFree(buf.iteration_map); cudaFree(buf.processed_cells);

    cudaFree(buf.elevation); cudaFree(buf.fwi); cudaFree(buf.aspect);
    cudaFree(buf.wind_dir); cudaFree(buf.vegetation_type); cudaFree(buf.burnable);

    cudaFree(buf.d_params); cudaFree(buf.rng_states);
}


Fire simulate_fire(
    LandscapeSoA landscape,
    size_t n_row, size_t n_col,
    const std::vector<std::pair<size_t, size_t>>& ignition_cells,
    SimulationParams params,
    float distance,
    float elevation_mean,
    float elevation_sd,
    int n_replicate,
    float upper_limit = 1.0f
) {
    const size_t MAX_CELLS = n_row * n_col;
    const int threads_per_block = 256;
    const int num_blocks = (MAX_CELLS + threads_per_block - 1) / threads_per_block;

    cudaMemcpyToSymbol(d_angles, h_angles, sizeof(h_angles));
    cudaMemcpyToSymbol(d_moves, h_moves, sizeof(h_moves));

    DeviceBuffers buf = allocate_device_memory(MAX_CELLS);

    copy_inputs_to_device(landscape, ignition_cells, params, buf, n_col, MAX_CELLS);

    initialize_rng(buf, n_row, n_col, 123 + n_replicate, threads_per_block, num_blocks);

    FireKernelParams args = {
        buf.elevation, buf.fwi, buf.aspect, buf.wind_dir, buf.vegetation_type,
        buf.burnable, buf.burned_bin,
        static_cast<int>(n_col), static_cast<int>(n_row),
        buf.processed_cells,
        buf.d_params,
        distance, upper_limit, elevation_mean, elevation_sd,
    };

    // 🔽 NUEVO: MEDICIÓN DE TIEMPO CON EVENTOS CUDA
    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);
    cudaEventRecord(start);

    launch_kernel(buf, args, threads_per_block, num_blocks);

    cudaEventRecord(stop);
    cudaEventSynchronize(stop);
    float milliseconds = 0;
    cudaEventElapsedTime(&milliseconds, start, stop);

    cudaEventDestroy(start);
    cudaEventDestroy(stop);

    float seconds = milliseconds / 1000.0f;

    Fire result = copy_results_from_device(buf, n_row, n_col);

    free_device_memory(buf);

    result.time_taken = seconds;

    return result;
}
