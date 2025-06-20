import matplotlib.pyplot as plt
import numpy as np
import sys

FILENAME = "./graphics/simdata/{}_perf_data_{}.txt"
DIR = "./plots/"

DATA_NAMES = {
    2548: '2005_26',
    8008: '2000_8',
    13125: '2011_19W',
    14161: '2005_6',
    15912: '2009_3',
    48614: '2011_19E',
    94188: '1999_28',
    143655: '1999_27j_N',
    1483274: '1999_27j_S',
    4696595: '2021_865',
    10434109: '2015_50'
}

def read_perf_data(name, versions):
    """
    Reads the performance data from the file

    Example input:
    m*n, max_metric, time

    Example output:
    {
        m*n: (max_metric, time)
    }
    """
    data = {}
    for version in versions:
        inner_data = {}
        with open(FILENAME.format(name, version), "r") as file:
            lines = file.readlines()
            for line in lines:
                _, cells, max_metric, time = line.split(",")
                if int(cells) in inner_data.keys():
                    inner_data[int(cells)].append((float(max_metric), float(time)))
                else:
                    inner_data[int(cells)] = [(float(max_metric), float(time))]
        for key, value in inner_data.items():
            max_metric = max([x[0] for x in value])
            time = min([x[1] for x in value])
            if key in data.keys():
                data[key].append((max_metric, time))
            else:
                data[key] = [(max_metric, time)]
    return data

def read_perf_data_by_thread(name):
    """
    Reads the performance data from the file

    Example input:
    thread_n, m*n, max_metric, time
    
    Example output:
    {
        thread_n: (max_metric, time)
    }
    """
    data = {}
    with open(FILENAME.format(name, "threads"), "r") as file:
        lines = file.readlines()
        for line in lines:
            thread_id, _, max_metric, time = line.split(",")
            if int(thread_id) not in data.keys():
                data[int(thread_id)] = [(float(max_metric), float(time))]
            else:
                data[int(thread_id)].append((float(max_metric), float(time)))
    for thread_id, l in data.items():
        max_metric = max([x[0] for x in l])
        time = min([x[1] for x in l])
        data[thread_id] = (max_metric, time)
    return data

def generate_barplots(data, name):
    """
    Generates bar plots for multiple metrics and times per dataset.

    Parameters:
    - data: dict with structure {id: [(value_i, time_i), ...]}
    - name: base name for the output files

    Saves:
    - {name}_metric_bar.png
    - {name}_times_bar.png
    """
    if not data:
        print("No data to plot")
        return

    ids = list(data.keys())
    num_variants = len(next(iter(data.values())))

    x_labels = [DATA_NAMES.get(i, str(i)) for i in ids]
    x = np.arange(len(ids))
    width = 0.8 / num_variants  # Ajusta ancho según cantidad de variantes

    # --- Plot de métricas ---
    fig, ax = plt.subplots(figsize=(10, 6))
    for idx in range(num_variants):
        values = [data[i][idx][0] for i in ids]
        offset = (idx - (num_variants - 1) / 2) * width
        bars = ax.bar(x + offset, values, width, label=f'Métrica {idx + 1}')
        # Añadir etiquetas de valor encima de cada barra
        for bar, value in zip(bars, values):
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                bar.get_height(),
                f'{value:.2f}',
                ha='center',
                va='bottom',
                fontsize=8,
                rotation=0
            )
    ax.set_xlabel('Datasets')
    ax.set_ylabel('celdas x ns')
    ax.set_title('Comparación Métrica (celdas x ns)')
    ax.set_xticks(x)
    ax.set_xticklabels(x_labels, rotation=45)
    ax.legend()
    plt.tight_layout()
    plt.savefig(f"{DIR}{name}_perf_bar.png")
    print(f"Saved plot to {DIR}{name}_perf_bar.png")
    plt.close()

    # --- Plot de tiempos ---
    fig, ax = plt.subplots(figsize=(10, 6))
    for idx in range(num_variants):
        times = [data[i][idx][1] for i in ids]
        offset = (idx - (num_variants - 1) / 2) * width
        bars = ax.bar(x + offset, times, width, label=f'Tiempo {idx + 1}')
        # Añadir etiquetas de valor encima de cada barra
        for bar, value in zip(bars, times):
            # Notación científica si el valor es muy grande o muy pequeño
            if abs(value) > 1000 or (0 < abs(value) < 0.01):
                label = f'{value:.2e}'
            else:
                label = f'{value:.2f}'
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                bar.get_height(),
                label,
                ha='center',
                va='bottom',
                fontsize=8,
                rotation=0  # Horizontal
            )
    ax.set_yscale('log')
    ax.set_xlabel('Datasets')
    ax.set_ylabel('Tiempo (s)')
    ax.set_title('Comparación Tiempos')
    ax.set_xticks(x)
    ax.set_xticklabels(x_labels, rotation=45)
    ax.legend()
    plt.tight_layout()
    plt.savefig(f"{DIR}{name}_times_bar.png")
    print(f"Saved plot to {DIR}{name}_times_bar.png")
    plt.close()

def generate_barplots_by_threads(data, name):
    """
    Generates bar plots for metrics and times based on the number of threads.

    Parameters:
    - data: dict with structure {'thread_n': [(metric, time)]}
    - name: base name for the output files

    Saves:
    - {name}_metric_threads_bar.png
    - {name}_time_threads_bar.png
    """
    if not data:
        print("No data to plot")
        return

    # Extract thread IDs, metrics, and times
    sorted_data = sorted(data.items(), key=lambda x: int(x[0]))
    thread_ids = [int(thread_id) for thread_id, _ in sorted_data]
    metrics = [values[0] for _, values in sorted_data]
    times = [values[1] for _, values in sorted_data]

    x = np.arange(len(thread_ids))  # Positions for bars
    width = 0.4  # Width of the bars

    # --- Plot for metrics ---
    fig, ax = plt.subplots(figsize=(8, 5))
    bars = ax.bar(x, metrics, width, label='Métrica')
    ax.set_xlabel('Número de Threads')
    ax.set_ylabel('Métrica')
    ax.set_title('Métrica x Número de Threads')
    ax.set_xticks(x)
    ax.set_xticklabels(thread_ids)
    ax.legend()

    # Add value labels on top of bars
    for bar, value in zip(bars, metrics):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height(),
            f'{value:.2f}',
            ha='center',
            va='bottom',
            fontsize=8
        )

    plt.tight_layout()
    plt.savefig(f"{DIR}{name}_metric_threads_bar.png")
    print(f"Saved plot to {DIR}{name}_metric_threads_bar.png")
    plt.close()

    # --- Plot for times ---
    fig, ax = plt.subplots(figsize=(8, 5))
    bars = ax.bar(x, times, width, label='Tiempo')
    ax.set_xlabel('Número de Threads')
    ax.set_ylabel('Tiempo (s)')
    ax.set_title('Tiempo x Número de Threads')
    ax.set_xticks(x)
    ax.set_xticklabels(thread_ids)
    ax.legend()

    # Add value labels on top of bars
    for bar, value in zip(bars, times):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height(),
            f'{value:.2f}',
            ha='center',
            va='bottom',
            fontsize=8
        )

    plt.plot(color="orange")
    plt.tight_layout()
    plt.savefig(f"{DIR}{name}_time_threads_bar.png")
    print(f"Saved plot to {DIR}{name}_time_threads_bar.png")
    plt.close()

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 generate_plots.py burned_probabilities|fire_animation")
        return
    name = sys.argv[1]
    if name not in ["burned_probabilities", "fire_animation"]:
        print("Usage: python3 generate_plots.py burned_probabilities|fire_animation")
        return
    versions = sys.argv[2:]
    if not versions:
        print("Usage: python3 generate_plots.py burned_probabilities|fire_animation v1 v2 ...")
        return
    if "threads" in versions:
        data = read_perf_data_by_thread(name)
        generate_barplots_by_threads(data, name)
        return
    else:
        data = read_perf_data(name, versions)
        generate_barplots(data, name)

if __name__ == "__main__":
    main()