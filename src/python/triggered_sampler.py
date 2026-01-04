import numpy as np
import matplotlib.pyplot as plt

class TriggeredSampler:
    def __init__(self, window_size: int = 256, full_scale: float = 32767, full_scale_volt: float = 1.0):
        self.window_size = window_size
        self.full_scale = full_scale
        self.full_scale_volt = full_scale_volt
        self.frames: np.ndarray[np.ndarray] = None

    def sample(self, signal: np.ndarray, trigger: np.ndarray[bool]):
        n_samples_before = self.window_size // 2
        n_samples_after = self.window_size - n_samples_before
        trigger_idxs = np.where(trigger)[0]
        trigger_idxs = trigger_idxs[(trigger_idxs >= n_samples_before) & (trigger_idxs + n_samples_after <= len(signal))]
        sample_idxs = []

        for idx in trigger_idxs:
            if len(sample_idxs) == 0 or (idx - sample_idxs[-1] >= self.window_size and idx + self.window_size <= len(signal)):
                sample_idxs.append(idx)

        signal_to_volt = lambda x: (x.astype(np.float32) / np.float32(self.full_scale)) * self.full_scale_volt
        self.frames = np.stack([signal_to_volt(signal[idx - n_samples_before:idx + n_samples_after]) for idx in sample_idxs])
    
    def plot_sampled_signal(self, ax: plt.Axes, color="b") -> None:
        if self.frames is None:
            raise ValueError("No sampled frames to plot. Please call sample() first.")

        num_samples = self.frames.shape[0]
        time_axis = np.arange(self.window_size)
        zero_time = self.window_size // 2
        time_axis = time_axis - zero_time

        for i in range(num_samples):
            ax.plot(time_axis, self.frames[i], alpha=0.5, color=color)
        ax.set_xlabel('Sample Index')
        ax.set_ylabel('Signal Value')
        ax.set_title('Sampled Signal')