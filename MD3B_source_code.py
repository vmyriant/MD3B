# BBB permeability simulation program
# This program simulates blood-brain barrier (BBB) permeability for various compounds using umbrella sampling data.
# Authors: Emmanuel Orfanakis and Vassilios Myrianthopoulos - National and Kapodistrian University of Athens, Department of Pharmacy, Panepistimiopolis Zografou, Greece.
# Version: 1.0
# Distributed under MIT License.
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from statsmodels.tsa.stattools import acovf
from scipy.stats import linregress
from scipy.interpolate import interp1d
from scipy.integrate import simpson
from colorama import Fore, Style, init as colorama_init
colorama_init()
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, ttk
from PIL import Image
import glob
import os
import sys
import argparse
import subprocess
import queue
import threading

if sys.platform == 'win32':
    try:
        import ctypes
        import struct as _struct
        from ctypes import wintypes as _wintypes

        _user32 = ctypes.windll.user32
        _gdi32 = ctypes.windll.gdi32
        _kernel32 = ctypes.windll.kernel32
        _dwmapi = ctypes.windll.dwmapi

        _GWLP_WNDPROC = -4
        _GCLP_HBRBACKGROUND = -10
        _GCL_STYLE = -26
        _CS_VREDRAW = 0x0001
        _CS_HREDRAW = 0x0002
        _MEM_COMMIT_RESERVE = 0x3000
        _PAGE_EXECUTE_READWRITE = 0x40

        _user32.SetWindowLongPtrW.argtypes = [_wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
        _user32.SetWindowLongPtrW.restype = ctypes.c_void_p
        _user32.GetWindowLongPtrW.argtypes = [_wintypes.HWND, ctypes.c_int]
        _user32.GetWindowLongPtrW.restype = ctypes.c_void_p
        _user32.GetClassLongPtrW.argtypes = [_wintypes.HWND, ctypes.c_int]
        _user32.GetClassLongPtrW.restype = ctypes.c_void_p
        _user32.SetClassLongPtrW.argtypes = [_wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
        _user32.SetClassLongPtrW.restype = ctypes.c_void_p
        _gdi32.CreateSolidBrush.argtypes = [_wintypes.COLORREF]
        _gdi32.CreateSolidBrush.restype = ctypes.c_void_p
        _kernel32.VirtualAlloc.argtypes = [ctypes.c_void_p, ctypes.c_size_t, _wintypes.DWORD, _wintypes.DWORD]
        _kernel32.VirtualAlloc.restype = ctypes.c_void_p
        _kernel32.GetModuleHandleW.argtypes = [_wintypes.LPCWSTR]
        _kernel32.GetModuleHandleW.restype = ctypes.c_void_p
        _kernel32.GetProcAddress.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
        _kernel32.GetProcAddress.restype = ctypes.c_void_p

        _win32_brush_cache = {}
        _win32_top_stubs = {}
        _win32_child_stubs = {}
        _h_user32 = _kernel32.GetModuleHandleW('user32.dll')
        _def_wnd_proc = _kernel32.GetProcAddress(_h_user32, b'DefWindowProcW') if _h_user32 else None
        _is_x64 = (ctypes.sizeof(ctypes.c_void_p) == 8)

        def _get_top_stub(orig_proc):
            stub = _win32_top_stubs.get(orig_proc)
            if stub is not None:
                return stub
            call_orig = b'\x48\xb8' + _struct.pack('<Q', orig_proc) + b'\xff\xe0'
            call_def  = b'\x48\xb8' + _struct.pack('<Q', _def_wnd_proc) + b'\xff\xe0'
            b_check3 = b'\x83\xfa\x03\x75\x09\x41\x81\xf9\x00\x83\x00\x83\x74' + bytes([len(call_orig)])
            b_check2 = b'\x83\xfa\x05\x75\x06\x41\x83\xf8\x01\x74' + bytes([len(b_check3) + len(call_orig)])
            b_check1 = b'\x83\xfa\x47\x75\x0a\x41\x81\x79\x10\x00\x83\xff\xff\x74' + bytes([len(b_check2) + len(b_check3) + len(call_orig)])
            full = b_check1 + b_check2 + b_check3 + call_orig + call_def
            buf = _kernel32.VirtualAlloc(None, len(full), _MEM_COMMIT_RESERVE, _PAGE_EXECUTE_READWRITE)
            if buf:
                ctypes.memmove(buf, full, len(full))
                _win32_top_stubs[orig_proc] = buf
            return buf

        def _get_child_stub(orig_proc):
            stub = _win32_child_stubs.get(orig_proc)
            if stub is not None:
                return stub
            call_orig = b'\x48\xb8' + _struct.pack('<Q', orig_proc) + b'\xff\xe0'
            call_def  = b'\x48\xb8' + _struct.pack('<Q', _def_wnd_proc) + b'\xff\xe0'
            full = b'\x83\xfa\x14\x74' + bytes([len(call_orig)]) + call_orig + call_def
            buf = _kernel32.VirtualAlloc(None, len(full), _MEM_COMMIT_RESERVE, _PAGE_EXECUTE_READWRITE)
            if buf:
                ctypes.memmove(buf, full, len(full))
                _win32_child_stubs[orig_proc] = buf
            return buf

        def _set_win32_class_bg(widget, bg_hex='#fafafa'):
            """Configure native Win32 fast background erase and prevent 0x0 unmap cascade on minimize."""
            try:
                h_hex = bg_hex.lstrip('#')
                if len(h_hex) == 6:
                    r, g, b = int(h_hex[0:2], 16), int(h_hex[2:4], 16), int(h_hex[4:6], 16)
                    cref = (b << 16) | (g << 8) | r
                    brush = _win32_brush_cache.get(cref)
                    if not brush:
                        brush = _gdi32.CreateSolidBrush(cref)
                        _win32_brush_cache[cref] = brush
                else:
                    brush = None

                hwnd = widget.winfo_id()
                if not hwnd:
                    return
                if brush:
                    _user32.SetClassLongPtrW(hwnd, _GCLP_HBRBACKGROUND, brush)
                c_style = _user32.GetClassLongPtrW(hwnd, _GCL_STYLE)
                if c_style & (_CS_HREDRAW | _CS_VREDRAW):
                    _user32.SetClassLongPtrW(hwnd, _GCL_STYLE, c_style & ~(_CS_HREDRAW | _CS_VREDRAW))

                if _is_x64 and _def_wnd_proc:
                    cur_proc = _user32.GetWindowLongPtrW(hwnd, _GWLP_WNDPROC)
                    if cur_proc and cur_proc not in _win32_child_stubs.values():
                        c_stub = _get_child_stub(cur_proc)
                        if c_stub:
                            _user32.SetWindowLongPtrW(hwnd, _GWLP_WNDPROC, c_stub)

                if isinstance(widget, (tk.Tk, tk.Toplevel)):
                    parent_hwnd = _user32.GetParent(hwnd)
                    if parent_hwnd:
                        if brush:
                            _user32.SetClassLongPtrW(parent_hwnd, _GCLP_HBRBACKGROUND, brush)
                        t_style = _user32.GetClassLongPtrW(parent_hwnd, _GCL_STYLE)
                        if t_style & (_CS_HREDRAW | _CS_VREDRAW):
                            _user32.SetClassLongPtrW(parent_hwnd, _GCL_STYLE, t_style & ~(_CS_HREDRAW | _CS_VREDRAW))
                        val = ctypes.c_int(1)
                        _dwmapi.DwmSetWindowAttribute(parent_hwnd, 3, ctypes.byref(val), 4)
                        if _is_x64 and _def_wnd_proc:
                            top_proc = _user32.GetWindowLongPtrW(parent_hwnd, _GWLP_WNDPROC)
                            if top_proc and top_proc not in _win32_top_stubs.values():
                                t_stub = _get_top_stub(top_proc)
                                if t_stub:
                                    _user32.SetWindowLongPtrW(parent_hwnd, _GWLP_WNDPROC, t_stub)
            except Exception:
                pass
    except Exception:
        def _set_win32_class_bg(widget, bg_hex='#fafafa'):
            pass
else:
    def _set_win32_class_bg(widget, bg_hex='#fafafa'):
        pass

# --- Introduction ---

# Clear the Terminal
# 'cls' is for Windows, 'clear' is for macOS/Linux
os.system('cls' if os.name == 'nt' else 'clear')
print(f"{Fore.RED}---------------------------------------------------------------{Style.RESET_ALL}")
print(f"{Fore.RED}BBB PERMEABILITY CALCULATION FROM UMBRELLA SAMPLING SIMULATIONS{Style.RESET_ALL}")
print(f"{Fore.RED}             DERIVED BY GROMACS - Version 1.0                  {Style.RESET_ALL}")
print(f"{Fore.RED}---------------------------------------------------------------{Style.RESET_ALL}")
print()
# --- Constants ---
# Boltzmann constant in GROMACS units: kJ/(mol*K)
KB = 0.0083144621 # kJ/(mol*K)
LOGBB_INTERCEPT_DEFAULT = 0.1725
LOGBB_SLOPE_DEFAULT = 2.808

# File and simulation parameters
# Command-line flag: --smoke-test to run a quick check using existing umbrella files
parser = argparse.ArgumentParser(add_help=False)
parser.add_argument('--smoke-test', action='store_true', help='Run a quick smoke test using existing umbrella files')
args, _ = parser.parse_known_args()

# --- Helper Functions ---
def calculate_tau_least_squares(z_data, dt, max_lag=500):
    # Use very high sampling frequency initially by computing ACF with fine time resolution
    # Dynamically increase ACF resolution based on data length for better precision
    effective_max_lag = min(max_lag, max(1000, int(0.5 * len(z_data))))
    acov = acovf(z_data, nlag=effective_max_lag, fft=True)
    lags = np.arange(len(acov)) * dt
    noise_floor_std = np.std(acov[-100:])
    valid_indices = np.where(acov <= noise_floor_std)[0]
    cutoff = valid_indices[0] if len(valid_indices) > 0 else len(acov)
    fit_mask = acov[:cutoff] > 0
    x_fit = lags[:cutoff][fit_mask]
    y_fit = np.log(acov[:cutoff][fit_mask])
    if len(x_fit) > 1:
        slope, _, r_val, _, _ = linregress(x_fit, y_fit)
        tau = -1 / slope
        return tau, r_val**2
    return None, None

def recommend_interval_size(z_values, dt, target_mult=20, min_blocks=10, min_points=500, max_lag=1000):
    """Estimate a reasonable interval size (in points) based on an approximate tZ."""
    if z_values is None or len(z_values) < 2:
        return None, None
    safe_max_lag = min(max_lag, len(z_values) - 1)
    tau, _ = calculate_tau_least_squares(z_values, dt, max_lag=safe_max_lag)
    if not tau or tau <= 0:
        return None, None
    interval_points = int(round((target_mult * tau) / dt))
    max_interval = max(1, len(z_values) // max(1, min_blocks))
    interval_points = min(interval_points, max_interval)
    interval_points = max(interval_points, min_points)
    return interval_points, tau

def optimize_interval_size(files, dt=0.1, logger=print, mode='fast'):
    """
    Automatically determine optimal interval size by analyzing multiple trajectory files.
    
    Strategy:
    1. Sample files to capture the full correlation-time distribution.
    2. Build a wide range of candidate intervals (100 → 15 000 points).
    3. Score each candidate by block-level tau estimation quality AND
       the number of blocks it produces — more blocks strongly preferred
       because block-averaging smooths noisy D(z) estimates.
    4. Return the highest-scoring candidate.
    
    mode: 'fast' (fewer samples, quicker) or 'thorough' (more samples, slower but more reliable)
    Returns: (optimal_interval_points, diagnostic_info)
    """
    if not files:
        return None, None
    
    # Mode-dependent parameters
    if mode == 'thorough':
        file_sample_limit = 50
        quality_limit = 15
        blocks_to_check = 8
        scoring_max_lag = 1000
    else:  # fast
        file_sample_limit = 20
        quality_limit = 8
        blocks_to_check = 4
        scoring_max_lag = 500
    
    logger(f"--- Auto-optimizing interval size ({mode} mode) ---", tag='blue')
    
    tau_estimates = []
    trajectory_lengths = []
    sampled_trajectories = []
    
    # Sample files to capture full correlation time distribution
    sample_size = min(len(files), file_sample_limit)
    
    if len(files) <= sample_size:
        sample_files = files
    else:
        step = len(files) / sample_size
        sample_files = [files[int(i * step)] for i in range(sample_size)]
    
    logger(f"Analyzing {len(sample_files)} trajectory files...", tag='blue')
    
    for file_path in sample_files:
        try:
            df = pd.read_csv(file_path, sep=r'\s+', comment='@', header=None,
                           usecols=[0, 1], on_bad_lines='skip', encoding='latin1', engine='python')
            df.columns = ['Time', 'z (nm)']
            z_vals = pd.to_numeric(df['z (nm)'], errors='coerce').dropna().values
            
            if len(z_vals) < 1000:
                continue
                
            trajectory_lengths.append(len(z_vals))
            sampled_trajectories.append(z_vals)
            
            safe_max_lag = min(1000, len(z_vals) - 1)
            tau, r_sq = calculate_tau_least_squares(z_vals, dt, max_lag=safe_max_lag)
            
            if tau and tau > 0 and r_sq and r_sq > 0.7:
                tau_estimates.append(tau)
                
        except Exception:
            continue
    
    if not tau_estimates or not trajectory_lengths or not sampled_trajectories:
        logger("Could not auto-optimize interval. Using default 5000 points.", tag='orange')
        return 5000, {'status': 'failed', 'reason': 'insufficient_data'}
    
    # Tau statistics for candidate generation and reporting
    percentile_50_tau = np.percentile(tau_estimates, 50)
    percentile_75_tau = np.percentile(tau_estimates, 75)
    percentile_90_tau = np.percentile(tau_estimates, 90)
    median_tau = np.median(tau_estimates)
    max_tau = max(tau_estimates)
    mean_tau = np.mean(tau_estimates)
    min_length = min(trajectory_lengths)
    
    # ----- Candidate generation -----
    min_interval = 100
    max_interval = 15000
    min_blocks_required = 15
    max_interval_by_length = max(1, min_length // min_blocks_required)

    def clamp_interval(value):
        value = int(round(value))
        value = min(value, max_interval_by_length)
        value = min(value, max_interval)
        value = max(value, min_interval)
        return value

    candidate_intervals = set()

    # Fixed small candidates that empirically work well
    for fixed in [100, 250, 500, 1000, 2000, 3000, 5000, 7500, 10000]:
        candidate_intervals.add(clamp_interval(fixed))

    # Tau-derived candidates (conservative multipliers: 5× – 20×)
    for tau_ref in [percentile_50_tau, percentile_75_tau, percentile_90_tau]:
        for mult in [5, 8, 10, 15, 20]:
            candidate_intervals.add(clamp_interval(round((mult * tau_ref) / dt)))

    candidate_intervals = sorted(candidate_intervals)

    # ----- Trajectory subsample for scoring -----
    quality_sample_size = min(len(sampled_trajectories), quality_limit)
    if len(sampled_trajectories) <= quality_sample_size:
        quality_trajectories = sampled_trajectories
    else:
        step_q = len(sampled_trajectories) / quality_sample_size
        quality_trajectories = [sampled_trajectories[int(i * step_q)] for i in range(quality_sample_size)]

    # ----- Scoring function -----
    def score_candidate(interval_points, trajectories):
        total_blocks = 0
        valid_blocks = 0
        good_fit_blocks = 0
        blocks_per_traj = []

        for z_vals in trajectories:
            n_blocks = len(z_vals) // interval_points
            blocks_per_traj.append(n_blocks)
            if n_blocks <= 0:
                continue

            max_blocks_to_check = min(n_blocks, blocks_to_check)
            if max_blocks_to_check == 1:
                starts = [0]
            else:
                max_start = len(z_vals) - interval_points
                stride = max(1, max_start // (max_blocks_to_check - 1))
                starts = [idx * stride for idx in range(max_blocks_to_check)]

            for start in starts:
                segment = z_vals[start:start + interval_points]
                if len(segment) < interval_points:
                    continue
                total_blocks += 1
                safe_max_lag = min(scoring_max_lag, len(segment) - 1)
                tau_val, r_sq_val = calculate_tau_least_squares(segment, dt, max_lag=safe_max_lag)
                if tau_val and tau_val > 0:
                    valid_blocks += 1
                    if r_sq_val and r_sq_val >= 0.8:
                        good_fit_blocks += 1

        if total_blocks == 0:
            return -1e9, {
                'interval': interval_points,
                'valid_fraction': 0.0,
                'good_fit_fraction': 0.0,
                'median_blocks': 0,
                'score': -1e9
            }

        valid_fraction = valid_blocks / total_blocks
        good_fit_fraction = (good_fit_blocks / valid_blocks) if valid_blocks > 0 else 0.0
        median_blocks = int(np.median(blocks_per_traj)) if blocks_per_traj else 0

        # Block-count bonus (logarithmic, saturates at ~250 blocks)
        block_bonus = 0.0
        if median_blocks >= 2:
            block_bonus = 0.06 * np.log2(median_blocks)

        # Penalty for too few blocks (steep)
        block_penalty = 0.0
        if median_blocks < 20:
            block_penalty += (20 - median_blocks) * 0.025
        if median_blocks < 5:
            block_penalty += 0.30

        # Disqualify candidates where most blocks can't estimate tau
        validity_penalty = 0.0
        if valid_fraction < 0.5:
            validity_penalty = 0.40

        score = (
            0.30 * valid_fraction
            + 0.15 * good_fit_fraction
            + block_bonus
            - block_penalty
            - validity_penalty
        )

        return score, {
            'interval': interval_points,
            'valid_fraction': valid_fraction,
            'good_fit_fraction': good_fit_fraction,
            'median_blocks': median_blocks,
            'score': score
        }

    # ----- Evaluate all candidates -----
    candidate_diagnostics = []
    for candidate in candidate_intervals:
        _score, diag = score_candidate(candidate, quality_trajectories)
        candidate_diagnostics.append(diag)

    best_candidate = max(candidate_diagnostics, key=lambda x: x['score'])
    optimal_interval = int(best_candidate['interval'])

    # Boundary warnings
    if optimal_interval == max_interval_by_length:
        logger(f"Interval adjusted to {optimal_interval} to ensure ≥{min_blocks_required} blocks/window", tag='orange')
    if optimal_interval == max_interval:
        logger(f"Interval capped at {max_interval} points (upper safety limit)", tag='orange')
    if optimal_interval == min_interval:
        logger(f"Interval raised to {min_interval} points (lower safety limit)", tag='orange')
    
    # Tau variability warning
    tau_std = np.std(tau_estimates)
    tau_cv = tau_std / mean_tau if mean_tau > 0 else 0
    
    diagnostic = {
        'status': 'success',
        'median_tau_ps': median_tau,
        'percentile_50_tau_ps': percentile_50_tau,
        'percentile_75_tau_ps': percentile_75_tau,
        'percentile_90_tau_ps': percentile_90_tau,
        'max_tau_ps': max_tau,
        'mean_tau_ps': mean_tau,
        'tau_std_ps': tau_std,
        'tau_cv': tau_cv,
        'tau_range': (min(tau_estimates), max(tau_estimates)),
        'trajectory_lengths': trajectory_lengths,
        'optimal_interval': optimal_interval,
        'blocks_per_window': min_length // optimal_interval,
        'samples_analyzed': len(tau_estimates),
        'method': 'candidate_scoring_v2',
        'candidates_tested': candidate_diagnostics,
        'best_candidate': best_candidate
    }
    
    logger(f"Analyzed {len(tau_estimates)} files:", tag='blue')
    logger(f"  Correlation time (tZ): median={median_tau:.2f} ps, p75={percentile_75_tau:.2f} ps, p90={percentile_90_tau:.2f} ps, max={max_tau:.2f} ps", tag='blue')
    
    if tau_cv > 0.5:
        logger(f"  Warning: High tau variability (CV={tau_cv:.2f}). Some windows may have convergence issues.", tag='orange')
        logger(f"  Consider longer simulations if results are unreliable.", tag='orange')
    
    logger(f"  Trajectory length: {min_length} - {max(trajectory_lengths)} points", tag='blue')
    logger(f"  Candidates tested: {len(candidate_diagnostics)} intervals from {candidate_intervals[0]} to {candidate_intervals[-1]} points", tag='blue')
    logger(f"  Best interval score: {best_candidate['score']:.3f} (valid={best_candidate['valid_fraction']:.2f}, good-fit={best_candidate['good_fit_fraction']:.2f}, median_blocks={best_candidate['median_blocks']})", tag='blue')
    logger(f"  Optimal interval: {optimal_interval} points (~{optimal_interval * dt:.1f} ps) [candidate-scoring v2]", tag='green', bold=True)
    logger(f"  Expected blocks/window: {min_length // optimal_interval}", tag='blue')
    logger("", tag='blue')
    
    return optimal_interval, diagnostic

def run_simulation(folder, T, pmf_path=None, pmf_neutral_path=None, pKa=None, is_acid=True, is_base=False, monitor=True, logger=print, stop_event=None, max_files=None, ionized_folder=None, neutral_folder=None, regression_intercept=LOGBB_INTERCEPT_DEFAULT, regression_slope=LOGBB_SLOPE_DEFAULT, interval_size_points=5000, optimize_mode='fast'):
    """Run the BBB diffusion/PMF processing and return results and matplotlib Figures.
    logger(msg) will be called for progress updates. stop_event is a threading.Event that may be set to request early termination.
    max_files limits the number of umbrella files processed (useful for smoke-tests).
    pmf_path: PMF for ion species (when acid/base) or neutral species (when neither)
    pmf_neutral_path: PMF for neutral species (required only when pKa correction is applied)
    is_acid: True if compound is an acid (for Henderson-Hasselbalch)
    is_base: True if compound is a base (for Henderson-Hasselbalch)
    ionized_folder: Path to ionized subfolder (if applicable)
    neutral_folder: Path to neutral subfolder (if applicable)
    """
    logger(f"\n============================================================================", tag='cyan', bold=True)
    logger(f"--- Starting BBB permeability calculation with neutralization correction ---", tag='cyan', bold=True)
    logger(f"============================================================================\n", tag='cyan', bold=True)
    logger("")
    compound_display = os.path.basename(folder.rstrip(os.sep)) or folder
    logger(f"Starting simulation for {compound_display} in:", tag='blue')
    logger(f"  Folder: {folder}", tag='orange')
    logger("")
    logger(f"Simulation temperature: {T} K", tag='blue', bold=True)
    logger("")
    if pKa is not None and pmf_path is None:
        logger("PMF file is required for acid/base correction when pKa is provided.")
        return None
    
    common_expression = 'umbrella'
    files = []
    if ionized_folder and os.path.isdir(ionized_folder):
        try:
            all_entries = os.listdir(ionized_folder)
            # Only process umbrella sampling trajectory files (e.g., *pullx.xvg); skip PMF .xvg
            files = [
                os.path.join(ionized_folder, f)
                for f in all_entries
                if f.lower().endswith('.xvg') and ('pullx' in f.lower() or 'umbrella' in f.lower())
            ]
            logger(f"Looking for pullx/umbrella .xvg files in ionized folder:", tag='blue') 
            logger(f"{ionized_folder}", tag='orange')
            logger("")
        except Exception as e:
            logger(f"Error listing ionized folder '{ionized_folder}': {e}", tag='red')
            return None
    elif neutral_folder and os.path.isdir(neutral_folder):
        try:
            all_entries = os.listdir(neutral_folder)
            # Only process umbrella sampling trajectory files (e.g., *pullx.xvg); skip PMF .xvg
            files = [
                os.path.join(neutral_folder, f)
                for f in all_entries
                if f.lower().endswith('.xvg') and ('pullx' in f.lower() or 'umbrella' in f.lower())
            ]
            logger(f"Looking for pullx/umbrella .xvg files in neutral folder:", tag='blue') 
            logger(f"{neutral_folder}", tag='orange')
        except Exception as e:
            logger(f"Error listing neutral folder '{neutral_folder}': {e}", tag='red')
            return None
    else:
        try:
            all_entries = os.listdir(folder)
            files = [os.path.join(folder, f) for f in all_entries if f.endswith('.xvg') and common_expression in f]
            logger(f"Looking for umbrella .xvg files in main folder:", tag='blue') 
            logger(f"{folder}", tag='orange')
        except Exception as e:
            logger(f"Error listing folder '{folder}': {e}", tag='red')
            return None
    if max_files:
        files = files[:max_files]
    if not files:
        logger("No umbrella .xvg files found in the selected folder.", tag='blue')
        return None

    all_files_summary = []
    time_step_of_simulation = 0.1
    file_tau_estimates = []
    max_simulation_time_ps = 0
    
    # Auto-optimize interval size if requested (interval_size_points == 0 means "auto")
    use_optimized_interval = (interval_size_points == 0)
    if use_optimized_interval:
        logger("")
        optimized_interval, _ = optimize_interval_size(files, time_step_of_simulation, logger, mode=optimize_mode)
        if optimized_interval:
            interval_size_points = optimized_interval
            logger(f"Using auto-optimized interval: {interval_size_points} points", tag='green', bold=True)
        else:
            interval_size_points = 5000
            logger(f"Auto-optimization failed. Using default: {interval_size_points} points", tag='orange')
        logger("")
    else:
        # User manually specified interval - validate and warn if needed
        logger(f"Using user-specified interval: {interval_size_points} points (~{interval_size_points * time_step_of_simulation:.1f} ps)", tag='blue')
        logger("")
    
    # Get total simulation time from first file
    if files:
        try:
            first_file_path = files[0]
            df_first = pd.read_csv(first_file_path, sep=r'\s+', comment='@', header=None,
                                   usecols=[0, 1], on_bad_lines='skip', encoding='latin1', engine='python')
            df_first.columns = ['Time', 'z (nm)']
            if not df_first.empty and 'Time' in df_first.columns:
                max_simulation_time_ps = float(df_first['Time'].iloc[-1])
                logger(f"Timestep: {time_step_of_simulation} ps, Total MD time: {max_simulation_time_ps / 1000:.2f} ns", tag='blue', bold=True)
                logger("")
        except Exception as e:
            logger(f"Could not read simulation time from first file: {e}", tag='blue')

    for file_name in files:
        if stop_event and stop_event.is_set():
            logger('Stop requested. Exiting loop.', tag='blue')
            return None
        full_path = file_name
        base_name = os.path.basename(file_name)
        if ionized_folder and os.path.isdir(ionized_folder):
            logger(f"Processing: {full_path}")
        else:
            logger(f"Processing: {base_name}")
        try:
            df_xvg = pd.read_csv(full_path, sep=r'\s+', comment='@', header=None,
                                 usecols=[0, 1], on_bad_lines='skip', encoding='latin1', engine='python')
            df_xvg.columns = ['Time', 'z (nm)']
            df_xvg['z (nm)'] = pd.to_numeric(df_xvg['z (nm)'], errors='coerce')
            df_xvg = df_xvg.dropna(subset=['z (nm)'])
            z_values = df_xvg['z (nm)'].values

            interval_size = interval_size_points
            file_D_estimates = []
            file_tau_estimates_local = []
            for i in range(0, len(z_values), interval_size):
                if stop_event and stop_event.is_set():
                    logger('Stop requested during file processing.')
                    return None
                segment = z_values[i: i + interval_size]
                if len(segment) == interval_size:
                    safe_max_lag = min(1000, len(segment) - 1)
                    tau, r_sq = calculate_tau_least_squares(segment, time_step_of_simulation, max_lag=safe_max_lag)
                    if tau and tau > 0:
                        var_seg = np.var(segment, ddof=1)
                        d_seg = var_seg / tau
                        file_D_estimates.append(d_seg)
                        file_tau_estimates_local.append(tau)
            if file_D_estimates:
                final_D = np.mean(file_D_estimates)
                final_tau = np.mean(file_tau_estimates_local)
                avg_Z_pos = np.mean(z_values)
                std_err_D = np.std(file_D_estimates) / np.sqrt(len(file_D_estimates))
                all_files_summary.append({
                    'File': file_name,
                    'Z_pos_nm': round(avg_Z_pos, 4),
                    'D_nm2_ps': final_D,
                    'tau_ps': round(final_tau, 4),
                    'Estimates': len(file_D_estimates),
                    'Std_Error': std_err_D,
                    'R2': round(r_sq, 4) if 'r_sq' in locals() else None
                })
                file_tau_estimates.extend(file_tau_estimates_local)
                # Get the last time value from the Time column
                if not df_xvg.empty and 'Time' in df_xvg.columns:
                    last_time_ps = float(df_xvg['Time'].iloc[-1])
                    max_simulation_time_ps = max(max_simulation_time_ps, last_time_ps)
                logger(f"processing, {base_name}, success, average D {final_D:.4e} (from {len(file_D_estimates)} sample)", tag='green')
            else:
                logger(f"  > No valid estimates for {base_name}")
        except Exception as e:
            logger(f"  > Error processing {base_name}: {e}")

    if not all_files_summary:
        logger('No data processed successfully. Aborting.')
        return None

    summary_df = pd.DataFrame(all_files_summary).sort_values(by='Z_pos_nm')

    figs = []
    graph_names = []

    # Create D(z) figure for the currently processed species (ionized or dominant)
    is_dual_form = bool(is_acid or is_base)
    fig1 = Figure(figsize=(3.5, 2.5))
    ax1 = fig1.add_subplot(111)
    try:
        summary_df['D_float'] = summary_df['D_nm2_ps'].astype(float)
        ax1.errorbar(summary_df['Z_pos_nm'], summary_df['D_float'], yerr=summary_df['Std_Error'], fmt='-o', color='#5AA2E2', ecolor='#5AA2E2', capsize=3, linewidth=2)
        if is_dual_form:
            ax1.set_title('Local diffusion coefficient of ionized form', fontsize=9)
        else:
            ax1.set_title('Local diffusion coefficient D(Z) profile', fontsize=9)
        ax1.set_xlabel('Z-position (nm)', fontsize=8)
        ax1.set_ylabel('D (nm^2/ps)', fontsize=8)
        ax1.tick_params(labelsize=7)
        ax1.grid(True, which='both', ls='-', alpha=0.5)
        fig1.tight_layout(pad=0.5)
    except Exception as e:
        logger(f"Plotting D(z) failed: {e}")
    figs.append(fig1)
    graph_names.append('Ionized_D_profile')

    # Handle PMF
    if not pmf_path:
        search_pattern = os.path.join(folder, f"PMF_*.xvg")
        found = glob.glob(search_pattern)
        pmf_path = found[0] if found else None
        if pmf_path:
            logger(f"Found PMF: {pmf_path}")
        else:
            logger('No PMF found in folder. Skipping PMF-related steps.')

    pmf_df = None
    fig2 = None
    neutral_plot_df = None
    if pmf_path:
        try:
            pmf_df_local = pd.read_csv(pmf_path, sep=r'\s+', comment='@', header=None, usecols=[0, 1], encoding='latin1', engine='python')
            pmf_df_local.columns = ['Z_pos', 'G_kcal_mol']
            pmf_df_local['Z_pos'] = pd.to_numeric(pmf_df_local['Z_pos'], errors='coerce')
            pmf_df_local['G_kJ_mol'] = pd.to_numeric(pmf_df_local['G_kcal_mol'], errors='coerce') * 4.184
            pmf_df_local = pmf_df_local.dropna()
            bulk_data = pmf_df_local.loc[pmf_df_local['Z_pos'] >= 3.5, 'G_kJ_mol']
            if not bulk_data.empty:
                bulk_reference = bulk_data.mean()
                pmf_df_local['G_kJ_mol'] = pmf_df_local['G_kJ_mol'] - bulk_reference
                logger(f"PMF normalized to bulk (Z>=3.5). Reference: {bulk_reference:.2f} kJ/mol", tag='red')

            pmf_interp = interp1d(pmf_df_local['Z_pos'], pmf_df_local['G_kJ_mol'], kind='cubic', fill_value='extrapolate')
            summary_df['G_kJ_mol'] = pmf_interp(summary_df['Z_pos_nm'])

            fig2 = Figure(figsize=(3.5,2.5))
            ax2 = fig2.add_subplot(111)
            ax2.plot(pmf_df_local['Z_pos'], pmf_df_local['G_kJ_mol'], label='PMF Profile', linestyle='-', color='#5AA2E2', linewidth=2)
            if is_dual_form:
                ax2.set_title('Potential of mean force of ionized form', fontsize=9)
            else:
                ax2.set_title('Potential of mean force (PMF)', fontsize=9)
            ax2.set_xlabel('Z-position (nm)', fontsize=8)
            ax2.set_ylabel('Free Energy G (kJ/mol)', fontsize=8)
            ax2.tick_params(labelsize=7)
            ax2.axhline(y=0, color='red', linestyle=':', linewidth=1.2)
            ax2.grid(True, linestyle='--', alpha=0.7)
            fig2.tight_layout(pad=0.5)

            pmf_df = pmf_df_local
        except Exception as e:
            logger(f"Failed to process PMF: {e}")
    if fig2 is not None:
        figs.append(fig2)
        graph_names.append('Ionized_PMF')

    # Compute Resistivity and Peff if PMF available
    peff = None
    log_bb = None
    log_bb_corrected = None
    try:
        if 'G_kJ_mol' in summary_df.columns:
            KBT = KB * T
            summary_df['Resistivity'] = np.exp(summary_df['G_kJ_mol'] / KBT) / summary_df['D_nm2_ps'].astype(float)
            
            # Calculate and display simulation summary statistics
            if file_tau_estimates:
                tZ_local_mean = np.mean(file_tau_estimates)
                tZ_error = np.std(file_tau_estimates) / np.sqrt(len(file_tau_estimates))
                logger(f"\n--- SIMULATION SUMMARY (for dominant species of {compound_display})---", tag='blue', bold=True)
                logger(f"Global Correlation Time (tZ): {tZ_local_mean:.4f} ± {tZ_error:.4f} ps", tag='red')
                logger(f"(In research standards, it is recommended to ensure your total simulation length is at least 10 to 50 times tZ for the result to be statistically significant.)", tag='blue')
                logger(f"\n--- Windows with FASTEST diffusion (Shortest tZ, should be in water) ---", tag='red')
                fastest_windows = summary_df.sort_values(by='tau_ps').head(5)[['Z_pos_nm', 'tau_ps', 'R2']]
                for _, row in fastest_windows.iterrows():
                    logger(f"  Z={row['Z_pos_nm']:.2f} nm, tau={row['tau_ps']:.2f} ps, R2={row['R2']:.2f}", tag='blue')
                logger(f"\n--- Windows with SLOWEST diffusion (Longest tZ, should be in membrane) ---", tag='red')
                slowest_windows = summary_df.sort_values(by='tau_ps', ascending=False).head(5)[['Z_pos_nm', 'tau_ps', 'R2']]
                for _, row in slowest_windows.iterrows():
                    logger(f"  Z={row['Z_pos_nm']:.2f} nm, tau={row['tau_ps']:.2f} ps, R2={row['R2']:.2f}", tag='blue')
                logger(f"\nSimulation time step: {time_step_of_simulation} ps", tag='blue')
                logger(f"Interval size used: {interval_size_points} points (~{interval_size_points * time_step_of_simulation:.1f} ps)", tag='blue')
                logger(f"Total simulation time: {max_simulation_time_ps / 1000:.2f} ns\n", tag='blue')
            
            total_resistance = simpson(summary_df['Resistivity'], summary_df['Z_pos_nm'])
            peff = 1 / total_resistance
            peff_cm_s = peff * 1e-7 * 1e12
            peff_valid = True
            if not np.isfinite(peff_cm_s) or peff_cm_s <= 0:
                logger(f"Permeability (Peff): {peff:.2e} nm/ps ({peff_cm_s:.2e} cm/s)", tag='red')
                logger(f"Total Resistance: {total_resistance:.2e}", tag='red')
                logger("")
                if not np.isfinite(peff_cm_s):
                    logger('Invalid Peff detected (non-finite). Check PMF and D(z) inputs.', tag='red')
                elif peff_cm_s < 0:
                    logger('Warning: Peff is negative. This indicates problematic PMF normalization or D(z) values.', tag='red')
                else:
                    logger('Invalid Peff detected (<=0). Check PMF and D(z) inputs.', tag='red')
                logger("")
                logger("--- Diagnostic Information ---", tag='blue')
                # Interval size diagnostics
                logger(f"Interval size used: {interval_size_points} points (~{interval_size_points * time_step_of_simulation:.1f} ps)", tag='blue')
                if 'Estimates' in summary_df.columns:
                    avg_estimates = summary_df['Estimates'].mean()
                    min_estimates = summary_df['Estimates'].min()
                    logger(f"Blocks per window: average={avg_estimates:.1f}, minimum={min_estimates}", tag='blue')
                    if interval_size_points > 15000:
                        logger(f"Warning: Interval size is very large (>{interval_size_points}). This may cause unreliable statistics.", tag='red')
                        logger("Recommendation: Try a smaller interval size (e.g., 500-5000 points) for better convergence.", tag='red')
                    if min_estimates < 5:
                        logger(f"Warning: Some windows have very few estimates (<5 blocks). Results may be unreliable.", tag='red')
                logger("")
                # PMF statistics
                g_bulk = summary_df.loc[summary_df['Z_pos_nm'] >= 3.5, 'G_kJ_mol']
                if not g_bulk.empty:
                    logger(f"PMF in bulk region (Z>=3.5): mean={g_bulk.mean():.2f}, std={g_bulk.std():.2f} kJ/mol", tag='blue')
                logger(f"PMF range: min={summary_df['G_kJ_mol'].min():.2f}, max={summary_df['G_kJ_mol'].max():.2f} kJ/mol", tag='blue')
                # D(z) statistics
                logger(f"D(z) range: min={summary_df['D_nm2_ps'].min():.2e}, max={summary_df['D_nm2_ps'].max():.2e} nm^2/ps", tag='blue')
                
                # Identify windows with problematic D(z) values
                very_low_d = summary_df[summary_df['D_nm2_ps'] < 1e-4]
                if not very_low_d.empty:
                    logger(f"\nWarning: {len(very_low_d)} windows have very low D(z) (<1e-4 nm^2/ps):", tag='red')
                    for _, row in very_low_d.iterrows():
                        tau_info = f", tau={row['tau_ps']:.2f} ps" if 'tau_ps' in row else ""
                        r2_info = f", R2={row['R2']:.3f}" if 'R2' in row else ""
                        est_info = f", blocks={int(row['Estimates'])}" if 'Estimates' in row else ""
                        logger(f"  Z={row['Z_pos_nm']:.2f} nm: D={row['D_nm2_ps']:.2e}{tau_info}{r2_info}{est_info}", tag='red')
                    logger("Low D(z) values may indicate insufficient sampling or poor ACF fit quality.", tag='red')
                
                # Resistivity statistics
                negative_R = summary_df[summary_df['Resistivity'] < 0]
                if not negative_R.empty:
                    logger(f"\nWarning: {len(negative_R)} windows have NEGATIVE resistivity:", tag='red')
                    for _, row in negative_R.iterrows():
                        logger(f"  Z={row['Z_pos_nm']:.2f} nm: R={row['Resistivity']:.2e}, G={row['G_kJ_mol']:.2f} kJ/mol, D={row['D_nm2_ps']:.2e}", tag='red')
                    logger("Negative resistivity indicates exp(G/kBT) < D(z), which is physically impossible.", tag='red')
                
                logger(f"\nResistivity range: min={summary_df['Resistivity'].min():.2e}, max={summary_df['Resistivity'].max():.2e}", tag='blue')
                
                # Identify windows with extremely high resistivity (potential outliers)
                median_R = summary_df['Resistivity'].median()
                outlier_threshold = median_R * 1000  # 1000x median
                high_R = summary_df[summary_df['Resistivity'] > outlier_threshold]
                if not high_R.empty and outlier_threshold > 0:
                    logger(f"\nWarning: {len(high_R)} windows have extremely high resistivity (>1000× median):", tag='orange')
                    for _, row in high_R.head(5).iterrows():
                        tau_info = f", tau={row['tau_ps']:.2f} ps" if 'tau_ps' in row else ""
                        r2_info = f", R2={row['R2']:.3f}" if 'R2' in row else ""
                        logger(f"  Z={row['Z_pos_nm']:.2f} nm: R={row['Resistivity']:.2e}, G={row['G_kJ_mol']:.2f} kJ/mol, D={row['D_nm2_ps']:.2e}{tau_info}{r2_info}", tag='orange')
                    logger("High resistivity often occurs in membrane core where both energy barrier and friction are maximum.", tag='orange')
                    logger("However, extreme outliers may indicate convergence issues in that specific window.", tag='orange')
                
                # Provide actionable recommendations
                logger("\n--- Recommendations ---", tag='blue', bold=True)
                
                # Check if low R2 is the issue
                if 'R2' in summary_df.columns:
                    poor_r2_windows = summary_df[summary_df['R2'] < 0.8]
                    if not poor_r2_windows.empty:
                        logger(f"• {len(poor_r2_windows)} windows have poor ACF fit quality (R² < 0.8)", tag='orange')
                        logger("  → Poor fits indicate unreliable tau estimation", tag='orange')
                        logger("  → Solution: Run longer simulations for these specific windows", tag='orange')
                
                # Check if tau is extremely long in problematic windows
                if 'tau_ps' in summary_df.columns and not very_low_d.empty:
                    max_tau_in_problem_windows = very_low_d['tau_ps'].max() if 'tau_ps' in very_low_d.columns else 0
                    if max_tau_in_problem_windows > 1000:
                        logger(f"• Extremely long correlation times detected (up to {max_tau_in_problem_windows:.0f} ps)", tag='orange')
                        logger(f"  → These windows require >10× longer sampling for convergence", tag='orange')
                        logger(f"  → Current interval ({interval_size_points} points) may still be too small for these specific windows", tag='orange')
                
                # Check if this is a general convergence issue
                if max_simulation_time_ps > 0 and 'tau_ps' in summary_df.columns:
                    mean_tau = summary_df['tau_ps'].mean()
                    ratio = max_simulation_time_ps / mean_tau if mean_tau > 0 else 0
                    if ratio < 20:
                        logger(f"• Simulation length ({max_simulation_time_ps/1000:.1f} ns) is only {ratio:.1f}× the mean correlation time", tag='red')
                        logger("  → Recommended: Simulation length should be >50× tau for reliable statistics", tag='red')
                        logger("  → Solution: Extend simulation time significantly", tag='red')
                    else:
                        logger(f"• Overall simulation length is adequate ({ratio:.0f}× mean tau)", tag='green')
                        logger("  → Issue is likely specific to a few problematic windows", tag='green')
                
                # Final recommendation
                if use_optimized_interval:
                    logger("\n• Auto-optimization was used, but results are still invalid.", tag='orange')
                    logger("  → The issue is likely NOT the interval size.", tag='orange')
                    logger("  → More probable causes: insufficient simulation time, poor equilibration, or membrane instability", tag='orange')
                else:
                    logger(f"\n• Manual interval size was used ({interval_size_points} points).", tag='blue')
                    logger("  → Try enabling auto-optimization to let the program determine the best interval.", tag='blue')
                
                logger("")
                peff_valid = False
                log_peff = None
                log_bb = None
            else:
                log_peff = np.log10(peff_cm_s)
                log_bb = (log_peff - regression_intercept) / regression_slope
            
            # Apply pKa correction if pKa is provided AND at least one of acid/base is selected
            if pKa is not None and (is_acid or is_base) and pmf_neutral_path:
                if peff_valid:
                    logger(f"Permeability (Peff) - Ionized form only: {peff:.2e} nm/ps ({peff_cm_s:.2e} cm/s)", tag='red')
                    logger(f"LogPeff (ionized form only): {log_peff:.4f}", tag='red')
                    logger("")
                    logger(f"LogBB (ionized form only): {log_bb:.4f}", tag='logbb_highlight')
                    logger("")
                else:
                    logger('Skipping ionized LogPeff/LogBB reporting due to invalid Peff.', tag='red')
                try:
                    # Methodology from Biophysical Journal 107(3) 630–641, page 633
                    # For compounds existing in two protonation states at pH 7.4:
                    # 1. Calculate R_charged(z) from charged species PMF (already done above as 'Resistivity')
                    # 2. Calculate R_neutral(z) from neutral species PMF offset by ΔG_neutralize, using D(z) from neutral umbrella sampling
                    # 3. Combine: R(z) = R_c(z) * R_n(z) / (R_c(z) + R_n(z))
                    # 4. Integrate to get total resistance

                    pKa_val = float(pKa)
                    pH_blood = 7.4

                    if is_acid:
                        # For acids (HA ⇌ H+ + A-): ΔG_neutralize = (pH - pKa) * R * T * ln(10)
                        DG_neutralize = (pH_blood - pKa_val) * KB * T * np.log(10)
                        fraction_neutral = 1.0 / (1.0 + 10**(pH_blood - pKa_val))
                        logger(f"pKa correction for ΔG of neutralization (acid) | pKa={pKa_val:.2f}, pH={pH_blood}", tag='blue')
                    elif is_base:
                        # For bases (B + H+ ⇌ BH+): ΔG_neutralize = (pKa - pH) * R * T * ln(10)
                        DG_neutralize = (pKa_val - pH_blood) * KB * T * np.log(10)
                        fraction_neutral = 1.0 / (1.0 + 10**(pKa_val - pH_blood))
                        logger(f"pKa correction for ΔG of neutralization (base) | pKa={pKa_val:.2f}, pH={pH_blood}", tag='blue')
                    logger(f"ΔG of neutralization = {DG_neutralize:.4f} kJ/mol", tag='blue')
                    logger(f"Fraction neutral at pH {pH_blood}: {fraction_neutral:.4f}, based on Henderson-Hasselbalch", tag='blue')

                    # Load neutral species PMF
                    logger("")
                    logger(f"\n--- Processing neutral {compound_display} species PMF and umbrella files for pKa correction ---", tag='blue', bold=True)
                    logger("")
                    logger(f"Processing neutral PMF:", tag='blue')
                    logger(f"{pmf_neutral_path}", tag='orange')
                    logger("")
                    pmf_neutral_df = pd.read_csv(pmf_neutral_path, sep=r'\s+', comment='@', header=None, usecols=[0, 1], encoding='latin1', engine='python')
                    pmf_neutral_df.columns = ['Z_pos', 'G_kcal_mol']
                    pmf_neutral_df['Z_pos'] = pd.to_numeric(pmf_neutral_df['Z_pos'], errors='coerce')
                    pmf_neutral_df['G_kJ_mol'] = pd.to_numeric(pmf_neutral_df['G_kcal_mol'], errors='coerce') * 4.184
                    pmf_neutral_df = pmf_neutral_df.dropna()

                    # Normalize neutral PMF to bulk water
                    bulk_data_neutral = pmf_neutral_df.loc[pmf_neutral_df['Z_pos'] >= 3.5, 'G_kJ_mol']
                    if not bulk_data_neutral.empty:
                        bulk_reference_neutral = bulk_data_neutral.mean()
                        pmf_neutral_df['G_kJ_mol'] = pmf_neutral_df['G_kJ_mol'] - bulk_reference_neutral
                        logger(f"Neutral PMF normalized to bulk (Z>=3.5). Reference: {bulk_reference_neutral:.2f} kJ/mol", tag='blue')
                        logger("")

                    # Apply ΔG_neutralization offset to neutral PMF
                    pmf_neutral_df['G_kJ_mol_offset'] = pmf_neutral_df['G_kJ_mol'] + DG_neutralize

                    pmf_neutral_interp = interp1d(pmf_neutral_df['Z_pos'], pmf_neutral_df['G_kJ_mol_offset'], kind='cubic', fill_value='extrapolate')
                    summary_df['G_kJ_mol_neutral_offset'] = pmf_neutral_interp(summary_df['Z_pos_nm'])

                    # --- Calculate D(z) for neutral species from umbrella sampling files ---
                    # Prefer the function argument 'neutral_folder' if provided; otherwise fallback to folder/neutral
                    neutral_src = neutral_folder if (neutral_folder and os.path.isdir(neutral_folder)) else os.path.join(folder, 'neutral')
                    neutral_files = []
                    if os.path.isdir(neutral_src):
                        logger(f"Looking for pullx/umbrella .xvg files in neutral folder:", tag='blue')
                        logger(f"{neutral_src}", tag='orange')
                        # Only process umbrella sampling trajectory files (e.g., *pullx.xvg); skip PMF .xvg
                        neutral_files = [
                            os.path.join(neutral_src, f)
                            for f in os.listdir(neutral_src)
                            if f.lower().endswith('.xvg') and ('pullx' in f.lower() or 'umbrella' in f.lower())
                        ]
                    if not neutral_files:
                        logger('No neutral .xvg files found in neutral subfolder for neutral species D(z). Using charged D(z) as fallback.', tag='red')
                        logger('Check your folder structure', tag='red')
                        D_neutral_interp = interp1d(summary_df['Z_pos_nm'], summary_df['D_nm2_ps'], kind='linear', fill_value='extrapolate')
                    else:
                        all_files_summary_neutral = []
                        for file_path in neutral_files:
                            file_name = os.path.basename(file_path)
                            logger(f"Processing: {file_path}")
                            try:
                                df_xvg = pd.read_csv(file_path, sep=r'\s+', comment='@', header=None, usecols=[0, 1], on_bad_lines='skip', encoding='latin1', engine='python')
                                df_xvg.columns = ['Time', 'z (nm)']
                                df_xvg['z (nm)'] = pd.to_numeric(df_xvg['z (nm)'], errors='coerce')
                                df_xvg = df_xvg.dropna(subset=['z (nm)'])
                                z_values = df_xvg['z (nm)'].values
                                interval_size = interval_size_points
                                file_D_estimates = []
                                for i in range(0, len(z_values), interval_size):
                                    segment = z_values[i: i + interval_size]
                                    if len(segment) == interval_size:
                                        safe_max_lag = min(1000, len(segment) - 1)
                                        tau, r_sq = calculate_tau_least_squares(segment, time_step_of_simulation, max_lag=safe_max_lag)
                                        if tau and tau > 0:
                                            var_seg = np.var(segment, ddof=1)
                                            d_seg = var_seg / tau
                                            file_D_estimates.append(d_seg)
                                if file_D_estimates:
                                    final_D = np.mean(file_D_estimates)
                                    avg_Z_pos = np.mean(z_values)
                                    sample_count = len(file_D_estimates)
                                    if sample_count > 1:
                                        std_error_neutral = np.std(file_D_estimates, ddof=1) / np.sqrt(sample_count)
                                    else:
                                        std_error_neutral = 0.0
                                    all_files_summary_neutral.append({
                                        'Z_pos_nm': round(avg_Z_pos, 4),
                                        'D_nm2_ps_neutral': final_D,
                                        'Std_Error_neutral': std_error_neutral
                                    })
                                    # Log neutral umbrella processing summary per file
                                    logger(f"processing, {file_name}, success, average D {final_D:.4e} (from {len(file_D_estimates)} sample)", tag='green')
                            except Exception as e:
                                logger(f"Error processing neutral umbrella file {file_name}: {e}", tag='red')
                        if all_files_summary_neutral:
                            df_neutral_D = pd.DataFrame(all_files_summary_neutral).sort_values(by='Z_pos_nm')
                            if 'Std_Error_neutral' not in df_neutral_D.columns:
                                df_neutral_D['Std_Error_neutral'] = 0.0
                            df_neutral_D['Std_Error_neutral'] = df_neutral_D['Std_Error_neutral'].fillna(0.0)
                            neutral_plot_df = df_neutral_D.copy()
                            D_neutral_interp = interp1d(df_neutral_D['Z_pos_nm'], df_neutral_D['D_nm2_ps_neutral'], kind='linear', fill_value='extrapolate')
                        else:
                            logger('No valid D(z) estimates for neutral species. Using charged D(z) as fallback.', tag='red')
                            D_neutral_interp = interp1d(summary_df['Z_pos_nm'], summary_df['D_nm2_ps'], kind='linear', fill_value='extrapolate')

                    # Calculate R_charged(z) - already done as 'Resistivity'
                    # Calculate R_neutral(z) with offset PMF and D(z) from neutral umbrella sampling
                    KBT = KB * T
                    summary_df['Resistivity_charged'] = summary_df['Resistivity']  # From charged species PMF
                    summary_df['D_nm2_ps_neutral'] = D_neutral_interp(summary_df['Z_pos_nm'])
                    summary_df['Resistivity_neutral'] = np.exp(summary_df['G_kJ_mol_neutral_offset'] / KBT) / summary_df['D_nm2_ps_neutral']

                    # Combine resistivities: R(z) = R_c(z) * R_n(z) / (R_c(z) + R_n(z))
                    R_c = summary_df['Resistivity_charged']
                    R_n = summary_df['Resistivity_neutral']
                    summary_df['Resistivity_combined'] = (R_c * R_n) / (R_c + R_n)

                    logger("")
                    logger(f"Using combined resistivity formula - calculating neutral species D(z) from the neutral simulation umbrella files and PMF", tag='blue')
                    logger("")
                    # Calculate corrected permeability by integrating combined resistivity
                    total_resistance_corrected = simpson(summary_df['Resistivity_combined'], summary_df['Z_pos_nm'])
                    peff_corrected = 1 / total_resistance_corrected
                    peff_corrected_cm_s = peff_corrected * 1e-7 * 1e12
                    log_peff_corrected = np.log10(peff_corrected_cm_s)
                    log_bb_corrected = (log_peff_corrected - regression_intercept) / regression_slope

                    species_type = "Acid" if is_acid else "Base"
                    logger(f"Compound type: {species_type}", tag='blue')
                    logger("")
                    logger(f"Corrected Peff (accounting for ionized and neutral species): {peff_corrected:.2e} nm/ps ({peff_corrected_cm_s:.2e} cm/s)", tag='red')
                    logger(f"Corrected LogPeff: {log_peff_corrected:.4f}", bold=True, tag='red')
                    logger("")
                    logger(f"-----------------------------------------------------------", tag='red')
                    logger(f"|           LogBB (corrected): {log_bb_corrected:.4f}       |", tag='logbb_highlight')
                    logger("-----------------------------------------------------------", tag='red')

                    # Add dedicated graphs for neutral species when acid/base correction is applied
                    try:
                        fig_neutral_d = Figure(figsize=(3.5, 2.5))
                        ax_nd = fig_neutral_d.add_subplot(111)
                        if neutral_plot_df is not None:
                            x_vals = neutral_plot_df['Z_pos_nm'].values
                            y_vals = neutral_plot_df['D_nm2_ps_neutral'].values
                            y_err = neutral_plot_df['Std_Error_neutral'].values if 'Std_Error_neutral' in neutral_plot_df.columns else None
                        else:
                            x_vals = summary_df['Z_pos_nm'].values
                            y_vals = summary_df['D_nm2_ps_neutral'].values
                            y_err = None
                        ax_nd.errorbar(x_vals, y_vals, yerr=y_err, fmt='-o', color='#27AE60', ecolor='#27AE60', capsize=3, linewidth=2)
                        ax_nd.set_title('Local diffusion coefficient of neutral form', fontsize=9)
                        ax_nd.set_xlabel('Z-position (nm)', fontsize=8)
                        ax_nd.set_ylabel('D (nm^2/ps)', fontsize=8)
                        ax_nd.tick_params(labelsize=7)
                        ax_nd.grid(True, linestyle='--', alpha=0.5)
                        fig_neutral_d.tight_layout(pad=0.5)
                        figs.append(fig_neutral_d)
                        graph_names.append('Neutral_D_profile')
                    except Exception as e:
                        logger(f"Failed to plot neutral D(z): {e}", tag='red')

                    try:
                        fig_neutral_pmf = Figure(figsize=(3.5, 2.5))
                        ax_np = fig_neutral_pmf.add_subplot(111)
                        ax_np.plot(pmf_neutral_df['Z_pos'], pmf_neutral_df['G_kJ_mol'], label='Neutral PMF', color='#27AE60', linewidth=2)
                        ax_np.plot(pmf_neutral_df['Z_pos'], pmf_neutral_df['G_kJ_mol_offset'], label='Neutral PMF + ΔG neutralization', color='#C0392B', linestyle='--', linewidth=1.5)
                        ax_np.set_title('Potential of mean force of neutral form', fontsize=9)
                        ax_np.set_xlabel('Z-position (nm)', fontsize=8)
                        ax_np.set_ylabel('Free Energy G (kJ/mol)', fontsize=8)
                        ax_np.tick_params(labelsize=7)
                        ax_np.axhline(y=0, color='red', linestyle=':', linewidth=1.2)
                        ax_np.grid(True, linestyle='--', alpha=0.5)
                        ax_np.legend(fontsize=7)
                        fig_neutral_pmf.tight_layout(pad=0.5)
                        figs.append(fig_neutral_pmf)
                        graph_names.append('Neutral_PMF')
                    except Exception as e:
                        logger(f"Failed to plot neutral PMF: {e}", tag='red')
                except Exception as pka_err:
                    logger(f"pKa correction failed: {pka_err}")
            else:
                # When both acid and base are unchecked, report values without annotation
                if peff_valid:
                    logger(f"LogPeff: {log_peff:.4f}", tag='red', bold=True)
                    logger("")
                    logger(f"--------------------------------------------", tag='red')
                    logger(f"|          LogBB: {log_bb:.4f}         |", tag='logbb_highlight')
                    logger(f"--------------------------------------------", tag='red')
                    logger("")
                    logger("")
                    logger("")
                    logger('--------------------------------------------------------------------', tag='green')
                    logger(f'LogBB calculation finished successfully for {compound_display}', tag='green')
                    logger('--------------------------------------------------------------------', tag='green')
                else:
                    logger('LogPeff/LogBB not reported due to invalid Peff.', tag='red')
    except Exception as e:
        logger(f"Failed to compute Peff/logBB: {e}")

    return {'summary_df': summary_df, 'pmf_df': pmf_df, 'figs': figs, 'graph_names': graph_names,
            'peff': peff, 'logbb': log_bb, 'logbb_corrected': log_bb_corrected,
            'timestep': time_step_of_simulation, 'total_time_ns': max_simulation_time_ps / 1000 if max_simulation_time_ps else 0}
            

# Smoke test handler (use existing umbrella files; no demo data required)
if args.smoke_test:
    print('Running SMOKE TEST using the folder selected in script (if any) or environment...')
    folder_test = globals().get('file_folder') or os.environ.get('BBB_FOLDER') or os.getcwd()
    print(f'Using folder for smoke test: {folder_test}')
    Tval = float(os.environ.get('BBB_TEMP', '310'))
    pmf_env = os.environ.get('BBB_PMF')
    pka_env = os.environ.get('BBB_PKA')
    is_acid_env = os.environ.get('BBB_IS_ACID', '1') in ('1', 'true', 'True')
    res = run_simulation(folder_test, Tval, pmf_path=pmf_env, pKa=pka_env, is_acid=is_acid_env, monitor=False, logger=print, stop_event=None, max_files=2)
    if res and 'summary_df' in res and not res['summary_df'].empty:
        print('SMOKE TEST PASSED: simulation produced results.')
        sys.exit(0)
    else:
        print('SMOKE TEST FAILED: no results produced or errors occurred.')
        sys.exit(2)

# If the user runs the script normally, show the Run window
def start_run_window():
    root_run = tk.Tk()
    root_run.title('MD3B - Blood Brain Barrier permeability from MD umbrella sampling simulations')
    root_run.resizable(True, True)
    screen_width = root_run.winfo_screenwidth()
    screen_height = root_run.winfo_screenheight()
    init_width = min(1560, max(960, screen_width - 40))
    init_height = min(860, max(550, screen_height - 70))
    pos_x = max(0, (screen_width - init_width) // 2)
    pos_y = max(0, (screen_height - init_height) // 2)
    root_run.geometry(f"{init_width}x{init_height}+{pos_x}+{pos_y}")
    root_run.configure(bg='#f0f0f0')
    
    # Create menu bar
    menubar = tk.Menu(root_run)
    root_run.config(menu=menubar)
    
    # Help menu
    help_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label='Using the interface', menu=help_menu)
    
    # About menu (separate)
    about_menu = tk.Menu(menubar, tearoff=0)
    menubar.add_cascade(label='About', menu=about_menu)

    def create_responsive_text_dialog(title, content, width=600, height=420, font_size=10, bold_first_line=False):
        dlg = tk.Toplevel(root_run)
        dlg.title(title)
        dlg.configure(bg='white')
        dlg.resizable(True, True)
        dlg.minsize(240, 80)
        sw = dlg.winfo_screenwidth()
        sh = dlg.winfo_screenheight()

        body_fnt = tkfont.Font(family='Segoe UI', size=font_size)
        title_fnt = tkfont.Font(family='Segoe UI', size=font_size + 2, weight='bold')
        line_space = body_fnt.metrics('linespace')

        cleaned_content = content.rstrip('\n')
        raw_lines = cleaned_content.split('\n')
        max_line_px = max(
            (title_fnt.measure(ln) if (idx == 0 and bold_first_line) else body_fnt.measure(ln))
            for idx, ln in enumerate(raw_lines)
        ) if raw_lines else 300

        max_allowed_w = min(max(width, 500), max(340, sw - 80))
        w = min(max_allowed_w, max(340, max_line_px + 54))

        pad_x, pad_y = 16, 12
        px = max(0, (sw - w) // 2)
        py = max(0, (sh - 400) // 2)
        dlg.geometry(f"{w}x400+{px}+{py}")
        dlg.grid_rowconfigure(0, weight=1)
        dlg.grid_columnconfigure(0, weight=1)
        dlg.grid_columnconfigure(1, weight=0)

        text_widget = tk.Text(
            dlg,
            wrap='word',
            width=1,
            height=1,
            font=body_fnt,
            bg='white',
            fg='#1f2c3d',
            relief='flat',
            bd=0,
            highlightthickness=0,
            padx=pad_x,
            pady=pad_y
        )
        v_scroll = ttk.Scrollbar(dlg, orient='vertical', command=text_widget.yview)
        _vscroll_visible = [False]

        def _on_yscroll(first, last):
            v_scroll.set(first, last)
            try:
                need_scroll = not (float(first) <= 0.001 and float(last) >= 0.999)
                if need_scroll != _vscroll_visible[0]:
                    _vscroll_visible[0] = need_scroll
                    if need_scroll:
                        v_scroll.grid(row=0, column=1, sticky='ns')
                    else:
                        v_scroll.grid_remove()
            except Exception:
                pass

        text_widget.configure(yscrollcommand=_on_yscroll)
        text_widget.grid(row=0, column=0, sticky='nsew')

        sizegrip = ttk.Sizegrip(dlg)
        sizegrip.place(relx=1.0, rely=1.0, anchor='se')

        text_widget.insert('1.0', cleaned_content)
        if bold_first_line:
            text_widget.tag_config('title', font=title_fnt)
            text_widget.tag_add('title', '1.0', '1.end')

        # Prevent ASCII folder trees and separator lines from wrapping into broken fragments on resize
        text_widget.tag_config('nowrap', wrap='none')
        for idx, ln in enumerate(raw_lines, start=1):
            stripped = ln.strip()
            if any(tok in ln for tok in ('├──', '└──', '└─', '│')) or (
                len(stripped) >= 10 and set(stripped) <= {'=', '-'}
            ):
                text_widget.tag_add('nowrap', f'{idx}.0', f'{idx}.end')

        text_widget.config(state='disabled')

        # Measure exact rendered pixel height and fit the dialog snugly to its content with zero scrollbar
        try:
            dlg.update_idletasks()
            _set_win32_class_bg(dlg, '#ffffff')
            _set_win32_class_bg(text_widget, '#ffffff')
            dlg.update()
            ypix = text_widget.count('1.0', 'end', 'ypixels')
            ypix_val = ypix[0] if isinstance(ypix, tuple) and ypix else (int(ypix) if ypix else 0)
            if ypix_val > 0:
                exact_h = min(max(70, ypix_val + 2 * pad_y + 6), sh - 80)
                py = max(0, (sh - exact_h) // 2)
                dlg.geometry(f"{w}x{exact_h}+{px}+{py}")
                dlg.update_idletasks()
                dlg.update()
                while text_widget.yview()[1] < 0.999 and exact_h < sh - 80:
                    exact_h = min(exact_h + line_space, sh - 80)
                    py = max(0, (sh - exact_h) // 2)
                    dlg.geometry(f"{w}x{exact_h}+{px}+{py}")
                    dlg.update_idletasks()
                    dlg.update()
        except Exception:
            pass

        def _on_dlg_mousewheel(event):
            try:
                if event.delta:
                    direction = -1 if event.delta > 0 else 1
                else:
                    direction = -1 if event.num == 4 else 1
                text_widget.yview_scroll(direction * 2, 'units')
            except Exception:
                pass

        text_widget.bind('<MouseWheel>', _on_dlg_mousewheel, add='+')
        text_widget.bind('<Button-4>', _on_dlg_mousewheel, add='+')
        text_widget.bind('<Button-5>', _on_dlg_mousewheel, add='+')
        return dlg

    def show_about():
        create_responsive_text_dialog(
            'About BBB Permeability Calculator',
            'Blood-Brain Barrier (BBB) Permeability Calculator\n\n'
            'MD3B v.1.0\n'
            '-------------------------------------------------\n\n'
            'This tool predicts Blood-Brain Barrier permeability from Molecular Dynamics simulations '
            'using the umbrella sampling biased technique.\n\n'
            'It processes diffusion coefficient profiles and potential of mean force (PMF) data to compute '
            'effective permeability values and LogBB values (logarithm of the brain-to-blood concentration ratio).\n\n'
            'Permeability predictions help in drug development by assessing whether compounds can partition into the CNS.\n\n'
            'Developed at Pharmacy Department, National and Kapodistrian University of Athens, Greece.\n'
            'For feedback or technical issues please contact: vmyriant@pharm.uoa.gr\n\n'
            'Distributed under MIT License.\n\n'
            'Version 1.0\n'
            'Last updated: 10-2026',
            width=540,
            height=380,
            font_size=10,
            bold_first_line=True
        )

    def show_user_guide():
        separator_line = '=' * 50
        create_responsive_text_dialog(
            'User Guide',
            'USER GUIDE\n' +
            separator_line + '\n\n' +
            '1. PREPARING THE FOLDER STRUCTURE:\n'
            '   - Create a main folder (root folder) named after the compound under study (e.g., "[Drug name]")\n'
            '   - If the compound is an acid or base, inside the root folder create two subfolders: "neutral" and "ionized"\n'
            '     If the compound does not ionize at pH 7.4, only the "neutral" subfolder is needed\n'
            '         NOTE: The folder names "neutral" and "ionized" are case-sensitive and must be exactly as shown.\n'
            '   - Place the corresponding GROMACS umbrella sampling pullx.xvg files and respective PMF .xvg file in each subfolder:\n'
            '       a) "neutral" folder: contains files for the neutral species\n'
            '       b) "ionized" folder: contains files for the charged species (if applicable)\n'
            '         NOTE: PMF files should contain Z-position and free energy columns\n\n'
            '2. CALCULATION SETTINGS:\n'
            '   - Click "Browse" to select the root folder\n'
            '   - Select the appropriate checkbox "Compound is an acid" or "Compound is a base" (if it ionizes considerably at pH 7.4)\n'
            '   - The compound name and respective umbrella sampling and PMF files will be automatically identified from the folder structure\n'
            '   - Define temperature of MD simulations (in Kelvin) in the respective field\n'
            '   - Typical value for body temperature: 310 K (37°C), for LogBB calculations with DOPC: 323 K (50°C)\n'
            '   - For acidic or basic compounds, enter the pKa value\n'
            '   - The pKa is used to shift the neutral PMF by the pKa-dependent ΔG at pH 7.4 applying correction for the neutral fraction\n\n'
            '3. RUN CALCULATION:\n'
            '   - Click "Run calculation" to start the analysis\n'
            '   - Results will appear in the output panel\n'
            '   - Graphs will show the diffusion profile and PMF of the assessed molecule\n\n'
            '4. STOP CALCULATION:\n'
            '   - Click to stop a running simulation\n'
            '   - Available only during active calculations\n\n'
            '5. END PROGRAM:\n'
            '   - Click to close the application\n\n'
            'ABOUT CORRECTION:\n'
            '   - If the compound ionizes, provide the PMF of the neutral species (neutral PMF)\n'
            '   - The neutral PMF is shifted by the pKa-dependent dG neutralization, then combined with D(z) '
            'from neutral umbrella trajectories to build the corrected resistivity profile\n'
            '   - If no neutral umbrella files are available, the code falls back to using the charged D(z)\n'
            '   - If the compound does not ionize, leave this field empty\n',
            width=800,
            height=520,
            font_size=9,
            bold_first_line=True
        )

    def show_interval_help():
        separator_line = '=' * 50
        create_responsive_text_dialog(
            'Interval Size Guidance',
            'INTERVAL SIZE (SEGMENT LENGTH)\n' +
            separator_line + '\n\n'
            'The interval size controls how many points are used per block when '
            'estimating tau and local diffusion coefficients. It affects stability '
            'and variance of the results.\n\n'
            'Recommended interval:\n'
            '  - The tool estimates a recommended value from the trajectory files '
            'using an approximate correlation time (tZ).\n'
            '  - As a rule of thumb, the block length should be at least 10-50 times tZ.\n\n'
            'Default interval:\n'
            '  - The default is 5000 points (often suitable for typical umbrella runs).\n\n'
            'Tips:\n'
            '  - Too small: noisy estimates and unstable tau values.\n'
            '  - Too large: too few blocks and large uncertainty.\n'
            '  - Aim for at least 10-20 blocks for reliable error bars.\n',
            width=540,
            height=360,
            font_size=9,
            bold_first_line=True
        )

    def show_correction_summary():
        separator_line = '=' * 50
        create_responsive_text_dialog(
            'Neutral PMF Correction Summary',
            'NEUTRAL PMF CORRECTION SUMMARY\n' +
            separator_line + '\n\n'
            'When a compound can exist in ionized and neutral forms at pH 7.4, the code '
            'combines both pathways to compute a corrected permeability:\n\n'
            '1) Charged pathway:\n'
            '   - Compute R_c(z) = exp(G_c(z)/kBT) / D_c(z) using the ionized PMF and '
            'diffusion profile from ionized umbrella files.\n\n'
            '2) Neutral pathway:\n'
            '   - Apply the pKa-dependent neutralization shift dG to the neutral PMF:\n'
            '     G_n*(z) = G_n(z) + dG, where at pH = 7.4:\n'
            '       * Acids (HA <-> H+ + A-): dG = (pH - pKa) * R * T * ln(10)\n'
            '       * Bases (B + H+ <-> BH+): dG = (pKa - pH) * R * T * ln(10)\n'
            '   - Compute D_n(z) from neutral umbrella files (fallback to D_c(z) if missing).\n'
            '   - Compute R_n(z) = exp(G_n*(z)/kBT) / D_n(z).\n\n'
            '3) Combine pathways:\n'
            '   - Use the parallel-resistivity formula:\n'
            '     R_combined(z) = (R_c(z) * R_n(z)) / (R_c(z) + R_n(z)).\n\n'
            '4) Final result:\n'
            '   - Integrate R_combined(z) to get corrected Peff and LogBB.\n',
            width=560,
            height=400,
            font_size=9,
            bold_first_line=True
        )

    def show_faq():
        separator_line = '=' * 50
        create_responsive_text_dialog(
            'FAQ',
            'FREQUENTLY ASKED QUESTIONS\n' +
            separator_line + '\n\n' +
            'Q: What are umbrella sampling files?\n'
            'A: These are GROMACS .xvg files containing Z-coordinate trajectories from umbrella sampling simulations '
            'in GROMACS format. Multiple files represent different sampling windows.\n\n'
            'Q: Why is PMF file important?\n'
            'A: The PMF (Potential of Mean Force) provides the free energy barrier for crossing the BBB, '
            'essential for calculating permeability accurately.\n\n'
            'Q: What does LogBB value mean?\n'
            'A: LogBB is a predictive measure for BBB penetration:\n'
            '   LogBB > 0.5: Good BBB penetration\n'
            '   0.5 > LogBB > -0.5: Moderate BBB penetration\n'
            '   LogBB < -0.5: Poor BBB penetration\n\n'
            'Q: What is the typical temperature value?\n'
            'A: A temperature of 310 K (37°C) represents normal human body temperature. '
            'However, you must use the temperature at which your simulations were performed.\n\n'
            'Q: How long should simulations be?\n'
            'A: Total simulation should be at least 10-50 times the correlation time (tZ) '
            'for statistically significant results.\n\n'
            'Q: What does pKa correction do?\n'
            'A: It shifts the neutral-species PMF by the pKa-dependent dG at pH 7.4 and '
            'recomputes resistivity using D(z) from neutral umbrella files, which '
            'yields a more accurate BBB permeability for ionizable compounds.',
            width=620,
            height=500,
            font_size=9,
            bold_first_line=True
        )

    def show_contact():
        separator_line = '=' * 50
        create_responsive_text_dialog(
            'Contact & Support',
            'CONTACT & SUPPORT\n' +
            separator_line + '\n\n' +
            'For issues, questions, or suggestions please contact: vmyriant@pharm.uoa.gr\n\n'
            'Documentation:\n'
            '  Check the User Guide available in the GitHub repository\n\n'
            'Troubleshooting:\n'
            '  - Ensure all input files are in the correct .xvg format\n'
            '  - Check that all folder paths are correct\n'
            '  - Verify the temperature value is realistic\n\n'
            'Error Messages:\n'
            '  Check the Simulation Output panel for detailed error information\n\n'
            'File Format:\n'
            '  Input files should be GROMACS .xvg format with:\n'
            '  - Header lines starting with # or @\n'
            '  - Data columns: time, z-coordinate\n\n',
            width=520,
            height=340,
            font_size=10,
            bold_first_line=True
        )
    
    help_menu.add_command(label='User Guide', command=show_user_guide)
    help_menu.add_command(label='Interval Size Guidance', command=show_interval_help)
    help_menu.add_command(label='Neutral PMF correction', command=show_correction_summary)
    help_menu.add_command(label='FAQ', command=show_faq)
    help_menu.add_separator()
    help_menu.add_command(label='Contact & Support', command=show_contact)
    
    about_menu.add_command(label='About this Tool', command=show_about)
    
    # Configure grid weights for a resizable layout
    root_run.grid_rowconfigure(0, weight=1)  # Main content row
    root_run.grid_rowconfigure(1, weight=0)  # Status bar - fixed size
    root_run.grid_rowconfigure(2, weight=0)  # End button - fixed size
    root_run.grid_columnconfigure(0, weight=1)

    # Main horizontal PanedWindow allowing mouse-adjustable width between left controls and right results
    main_paned = tk.PanedWindow(
        root_run,
        orient='horizontal',
        sashwidth=8,
        sashpad=2,
        sashrelief='raised',
        showhandle=True,
        handlesize=10,
        sashcursor='sb_h_double_arrow',
        bg='#b8cae4',
        opaqueresize=True
    )
    main_paned.grid(row=0, column=0, sticky='nsew', padx=0, pady=0)
    
    # Color scheme
    primary_color = "#6DB9EE"
    success_color = "#7BA3ED"
    danger_color = "#D5564A"
    bg_color = '#eef3fb'
    frame_color = '#ffffff'
    label_color = '#1f2c3d'
    browse_color = "#135989"
    disabled_fg_color = "#F4ECEC"
    card_bg = '#f9fbff'
    card_border = '#dce6f5'
    section_title_font = ('Segoe UI', 12, 'bold')
    body_font = ('Segoe UI', 10)
    
    # Helper to create consistent card-like sections for inputs
    def create_section(parent, title, row, column, columnspan=1, sticky='nsew'):
        container = tk.Frame(parent, bg=frame_color)
        container.grid(row=row, column=column, columnspan=columnspan, sticky=sticky, padx=(10,6), pady=(2,5))
        title_label = tk.Label(container, text=title, font=section_title_font, bg=frame_color, fg=label_color)
        title_label.pack(anchor='w')
        card = tk.Frame(container, bg=card_bg, bd=0, highlightbackground=card_border,
                        highlightcolor=card_border, highlightthickness=1, padx=12, pady=6)
        card.pack(fill='both', expand=True, pady=(2,0))
        return card

    # Scrollable container for controls (left column) inside main_paned
    left_container = tk.Frame(main_paned, bg=frame_color, relief='flat', bd=0)
    left_container.grid_rowconfigure(0, weight=1)
    left_container.grid_rowconfigure(1, weight=0)
    left_container.grid_columnconfigure(0, weight=1)
    left_container.grid_columnconfigure(1, weight=0)

    controls_canvas = tk.Canvas(left_container, bg=frame_color, bd=0, highlightthickness=0, width=900)
    controls_scrollbar = ttk.Scrollbar(left_container, orient='vertical', command=controls_canvas.yview)
    controls_h_scrollbar = ttk.Scrollbar(left_container, orient='horizontal', command=controls_canvas.xview)
    controls_canvas.configure(yscrollcommand=controls_scrollbar.set, xscrollcommand=controls_h_scrollbar.set)

    controls_canvas.grid(row=0, column=0, sticky='nsew')
    controls_scrollbar.grid(row=0, column=1, sticky='ns')
    controls_h_scrollbar.grid(row=1, column=0, sticky='ew')

    top_frame = tk.Frame(controls_canvas, bg=frame_color, relief='flat', bd=0)
    top_frame.grid_columnconfigure(0, weight=1)
    top_frame_window = controls_canvas.create_window((0, 0), window=top_frame, anchor='nw')

    _scroll_region_job = [None]
    _last_controls_width = [0]

    def _apply_controls_scroll_region():
        _scroll_region_job[0] = None
        try:
            if root_run.state() == 'iconic':
                return
            bbox = controls_canvas.bbox('all')
            if bbox:
                controls_canvas.configure(scrollregion=bbox)
        except Exception:
            pass

    def configure_controls_scroll_region(event=None):
        if _scroll_region_job[0] is None:
            _scroll_region_job[0] = root_run.after_idle(_apply_controls_scroll_region)

    top_frame.bind('<Configure>', configure_controls_scroll_region)

    def _on_controls_canvas_configure(event):
        canvas_width = event.width
        if canvas_width < 120:
            return
        try:
            if root_run.state() == 'iconic':
                return
        except Exception:
            pass
        if abs(canvas_width - _last_controls_width[0]) < 2:
            return
        _last_controls_width[0] = canvas_width
        _update_left_pane_responsive_layout(canvas_width)
        controls_canvas.itemconfig(top_frame_window, width=canvas_width)
        configure_controls_scroll_region()

    controls_canvas.bind('<Configure>', _on_controls_canvas_configure)

    def _on_controls_mousewheel(event):
        try:
            if event.delta:  # Windows
                direction = -1 if event.delta > 0 else 1
            else:  # Linux
                direction = -1 if event.num == 4 else 1
            controls_canvas.yview_scroll(direction * 2, 'units')
        except Exception:
            pass

    def _on_controls_shift_mousewheel(event):
        try:
            if event.delta:  # Windows
                direction = -1 if event.delta > 0 else 1
            else:  # Linux
                direction = -1 if event.num == 4 else 1
            controls_canvas.xview_scroll(direction * 2, 'units')
        except Exception:
            pass

    def _bind_controls_scroll_events(widget):
        widget.bind('<MouseWheel>', _on_controls_mousewheel, add='+')
        widget.bind('<Shift-MouseWheel>', _on_controls_shift_mousewheel, add='+')
        widget.bind('<Button-4>', _on_controls_mousewheel, add='+')
        widget.bind('<Button-5>', _on_controls_mousewheel, add='+')
        widget.bind('<Shift-Button-4>', _on_controls_shift_mousewheel, add='+')
        widget.bind('<Shift-Button-5>', _on_controls_shift_mousewheel, add='+')
        for child in widget.winfo_children():
            _bind_controls_scroll_events(child)

    root_run.minsize(650, 420)  # Allow mouse resizing down to compact size

    main_paned.add(left_container, minsize=430, stretch='always')

    # Vertical PanedWindow for right side allowing mouse-adjustable height between output and plots
    right_column = tk.PanedWindow(
        main_paned,
        orient='vertical',
        sashwidth=8,
        sashpad=2,
        sashrelief='raised',
        showhandle=True,
        handlesize=10,
        sashcursor='sb_v_double_arrow',
        bg='#b8cae4',
        opaqueresize=True
    )
    main_paned.add(right_column, minsize=320, stretch='always')
    
    def show_folder_info():
        create_responsive_text_dialog(
            'Simulation Folder - Help',
            'Simulation Folder:\n\n'
            'Structure your files as follows:\n'
            '  - Root folder: {named as the compound}\n'
            '  - Subfolders:\n'
            '    - neutral (necessary)\n'
            '    - ionized (if compound ionizes)\n\n'
            'Paste .xvg files of neutral and ionized simulations into the corresponding subfolders:\n\n'
            'Example folder structure:\n\n'
            'C:/path/to/imipramine/\n'
            '                    ├── neutral/\n'
            '                    │         └─ PMF_imipramine.xvg\n'
            '                    │         └─ umbrella0_pullx.xvg\n'
            '                    │         └─ ........................xvg\n'
            '                    │         └─ umbrellaXX_pullx.xvg\n'
            '                    └── ionized/\n'
            '                                └─ PMF_imipramine.xvg\n'
            '                                └─ umbrella0_pullx.xvg\n'
            '                                └─ ........................xvg\n'
            '                                └─ umbrellaXX_pullx.xvg\n',
            width=480,
            height=420,
            font_size=9,
            bold_first_line=True
        )
    
    folder_var = tk.StringVar()
    folder_section = create_section(top_frame, '1 · Simulation Folder', row=0, column=0, columnspan=1)
    folder_section.grid_columnconfigure(1, weight=1)
    tk.Label(folder_section, text='Simulation folder:', bg=card_bg, fg=label_color, font=('Segoe UI', 11, 'bold')).grid(row=0, column=0, sticky='w')
    folder_entry = tk.Entry(folder_section, textvariable=folder_var, width=16, font=body_font, relief='flat', bd=1,
                            highlightthickness=1, highlightbackground='#d0d0d0', highlightcolor='#2E86DE')
    folder_entry.grid(row=0, column=1, sticky='ew', padx=(8,0))
    # Compound name field (unified in the same card as Simulation folder)
    compound_name_var = tk.StringVar()
    tk.Label(folder_section, text='Compound name:', bg=card_bg, fg=label_color,
             font=('Segoe UI', 11, 'bold')).grid(row=1, column=0, sticky='w', pady=(4,0))
    compound_entry = tk.Entry(folder_section, textvariable=compound_name_var, width=16, font=('Segoe UI', 14, 'bold'),
                               fg="#D22E1C", state='readonly', readonlybackground=card_bg, relief='flat', bd=0)
    compound_entry.grid(row=1, column=1, columnspan=3, sticky='ew', padx=(8,0), pady=(4,0))

    recommended_interval_var_run = tk.StringVar(value=' - ')
    recommended_interval_points_run = tk.IntVar(value=0)
    interval_size_var_run = tk.StringVar(value='5000')

    # Flashing "Calculating..." animation
    _calc_flash_states = ['Calculating.', 'Calculating..', 'Calculating...', 'Calculating..', 'Calculating.']
    _calc_flash_idx = [0]  # mutable container so the closure can update it

    def _flash_calculating():
        current = recommended_interval_var_run.get()
        if current.startswith('Calculating'):
            recommended_interval_var_run.set(_calc_flash_states[_calc_flash_idx[0] % len(_calc_flash_states)])
            _calc_flash_idx[0] += 1
            recommended_interval_entry.config(fg='#1a8a2e', font=('Segoe UI', 10, 'bold'))
            root_run.after(400, _flash_calculating)
        else:
            _calc_flash_idx[0] = 0
            recommended_interval_entry.config(fg='#7a7a7a', font=('Segoe UI', 10))

    def update_recommended_interval_display(folder_path):
        """Run interval optimisation in a background thread so the GUI stays responsive."""
        recommended_interval_var_run.set('Calculating...')
        recommended_interval_points_run.set(0)
        _calc_flash_idx[0] = 0
        _flash_calculating()  # start flash animation
        if not folder_path:
            recommended_interval_var_run.set('N/A')
            return

        def _worker():
            """Heavy I/O + computation — runs off the main thread."""
            candidate_dirs = []
            for sub in ('ionized', 'neutral'):
                sub_path = os.path.join(folder_path, sub)
                if os.path.isdir(sub_path):
                    candidate_dirs.append(sub_path)
            candidate_dirs.append(folder_path)

            # Collect ALL umbrella/pullx files (same logic the run uses)
            candidate_files = []
            for candidate in candidate_dirs:
                try:
                    entries = os.listdir(candidate)
                except Exception:
                    continue
                for name in entries:
                    lower_name = name.lower()
                    if lower_name.endswith('.xvg') and ('pullx' in lower_name or 'umbrella' in lower_name):
                        candidate_files.append(os.path.join(candidate, name))
            if not candidate_files:
                root_run.after(0, lambda: recommended_interval_var_run.set('N/A'))
                return

            # Use the same optimizer the run uses, with a silent logger
            def silent_logger(*args, **kwargs):
                return

            rec_size = None
            try:
                mode = optimize_mode_var.get().lower()
                rec_size, _ = optimize_interval_size(candidate_files, 0.1, logger=silent_logger, mode=mode)
            except Exception:
                pass

            # Fallback: single-file estimate if full optimization fails
            if not rec_size:
                try:
                    first_file = candidate_files[0]
                    df_first = pd.read_csv(first_file, sep=r'\s+', comment='@', header=None,
                                           usecols=[0, 1], on_bad_lines='skip', encoding='latin1', engine='python')
                    if not df_first.empty:
                        df_first.columns = ['Time', 'z (nm)']
                        z_first = pd.to_numeric(df_first['z (nm)'], errors='coerce').dropna().values
                        if len(z_first) >= 2:
                            rec_size, _ = recommend_interval_size(z_first, 0.1)
                except Exception:
                    pass

            # Push result back to the GUI thread
            def _update_gui():
                if rec_size:
                    recommended_interval_points_run.set(int(rec_size))
                    recommended_interval_var_run.set(f"{rec_size} pts (~{rec_size * 0.1:.1f} ps)")
                else:
                    recommended_interval_var_run.set('N/A')

            root_run.after(0, _update_gui)

        threading.Thread(target=_worker, daemon=True).start()
    
    def browse_folder_run():
        d = filedialog.askdirectory(title='Select Simulation Folder')
        if d:
            folder_var.set(d)
            # Extract compound name from folder path
            compound_name = os.path.basename(d)
            compound_name_var.set(compound_name)
            # Verify required neutral subfolder exists for corrections
            if not os.path.isdir(os.path.join(d, 'neutral')):
                tk.messagebox.showerror(
                    'Folder structure error',
                    "Missing subfolder: neutral. Check your folder structure."
                )
            # Auto-search for PMF and pullx.xvg in neutral/ionized subfolders
            neutral_sub = os.path.join(d, 'neutral')
            ionized_sub = os.path.join(d, 'ionized')

            if os.path.isdir(ionized_sub):
                ionized_pmf = [os.path.join(ionized_sub, f) for f in os.listdir(ionized_sub) if 'pmf' in f.lower() and f.endswith('.xvg')]
                ionized_pullx = [os.path.join(ionized_sub, f) for f in os.listdir(ionized_sub) if f.endswith('pullx.xvg')]
                pmf_ionized_var_run.set(ionized_pmf[0] if ionized_pmf else 'No PMF file found')
                ionized_pullx_var_run.set(ionized_pullx[0] if ionized_pullx else 'No pullx.xvg file found')
            else:
                pmf_ionized_var_run.set(' - ')
                ionized_pullx_var_run.set(' - ')

            if os.path.isdir(neutral_sub):
                neutral_pmf = [os.path.join(neutral_sub, f) for f in os.listdir(neutral_sub) if 'pmf' in f.lower() and f.endswith('.xvg')]
                neutral_pullx = [os.path.join(neutral_sub, f) for f in os.listdir(neutral_sub) if f.endswith('pullx.xvg')]
                pmf_neutral_var_run.set(neutral_pmf[0] if neutral_pmf else 'No PMF file found')
                neutral_pullx_var_run.set(neutral_pullx[0] if neutral_pullx else 'No pullx.xvg file found')
            else:
                pmf_neutral_var_run.set('No neutral folder found')
                neutral_pullx_var_run.set('No neutral folder found')
            if auto_optimize_interval_var.get():
                update_recommended_interval_display(d)
            else:
                recommended_interval_var_run.set(' - ')
                recommended_interval_points_run.set(0)
    
    browse_folder_btn = tk.Button(
        folder_section,
        text='Browse',
        fg='white',
        bg=browse_color,
        font=('Segoe UI', 10, 'bold'),
        relief='raised',
        bd=2,
        cursor='hand2',
        command=browse_folder_run,
        padx=12,
        pady=2,
        activebackground='#0d4266',
        activeforeground='white'
    )
    help_buttons = []

    def create_help_button(parent, command):
        btn = tk.Button(
            parent,
            text='help',
            command=command,
            bg='#e8f0fe',
            fg='#135989',
            activebackground='#135989',
            activeforeground='white',
            font=('Segoe UI', 9, 'bold'),
            relief='solid',
            bd=1,
            padx=8,
            pady=1,
            cursor='hand2'
        )
        btn.bind('<Enter>', lambda e: btn.config(bg='#d2e3fc', fg='#0d4266'))
        btn.bind('<Leave>', lambda e: btn.config(bg='#e8f0fe', fg='#135989'))
        help_buttons.append(btn)
        return btn

    browse_folder_btn.grid(row=0, column=2, padx=(10,0))
    info_btn = create_help_button(folder_section, show_folder_info)
    info_btn.grid(row=0, column=3, padx=(6,0))
    
    simulation_section = create_section(top_frame, '2 · Simulation Settings', row=2, column=0, columnspan=1)
    simulation_section.grid_columnconfigure(2, weight=1)
    # First row: temperature on the left, interval size on the right
    tk.Label(simulation_section, text='Simulation temperature (K):', bg=card_bg, fg=label_color,
             font=('Segoe UI', 11, 'bold')).grid(row=0, column=0, sticky='w')

    def show_temp_info():
        create_responsive_text_dialog(
            'Temperature & Interval - Help',
            'The interval size is measured in timesteps (usually 0.1 ps) and controls how many points '
            'are used per analysis block for estimating tau and local diffusion coefficients.\n\n'
            'Selection is critical as it affects stability and variance of the results and needs optimization '
            'on the basis of a carefully chosen training set.\n',
            width=420,
            height=260,
            font_size=9
        )

    temp_var_run = tk.DoubleVar()
    temp_entry_var_run = tk.StringVar(value="")
    temp_entry_run = tk.Entry(simulation_section, textvariable=temp_entry_var_run, width=12, font=body_font,
                              relief='solid', bd=1, highlightthickness=1, highlightbackground='#d0d0d0', highlightcolor='#2E86DE')
    temp_entry_run.grid(row=0, column=1, sticky='w', padx=(8,12))

    tk.Label(simulation_section, text='Interval size (timestep points):', bg=card_bg, fg=label_color,
             font=('Segoe UI', 11, 'bold')).grid(row=1, column=0, sticky='w', pady=(6,0))
    interval_entry_run = tk.Entry(simulation_section, textvariable=interval_size_var_run, width=12, font=body_font,
                                  relief='solid', bd=1, highlightthickness=1, highlightbackground='#d0d0d0', highlightcolor='#2E86DE')
    interval_entry_run.grid(row=1, column=1, sticky='w', padx=(8,0), pady=(6,0))

    interval_actions_frame = tk.Frame(simulation_section, bg=card_bg)
    interval_actions_frame.grid(row=1, column=2, sticky='w', padx=(10,0), pady=(6,0))
    tk.Label(interval_actions_frame, text='(Default: 5000 points)', bg=card_bg, fg=label_color,
             font=('Segoe UI', 10)).pack(side='left', padx=(0,10))
    use_recommended_btn = tk.Button(
        interval_actions_frame,
        text='Use recommended',
        fg='white',
        bg=browse_color,
        font=('Segoe UI', 10, 'bold'),
        relief='raised',
        bd=2,
        cursor='hand2',
        command=lambda: interval_size_var_run.set(str(recommended_interval_points_run.get())) if recommended_interval_points_run.get() > 0 else None,
        padx=10,
        pady=2,
        activebackground='#0d4266',
        activeforeground='white'
    )
    use_recommended_btn.pack(side='left', padx=(0,6))
    use_default_btn = tk.Button(
        interval_actions_frame,
        text='Use default',
        fg='white',
        bg=browse_color,
        font=('Segoe UI', 10, 'bold'),
        relief='raised',
        bd=2,
        cursor='hand2',
        command=lambda: interval_size_var_run.set('5000'),
        padx=10,
        pady=2,
        activebackground='#0d4266',
        activeforeground='white'
    )
    use_default_btn.pack(side='left')
    
    # Auto-optimize checkbox
    auto_optimize_interval_var = tk.BooleanVar(value=False)
    
    def toggle_interval_entry():
        """Enable or disable interval entry based on auto-optimize checkbox"""
        if auto_optimize_interval_var.get():
            interval_entry_run.config(state='disabled', bg='#f0f0f0')
            optimize_mode_combo.config(state='readonly')
            # Trigger optimization if a folder is already selected
            current_folder = folder_var.get().strip()
            if current_folder and os.path.isdir(current_folder):
                update_recommended_interval_display(current_folder)
        else:
            interval_entry_run.config(state='normal', bg='white')
            optimize_mode_combo.config(state='disabled')
            recommended_interval_var_run.set(' - ')
            recommended_interval_points_run.set(0)
    
    def show_auto_optimize_info():
        create_responsive_text_dialog(
            'Auto-optimize interval',
            'Auto-Optimize Interval Size\n\n'
            'When enabled, the simulation automatically determines the optimal interval size '
            'for block averaging based on the statistical properties of your trajectory data.\n\n'
            'How it works:\n'
            '• Analyzes autocorrelation times (τZ) from trajectory files\n'
            '• Tests many candidate intervals (100 to 15,000 points)\n'
            '• Scores each by block-averaging quality and number of blocks\n'
            '• Prefers more blocks (better averaging) over perfect individual fits\n'
            '• Caps at 15,000 points maximum\n\n'
            'Recommended:\n'
            '• Leave enabled for most simulations (default)\n'
            '• Prevents common issues with overly large or small intervals\n'
            '• Optimizes accuracy for systems with heterogeneous diffusion\n\n'
            'Manual mode:\n'
            '• Uncheck to specify your own interval size\n'
            '• Useful for consistent comparison across datasets\n'
            '• Warning: Values >15,000 may cause statistical errors',
            width=600,
            height=380,
            font_size=10,
            bold_first_line=True
        )

    # Recommended interval moved to its own line, left-aligned under the other fields
    recommended_interval_label = tk.Label(simulation_section, text='Recommended interval:', bg=card_bg, fg=label_color,
                                          font=('Segoe UI', 11, 'bold'))
    recommended_interval_label.grid(row=3, column=0, sticky='w', pady=(6,0))
    recommended_interval_entry = tk.Entry(
        simulation_section,
        textvariable=recommended_interval_var_run,
        width=18,
        font=('Segoe UI', 10),
        state='readonly',
        readonlybackground=card_bg,
        relief='flat',
        bd=0,
        highlightthickness=0,
        fg='#7a7a7a'
    )
    recommended_interval_entry.grid(row=3, column=1, sticky='w', padx=(8,0), pady=(6,0))

    optimize_actions_frame = tk.Frame(simulation_section, bg=card_bg)
    optimize_actions_frame.grid(row=3, column=2, sticky='w', padx=(10,0), pady=(6,0))
    create_help_button(optimize_actions_frame, show_temp_info).pack(side='left', padx=(0,12))
    auto_optimize_check = tk.Checkbutton(
        optimize_actions_frame,
        text='Auto-optimize',
        variable=auto_optimize_interval_var,
        command=toggle_interval_entry,
        bg=card_bg,
        fg=label_color,
        font=('Segoe UI', 10, 'bold'),
        selectcolor=card_bg,
        activebackground=card_bg,
        activeforeground=label_color,
        cursor='hand2'
    )
    auto_optimize_check.pack(side='left', padx=(0,6))
    optimize_mode_var = tk.StringVar(value='Fast')
    optimize_mode_combo = ttk.Combobox(
        optimize_actions_frame,
        textvariable=optimize_mode_var,
        values=['Fast', 'Thorough'],
        state='readonly',
        width=9,
        font=('Segoe UI', 9)
    )
    optimize_mode_combo.pack(side='left', padx=(0,6))
    create_help_button(optimize_actions_frame, show_auto_optimize_info).pack(side='left')

    # Set initial state (enabled entry since auto_optimize defaults to False)
    toggle_interval_entry()
    
    def on_entry_change_run(event=None):
        try:
            v = float(temp_entry_var_run.get())
            if 200.0 <= v <= 1000.0:
                temp_var_run.set(v)
            else:
                temp_entry_var_run.set(f"{temp_var_run.get():.2f}")
        except Exception:
            temp_entry_var_run.set(f"{temp_var_run.get():.2f}")
    
    temp_entry_run.bind('<Return>', lambda e: on_entry_change_run())
    temp_entry_run.bind('<FocusOut>', lambda e: on_entry_change_run())

    ionizes_var_run = tk.BooleanVar(value=True)
    ionization_section = create_section(top_frame, '3 · Ionization & pKa Settings', row=3, column=0, columnspan=1)
    ionization_section.grid_columnconfigure(2, weight=1)
    tk.Label(ionization_section, text='Compound is an acid or base?', bg=card_bg, fg=label_color,
             font=('Segoe UI', 11, 'bold')).grid(row=0, column=0, sticky='w')
    ionization_frame = tk.Frame(ionization_section, bg=card_bg)
    ionization_frame.grid(row=0, column=1, columnspan=2, sticky='w', padx=(10,0))
    ionize_yes_rb = tk.Radiobutton(ionization_frame, text='Yes', variable=ionizes_var_run, value=True, bg=card_bg,
                                    fg=label_color, font=('Segoe UI', 11, 'bold'), activebackground=card_bg)
    ionize_yes_rb.pack(side='left', padx=10)
    ionize_no_rb = tk.Radiobutton(ionization_frame, text='No (treat as single species)', variable=ionizes_var_run, value=False,
                                   bg=card_bg, fg=label_color, font=('Segoe UI', 11, 'bold'), activebackground=card_bg)
    ionize_no_rb.pack(side='left', padx=10)

    pka_label = tk.Label(ionization_section, text='Compound pKa (blood pH: 7.4):', bg=card_bg, fg=label_color,
                         font=('Segoe UI', 11, 'bold'))
    pka_label.grid(row=1, column=0, sticky='w', pady=(6,0))
    pka_var_run = tk.StringVar()
    pka_entry_run = tk.Entry(ionization_section, textvariable=pka_var_run, width=12, font=body_font,
                             relief='solid', bd=1, highlightthickness=1, highlightbackground='#d0d0d0',
                             highlightcolor='#2E86DE')
    pka_entry_run.grid(row=1, column=1, sticky='w', padx=(4,4), pady=(6,0))

    ionization_mode_group = tk.Frame(ionization_section, bg=card_bg)
    ionization_mode_group.grid(row=1, column=2, sticky='w', padx=(8,0), pady=(6,0))
    ionization_mode_label = tk.Label(ionization_mode_group, text='Select ionization mode:', bg=card_bg, fg=label_color,
                                     font=('Segoe UI', 11, 'bold'))
    ionization_mode_label.pack(side='left', padx=(0,6))
    species_frame = tk.Frame(ionization_mode_group, bg=card_bg)
    species_frame.pack(side='left')
    is_acid_var_run = tk.BooleanVar(value=True)
    is_base_var_run = tk.BooleanVar(value=False)

    def toggle_species(selection):
        if selection == 'acid':
            if is_acid_var_run.get():
                is_base_var_run.set(False)
            elif not is_base_var_run.get():
                # Prevent both from being False; default back to acid
                is_acid_var_run.set(True)
        else:
            if is_base_var_run.get():
                is_acid_var_run.set(False)
            elif not is_acid_var_run.get():
                is_base_var_run.set(True)
    acid_checkbox = tk.Checkbutton(
        species_frame,
        text='Compound is an acid',
        variable=is_acid_var_run,
        onvalue=True,
        offvalue=False,
        bg=card_bg,
        fg='#8B1A1A',
        selectcolor=card_bg,
        font=('Segoe UI', 10, 'bold'),
        activebackground=card_bg,
        cursor='hand2',
        command=lambda: toggle_species('acid')
    )
    acid_checkbox.pack(side='left', padx=(0,16))
    base_checkbox = tk.Checkbutton(
        species_frame,
        text='Compound is a base',
        variable=is_base_var_run,
        onvalue=True,
        offvalue=False,
        bg=card_bg,
        fg='#1B4F72',
        selectcolor=card_bg,
        font=('Segoe UI', 10, 'bold'),
        activebackground=card_bg,
        cursor='hand2',
        command=lambda: toggle_species('base')
    )
    base_checkbox.pack(side='left')
    
    pmf_ionized_var_run = tk.StringVar()
    # Unified section for ionized and neutral files
    ionized_section = create_section(top_frame, '4 · Ionized and neutral files (auto-detected)', row=4, column=0, columnspan=1)
    ionized_section.grid_columnconfigure(1, weight=1)
    ionized_section.grid_columnconfigure(3, weight=1)
    # Row 0: ionized files
    ionized_pmf_label = tk.Label(ionized_section, text='Ionized PMF file:', bg=card_bg, fg=label_color, font=('Segoe UI', 10, 'bold'))
    ionized_pmf_label.grid(row=0, column=0, sticky='w')
    ionized_pmf_entry = tk.Entry(ionized_section, textvariable=pmf_ionized_var_run, width=16, font=body_font, state='readonly',
                                 readonlybackground=card_bg, relief='flat', bd=0, highlightthickness=0)
    ionized_pmf_entry.grid(row=0, column=1, sticky='ew', padx=(6,10))
    ionized_pullx_label = tk.Label(ionized_section, text='Ionized pullx.xvg file:', bg=card_bg, fg=label_color, font=('Segoe UI', 10, 'bold'))
    ionized_pullx_label.grid(row=0, column=2, sticky='w', padx=(12,0))
    ionized_pullx_var_run = tk.StringVar()
    ionized_pullx_entry = tk.Entry(ionized_section, textvariable=ionized_pullx_var_run, width=16, font=body_font, state='readonly',
                                   readonlybackground=card_bg, relief='flat', bd=0, highlightthickness=0)
    ionized_pullx_entry.grid(row=0, column=3, sticky='ew', padx=(6,0))

    regression_section = create_section(top_frame, '5 · Coefficients for empirical correction', row=6, column=0, columnspan=1)
    regression_section.grid_columnconfigure(5, weight=1)
    tk.Label(regression_section, text='LogBB regression:', bg=card_bg, fg=label_color,
             font=('Segoe UI', 11, 'bold')).grid(row=0, column=0, sticky='w')
    tk.Label(regression_section, text='Intercept', bg=card_bg, fg=label_color, font=('Segoe UI', 10)).grid(row=0, column=1, sticky='w', padx=(10,2))
    logbb_intercept_var = tk.StringVar(value=f"{LOGBB_INTERCEPT_DEFAULT:.4f}")
    logbb_intercept_entry = tk.Entry(regression_section, textvariable=logbb_intercept_var, width=10, font=body_font, relief='solid', bd=1,
                                     highlightthickness=1, highlightbackground='#d0d0d0', highlightcolor='#2E86DE')
    logbb_intercept_entry.grid(row=0, column=2, sticky='w')
    tk.Label(regression_section, text='Slope', bg=card_bg, fg=label_color, font=('Segoe UI', 10)).grid(row=0, column=3, sticky='w', padx=(12,2))
    logbb_slope_var = tk.StringVar(value=f"{LOGBB_SLOPE_DEFAULT:.4f}")
    logbb_slope_entry = tk.Entry(regression_section, textvariable=logbb_slope_var, width=10, font=body_font, relief='solid', bd=1,
                                 highlightthickness=1, highlightbackground='#d0d0d0', highlightcolor='#2E86DE')
    logbb_slope_entry.grid(row=0, column=4, sticky='w')

    regression_equation_label = tk.Label(regression_section, text='Linear regression for empirical correction:', bg=card_bg, fg=label_color,
                                         font=('Segoe UI', 10))
    regression_equation_label.grid(row=2, column=0, columnspan=2, sticky='w', pady=(6,0))
    logbb_equation_var = tk.StringVar(value=f"LogBB = (LogPeff - {LOGBB_INTERCEPT_DEFAULT:.4f}) / {LOGBB_SLOPE_DEFAULT:.4f}")
    logbb_equation_entry = tk.Entry(regression_section, textvariable=logbb_equation_var, width=28, font=body_font, relief='flat', bd=0,
                                    state='readonly', readonlybackground=card_bg, fg=label_color, borderwidth=0)
    logbb_equation_entry.grid(row=2, column=2, columnspan=4, sticky='ew', padx=(6,0), pady=(6,0))

    def apply_logbb_regression():
        try:
            intercept_val = float(logbb_intercept_var.get().strip())
            slope_val = float(logbb_slope_var.get().strip())
        except Exception:
            tk.messagebox.showerror('Regression error', 'Intercept and slope must be numeric values.')
            return False
        if slope_val == 0:
            tk.messagebox.showerror('Regression error', 'Slope must be non-zero.')
            return False
        logbb_intercept_var.set(f"{intercept_val:.4f}")
        logbb_slope_var.set(f"{slope_val:.4f}")
        logbb_equation_var.set(f"LogBB = (LogPeff - {intercept_val:.4f}) / {slope_val:.4f}")
        return True

    def reset_logbb_regression():
        logbb_intercept_var.set(f"{LOGBB_INTERCEPT_DEFAULT:.4f}")
        logbb_slope_var.set(f"{LOGBB_SLOPE_DEFAULT:.4f}")
        logbb_equation_var.set(
            f"LogBB = (LogPeff - {LOGBB_INTERCEPT_DEFAULT:.4f}) / {LOGBB_SLOPE_DEFAULT:.4f}"
        )

    regression_btns_frame = tk.Frame(regression_section, bg=card_bg)
    regression_btns_frame.grid(row=0, column=5, sticky='w', padx=(12,0))
    tk.Button(regression_btns_frame, text='Apply changes', command=apply_logbb_regression, fg='white', bg=browse_color,
              font=('Segoe UI', 10, 'bold'), relief='raised', bd=2, cursor='hand2', padx=8, pady=2,
              activebackground='#0d4266', activeforeground='white').pack(side='left', padx=(0,6))
    tk.Button(regression_btns_frame, text='Reset to defaults', command=reset_logbb_regression, fg='white', bg=browse_color,
              font=('Segoe UI', 10, 'bold'), relief='raised', bd=2, cursor='hand2', padx=8, pady=2,
              activebackground='#0d4266', activeforeground='white').pack(side='left')

    pmf_neutral_var_run = tk.StringVar()
    neutral_pullx_var_run = tk.StringVar()
    # Row 1: neutral files, inside the same unified section
    neutral_pmf_label = tk.Label(ionized_section, text='Neutral PMF file:', bg=card_bg, fg=label_color, font=('Segoe UI', 10, 'bold'))
    neutral_pmf_label.grid(row=1, column=0, sticky='w', pady=(4,0))
    pmf_neutral_entry = tk.Entry(ionized_section, textvariable=pmf_neutral_var_run, width=16, font=body_font, state='readonly',
                                 readonlybackground=card_bg, relief='flat', bd=0)
    pmf_neutral_entry.grid(row=1, column=1, sticky='ew', padx=(6,10), pady=(4,0))
    neutral_pullx_label = tk.Label(ionized_section, text='Neutral pullx.xvg file:', bg=card_bg, fg=label_color, font=('Segoe UI', 10, 'bold'))
    neutral_pullx_label.grid(row=1, column=2, sticky='w', padx=(12,0), pady=(4,0))
    neutral_pullx_entry = tk.Entry(ionized_section, textvariable=neutral_pullx_var_run, width=16, font=body_font, state='readonly',
                                   readonlybackground=card_bg, relief='flat', bd=0)
    neutral_pullx_entry.grid(row=1, column=3, sticky='ew', padx=(6,0), pady=(4,0))

    _responsive_layout_state = {'stage': 0, 'help_sz': 8}

    def _update_left_pane_responsive_layout(canvas_width):
        # 4 responsive stages based on exact measured section widths:
        # Stage 0 (>= 885px): all sections on single rows (reqwidth = 879px)
        # Stage 1 (805..884px): Section 3 ionization_mode_group wraps (reqwidth = 798px)
        # Stage 2 (600..804px): Section 2 & Section 5 action groups wrap (reqwidth = 593px)
        # Stage 3 (< 600px): Section 3, Section 4, and Section 5 sub-rows stack (reqwidth = 420px)
        if canvas_width >= 885:
            stage = 0
        elif canvas_width >= 805:
            stage = 1
        elif canvas_width >= 600:
            stage = 2
        else:
            stage = 3

        if _responsive_layout_state['stage'] != stage:
            _responsive_layout_state['stage'] = stage

            # Section 2 & Section 5 buttons wrap at stage >= 2 (< 805px)
            if stage >= 2:
                interval_actions_frame.grid_configure(row=2, column=0, columnspan=3, sticky='w', padx=(0,0), pady=(4,0))
                optimize_actions_frame.grid_configure(row=4, column=0, columnspan=3, sticky='w', padx=(0,0), pady=(4,0))
                regression_btns_frame.grid_configure(row=1, column=0, columnspan=5, sticky='w', padx=(0,0), pady=(6,0))
            else:
                interval_actions_frame.grid_configure(row=1, column=2, columnspan=1, sticky='w', padx=(10,0), pady=(6,0))
                optimize_actions_frame.grid_configure(row=3, column=2, columnspan=1, sticky='w', padx=(10,0), pady=(6,0))
                regression_btns_frame.grid_configure(row=0, column=5, columnspan=1, sticky='w', padx=(12,0), pady=(0,0))

            # Section 3, Section 4, and Section 5 equation wrap at stage 3 (< 600px) vs stage 1/2 vs stage 0
            if stage == 0:
                ionization_frame.grid_configure(row=0, column=1, columnspan=2, sticky='w', padx=(10,0), pady=(0,0))
                pka_label.grid_configure(row=1, column=0, sticky='w', pady=(6,0))
                pka_entry_run.grid_configure(row=1, column=1, sticky='w', padx=(4,4), pady=(6,0))
                ionization_mode_group.grid_configure(row=1, column=2, columnspan=1, sticky='w', padx=(8,0), pady=(6,0))
                ionization_mode_label.pack_configure(side='left', anchor='center', padx=(0,6), pady=(0,0))
                species_frame.pack_configure(side='left', anchor='center', pady=(0,0))
            elif stage in (1, 2):
                ionization_frame.grid_configure(row=0, column=1, columnspan=2, sticky='w', padx=(10,0), pady=(0,0))
                pka_label.grid_configure(row=1, column=0, sticky='w', pady=(6,0))
                pka_entry_run.grid_configure(row=1, column=1, sticky='w', padx=(4,4), pady=(6,0))
                ionization_mode_group.grid_configure(row=2, column=0, columnspan=3, sticky='w', padx=(0,0), pady=(6,0))
                ionization_mode_label.pack_configure(side='left', anchor='center', padx=(0,6), pady=(0,0))
                species_frame.pack_configure(side='left', anchor='center', pady=(0,0))
            else:
                ionization_frame.grid_configure(row=1, column=0, columnspan=3, sticky='w', padx=(0,0), pady=(4,0))
                pka_label.grid_configure(row=2, column=0, sticky='w', pady=(6,0))
                pka_entry_run.grid_configure(row=2, column=1, sticky='w', padx=(4,4), pady=(6,0))
                ionization_mode_group.grid_configure(row=3, column=0, columnspan=3, sticky='w', padx=(0,0), pady=(6,0))
                ionization_mode_label.pack_configure(side='top', anchor='w', padx=(0,0), pady=(0,2))
                species_frame.pack_configure(side='top', anchor='w', pady=(0,0))

            if stage == 3:
                ionized_pmf_label.grid_configure(row=0, column=0, sticky='w', pady=(0,0))
                ionized_pmf_entry.grid_configure(row=0, column=1, columnspan=3, sticky='ew', padx=(6,0), pady=(0,0))
                ionized_pullx_label.grid_configure(row=1, column=0, sticky='w', padx=(0,0), pady=(4,0))
                ionized_pullx_entry.grid_configure(row=1, column=1, columnspan=3, sticky='ew', padx=(6,0), pady=(4,0))
                neutral_pmf_label.grid_configure(row=2, column=0, sticky='w', pady=(4,0))
                pmf_neutral_entry.grid_configure(row=2, column=1, columnspan=3, sticky='ew', padx=(6,0), pady=(4,0))
                neutral_pullx_label.grid_configure(row=3, column=0, sticky='w', padx=(0,0), pady=(4,0))
                neutral_pullx_entry.grid_configure(row=3, column=1, columnspan=3, sticky='ew', padx=(6,0), pady=(4,0))

                regression_equation_label.grid_configure(row=2, column=0, columnspan=5, sticky='w', pady=(6,0))
                logbb_equation_entry.grid_configure(row=3, column=0, columnspan=5, sticky='ew', padx=(0,0), pady=(2,0))
            else:
                ionized_pmf_label.grid_configure(row=0, column=0, sticky='w', pady=(0,0))
                ionized_pmf_entry.grid_configure(row=0, column=1, columnspan=1, sticky='ew', padx=(6,10), pady=(0,0))
                ionized_pullx_label.grid_configure(row=0, column=2, sticky='w', padx=(12,0), pady=(0,0))
                ionized_pullx_entry.grid_configure(row=0, column=3, columnspan=1, sticky='ew', padx=(6,0), pady=(0,0))
                neutral_pmf_label.grid_configure(row=1, column=0, sticky='w', pady=(4,0))
                pmf_neutral_entry.grid_configure(row=1, column=1, columnspan=1, sticky='ew', padx=(6,10), pady=(4,0))
                neutral_pullx_label.grid_configure(row=1, column=2, sticky='w', padx=(12,0), pady=(4,0))
                neutral_pullx_entry.grid_configure(row=1, column=3, columnspan=1, sticky='ew', padx=(6,0), pady=(4,0))

                regression_equation_label.grid_configure(row=2, column=0, columnspan=2, sticky='w', pady=(6,0))
                logbb_equation_entry.grid_configure(row=2, column=2, columnspan=4, sticky='ew', padx=(6,0), pady=(6,0))

        new_padx = 6 if canvas_width < 600 else 8
        if _responsive_layout_state['help_sz'] != new_padx:
            _responsive_layout_state['help_sz'] = new_padx
            for btn in help_buttons:
                try:
                    btn.configure(padx=new_padx)
                except Exception:
                    pass

    def update_ionization_mode(*args):
        ionizes = ionizes_var_run.get()
        has_species = is_acid_var_run.get() or is_base_var_run.get()
        pka_state = 'normal' if (ionizes and has_species) else 'disabled'
        ionized_state = 'readonly' if ionizes else 'disabled'
        neutral_state = 'readonly'
        if not ionizes:
            pka_var_run.set('')
            is_acid_var_run.set(False)
            is_base_var_run.set(False)
        elif not has_species:
            pka_var_run.set('')
        if pka_entry_run:
            pka_entry_run.config(state=pka_state)
        for checkbox in (acid_checkbox, base_checkbox):
            checkbox.config(state='normal' if ionizes else 'disabled')
        ionized_pmf_entry.config(state=ionized_state)
        ionized_pullx_entry.config(state=ionized_state)
        pmf_neutral_entry.config(state=neutral_state)
        neutral_pullx_entry.config(state=neutral_state)

    ionizes_var_run.trace_add('write', lambda *args: update_ionization_mode())
    is_acid_var_run.trace_add('write', lambda *args: update_ionization_mode())
    is_base_var_run.trace_add('write', lambda *args: update_ionization_mode())
    update_ionization_mode()

    # Button frame anchored at bottom of controls column
    button_frame = tk.Frame(top_frame, bg=frame_color)
    # Stretch horizontally so inner content (start/stop) can be centered
    button_frame.grid(row=7, column=0, columnspan=1, sticky='ew', pady=(8,0))
    
    # Create primary action buttons (Start/Stop) with prominent styling
    def create_text_button(parent, text, bg_color, command=None, state='normal'):
        """Create a primary action button with filled background"""
        btn = tk.Button(
            parent,
            text=text,
            fg='white',
            bg=bg_color,
            font=('Segoe UI', 12, 'bold'),
            relief='raised',
            bd=2,
            cursor='hand2' if state == 'normal' else '',
            command=command,
            state=state,
            activebackground=bg_color,
            activeforeground='white',
            disabledforeground=disabled_fg_color,
            padx=16,
            pady=2
        )
        return btn
    
    # PMF browse buttons removed (auto-selection based on folder structure)

    # Single centered column for the main action buttons
    button_frame.grid_columnconfigure(0, weight=1)

    left_button_group = tk.Frame(button_frame, bg=frame_color)
    # Place start/stop buttons in the single centered column
    left_button_group.grid(row=0, column=0, pady=(0,4))

    start_button_run = create_text_button(left_button_group, 'Run calculation', success_color, state='normal')
    start_button_run.pack(side='left', padx=(0,10))
    
    stop_button_run = create_text_button(left_button_group, 'Stop calculation', danger_color, state='disabled')
    stop_button_run.pack(side='left', padx=(0,10))
    
    # Results display boxes for corrected LogPeff and LogBB
    results_frame = tk.Frame(top_frame, bg=frame_color)
    results_frame.grid(row=8, column=0, sticky='ew', padx=10, pady=(8,4))
    results_frame.grid_columnconfigure(0, weight=1)
    results_frame.grid_columnconfigure(1, weight=1)
    
    # LogPeff box
    logpeff_box = tk.LabelFrame(results_frame, text='Calculated LogPeff', font=('Segoe UI', 13, 'bold'), 
                                bg=card_bg, fg=label_color, relief='solid', borderwidth=2)
    logpeff_box.grid(row=0, column=0, sticky='ew', padx=(0,4), pady=0)
    logpeff_var = tk.StringVar(value='—')
    logpeff_display = tk.Label(logpeff_box, textvariable=logpeff_var, font=('Segoe UI', 18, 'bold'), 
                               fg='#D12F1D', bg=card_bg, justify='center', padx=10, pady=6)
    logpeff_display.pack(fill='both', expand=True)
    
    # LogBB box
    logbb_box = tk.LabelFrame(results_frame, text='Calculated LogBB', font=('Segoe UI', 13, 'bold'), 
                              bg=card_bg, fg=label_color, relief='solid', borderwidth=2)
    logbb_box.grid(row=0, column=1, sticky='ew', padx=(4,0), pady=0)
    logbb_var = tk.StringVar(value='—')
    logbb_display = tk.Label(logbb_box, textvariable=logbb_var, font=('Segoe UI', 18, 'bold'), 
                             fg="#D12F1D", bg=card_bg, justify='center', padx=10, pady=6)
    logbb_display.pack(fill='both', expand=True)

    # Log box frame with styling - added to right_column PanedWindow
    log_frame_run = tk.LabelFrame(right_column, text='Simulation Output', font=('Segoe UI', 11, 'bold'), fg=label_color, bg=frame_color, relief='solid', borderwidth=1)
    right_column.add(log_frame_run, minsize=140, stretch='always')
    log_frame_run.grid_rowconfigure(1, weight=1)
    log_frame_run.grid_columnconfigure(0, weight=1)
    log_frame_run.grid_columnconfigure(1, weight=0)
    
    # Toolbar for Simulation Output with easy Copy buttons
    log_toolbar = tk.Frame(log_frame_run, bg=frame_color)
    log_toolbar.grid(row=0, column=0, columnspan=2, sticky='ew', padx=6, pady=(3, 3))

    copy_btn = tk.Button(
        log_toolbar,
        text='📋 Copy Output',
        font=('Segoe UI', 9, 'bold'),
        bg='#e8f0fe',
        fg='#1a73e8',
        activebackground='#d2e3fc',
        activeforeground='#174ea6',
        relief='flat',
        bd=1,
        cursor='hand2',
        padx=8,
        pady=1
    )
    copy_btn.pack(side='left', padx=(0, 6))

    copy_sel_btn = tk.Button(
        log_toolbar,
        text='Copy Selection',
        font=('Segoe UI', 9),
        bg='#f1f3f4',
        fg=label_color,
        activebackground='#e8eaed',
        relief='flat',
        bd=1,
        cursor='hand2',
        padx=8,
        pady=1
    )
    copy_sel_btn.pack(side='left', padx=(0, 6))

    clear_log_btn = tk.Button(
        log_toolbar,
        text='Clear Output',
        font=('Segoe UI', 9),
        bg='#f1f3f4',
        fg='#5f6368',
        activebackground='#e8eaed',
        relief='flat',
        bd=1,
        cursor='hand2',
        padx=8,
        pady=1
    )
    clear_log_btn.pack(side='left')

    log_box_run = tk.Text(
        log_frame_run,
        width=1,
        height=1,
        bg='#fafafa',
        fg='#2c3e50',
        font=('Consolas', 10),
        relief='flat',
        borderwidth=0,
        highlightthickness=0,
        state='normal',
        wrap='word',
        padx=6,
        pady=4
    )
    log_v_scroll = ttk.Scrollbar(log_frame_run, orient='vertical', command=log_box_run.yview)
    log_box_run.configure(yscrollcommand=log_v_scroll.set)
    log_box_run.grid(row=1, column=0, sticky='nsew', padx=(4, 0), pady=4)
    log_v_scroll.grid(row=1, column=1, sticky='ns', padx=(0, 4), pady=4)
    
    def copy_to_system_clipboard(text):
        if not text:
            return False
        copied = False
        try:
            import win32clipboard
            win32clipboard.OpenClipboard()
            win32clipboard.EmptyClipboard()
            win32clipboard.SetClipboardText(text, win32clipboard.CF_UNICODETEXT)
            win32clipboard.CloseClipboard()
            copied = True
        except Exception:
            pass
        try:
            root_run.clipboard_clear()
            root_run.clipboard_append(text)
            root_run.update_idletasks()
            copied = True
        except Exception:
            pass
        return copied

    def _flash_copied_feedback(button_widget, message):
        orig_text = button_widget.cget('text')
        orig_fg = button_widget.cget('fg')
        button_widget.config(text=f'✓ {message}', fg='#137333')
        root_run.after(1500, lambda: button_widget.config(text=orig_text, fg=orig_fg))

    def copy_selection(event=None):
        """Copy selected text to clipboard (or all text if none selected)"""
        try:
            selected_text = log_box_run.get(tk.SEL_FIRST, tk.SEL_LAST)
        except tk.TclError:
            selected_text = ""
        if not selected_text:
            selected_text = log_box_run.get('1.0', tk.END).strip()
        if selected_text:
            copy_to_system_clipboard(selected_text)
            _flash_copied_feedback(copy_sel_btn, 'Copied!')
        return 'break'

    def copy_all_text(event=None):
        """Copy all text in the log box to clipboard"""
        all_text = log_box_run.get('1.0', tk.END).strip()
        if all_text:
            copy_to_system_clipboard(all_text)
            _flash_copied_feedback(copy_btn, 'Copied!')
        return 'break'

    def clear_log(event=None):
        log_box_run.delete('1.0', tk.END)

    def select_all(event=None):
        """Select all text in the log box"""
        log_box_run.tag_add(tk.SEL, '1.0', tk.END)
        log_box_run.mark_set(tk.INSERT, '1.0')
        log_box_run.see(tk.INSERT)
        return 'break'

    copy_btn.config(command=copy_all_text)
    copy_sel_btn.config(command=copy_selection)
    clear_log_btn.config(command=clear_log)

    # Right-click context menu for log box
    log_context_menu = tk.Menu(log_box_run, tearoff=0)
    log_context_menu.add_command(label='Copy Selection', command=copy_selection)
    log_context_menu.add_command(label='Copy All Output', command=copy_all_text)
    log_context_menu.add_separator()
    log_context_menu.add_command(label='Select All', command=select_all)
    log_context_menu.add_command(label='Clear Output', command=clear_log)

    def show_log_context_menu(event):
        try:
            has_sel = bool(log_box_run.tag_ranges(tk.SEL))
            if has_sel:
                log_context_menu.entryconfig('Copy Selection', state='normal')
            else:
                log_context_menu.entryconfig('Copy Selection', state='disabled')
            log_context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            log_context_menu.grab_release()

    # Bind right-click and keyboard shortcuts (Windows, Linux, and macOS)
    log_box_run.bind('<Button-3>', show_log_context_menu)
    log_box_run.bind('<Control-c>', copy_selection)
    log_box_run.bind('<Control-C>', copy_selection)
    log_box_run.bind('<Control-Insert>', copy_selection)
    log_box_run.bind('<Control-a>', select_all)
    log_box_run.bind('<Control-A>', select_all)
    if sys.platform == 'darwin':
        log_box_run.bind('<Button-2>', show_log_context_menu)
        log_box_run.bind('<Control-Button-1>', show_log_context_menu)
        log_box_run.bind('<Command-c>', copy_selection)
        log_box_run.bind('<Command-C>', copy_selection)
        log_box_run.bind('<Command-a>', select_all)
        log_box_run.bind('<Command-A>', select_all)
    
    # Configure text tags for colored output
    log_box_run.tag_config('red', foreground='#E74C3C', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('green', foreground='#27AE60', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('blue', foreground='#2E86DE', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('cyan', foreground='#17A2B8', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('yellow', foreground='#F1C40F', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('orange', foreground='#E67E22', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('purple', foreground='#8E44AD', font=('Consolas', 10, 'bold'))
    log_box_run.tag_config('bold', font=('Consolas', 10, 'bold'))
    # Add special tag for LogBB highlighting with larger font
    log_box_run.tag_config('logbb_highlight', foreground='#C0392B', font=('Consolas', 12, 'bold'))

    # Plot frame with styling - added to right_column PanedWindow
    plot_container = tk.LabelFrame(right_column, text='Simulation Plots', font=('Segoe UI', 11, 'bold'), fg=label_color, bg=frame_color, relief='solid', borderwidth=1)
    right_column.add(plot_container, minsize=180, stretch='always')
    
    # Create a border frame to hold the canvas
    canvas_border_frame = tk.Frame(plot_container, bg='#d0d0d0', bd=1, relief='solid')
    canvas_border_frame.pack(side='top', fill='both', expand=True, padx=5, pady=5)
    
    plot_canvas = tk.Canvas(canvas_border_frame, bg='white', relief='flat', borderwidth=0, highlightthickness=0)
    v_scrollbar = tk.Scrollbar(canvas_border_frame, orient='vertical', command=plot_canvas.yview, bg=bg_color)
    h_scrollbar = tk.Scrollbar(canvas_border_frame, orient='horizontal', command=plot_canvas.xview, bg=bg_color)
    plot_canvas.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
    
    v_scrollbar.pack(side='right', fill='y')
    h_scrollbar.pack(side='bottom', fill='x')
    plot_canvas.pack(side='top', fill='both', expand=True)
    
    plot_frame_run = tk.Frame(plot_canvas, bg='white')
    plot_canvas.create_window((0, 0), window=plot_frame_run, anchor='nw')
    
    # Configure grid for centered content
    plot_frame_run.grid_columnconfigure(0, weight=1)
    plot_frame_run.grid_columnconfigure(1, weight=1)
    plot_frame_run.grid_rowconfigure(0, weight=1)
    
    def configure_scroll_region(event=None):
        plot_canvas.configure(scrollregion=plot_canvas.bbox('all'))
    
    plot_frame_run.bind('<Configure>', configure_scroll_region)
    
    # Mouse wheel scrolling support - responsive scrolling
    def _on_mousewheel(event):
        """Handle mouse wheel scrolling - vertical"""
        try:
            if event.delta:  # Windows
                direction = -1 if event.delta > 0 else 1
            else:  # Linux
                direction = -1 if event.num == 4 else 1
            plot_canvas.yview_scroll(direction * 3, 'units')
        except Exception:
            pass
    
    def _on_shift_mousewheel(event):
        """Handle shift+wheel scrolling - horizontal"""
        try:
            if event.delta:  # Windows
                direction = -1 if event.delta > 0 else 1
            else:  # Linux
                direction = -1 if event.num == 4 else 1
            plot_canvas.xview_scroll(direction * 3, 'units')
        except Exception:
            pass
    
    def _bind_scroll_events(widget):
        """Recursively bind scroll events to widget and all children"""
        widget.bind('<MouseWheel>', _on_mousewheel, add='+')
        widget.bind('<Shift-MouseWheel>', _on_shift_mousewheel, add='+')
        widget.bind('<Button-4>', _on_mousewheel, add='+')
        widget.bind('<Button-5>', _on_mousewheel, add='+')
        widget.bind('<Shift-Button-4>', _on_shift_mousewheel, add='+')
        widget.bind('<Shift-Button-5>', _on_shift_mousewheel, add='+')
        
        def on_enter(event):
            widget.focus_set()
        
        widget.bind('<Enter>', on_enter, add='+')
        
        # Recursively bind to all children
        for child in widget.winfo_children():
            _bind_scroll_events(child)
    
    # Bind scroll events to canvas and all its children
    _bind_scroll_events(plot_canvas)
    _bind_scroll_events(plot_frame_run)

    # Status bar with centered label (zero <Configure> overhead during maximize/restore)
    status_frame = tk.Frame(root_run, bg=primary_color)
    status_frame.grid(row=1, column=0, columnspan=2, sticky='ew', padx=20, pady=2)

    status_inner_label = tk.Label(
        status_frame,
        text='Status: Idle',
        font=('Segoe UI', 11, 'bold'),
        fg='white',
        bg=primary_color,
        anchor='center',
        pady=2
    )
    status_inner_label.pack(fill='x', expand=True)

    class StatusLabel:
        def config(self, text=None, bg=None, fg=None, **kwargs):
            if text is not None:
                status_inner_label.config(text=text)
            if bg is not None:
                status_inner_label.config(bg=bg)
                status_frame.config(bg=bg)
            elif text is not None:
                status_inner_label.config(bg=primary_color)
                status_frame.config(bg=primary_color)
            if fg is not None:
                status_inner_label.config(fg=fg)

    status_label_run = StatusLabel()

    # End program button below status bar
    def end_program():
        root_run.quit()
        root_run.destroy()
    
    end_button_frame = tk.Frame(root_run, bg=bg_color)
    end_button_frame.grid(row=2, column=0, columnspan=2, pady=(2, 6), sticky='ew')
    
    end_button_run = tk.Button(end_button_frame, text='End program', fg="#AF2617", bg=bg_color, font=('Segoe UI', 12, 'bold'), 
                               relief='flat', bd=0, cursor='hand2', command=end_program)
    end_button_run.pack(side='top')

    # Native resize grip in the bottom-right corner
    sizegrip = ttk.Sizegrip(end_button_frame)
    sizegrip.pack(side='right', anchor='se', padx=2, pady=2)

    _log_queue = queue.Queue()
    _ui_action_queue = queue.Queue()
    _main_thread_id = threading.get_ident()
    _log_flush_scheduled = [False]

    def _flush_log_queue():
        _log_flush_scheduled[0] = False
        if not log_box_run.winfo_exists():
            return
        while True:
            try:
                fn = _ui_action_queue.get_nowait()
            except queue.Empty:
                break
            try:
                fn()
            except Exception:
                pass
        inserted = False
        for _ in range(250):
            try:
                msg, color, bold = _log_queue.get_nowait()
            except queue.Empty:
                break
            if bold and color:
                log_box_run.insert(tk.END, msg + '\n', color)
            elif bold:
                log_box_run.insert(tk.END, msg + '\n', 'bold')
            elif color:
                log_box_run.insert(tk.END, msg + '\n', color)
            else:
                log_box_run.insert(tk.END, msg + '\n')
            inserted = True
        if inserted:
            try:
                if root_run.state() != 'iconic':
                    log_box_run.see(tk.END)
            except Exception:
                pass
        worker_alive = bool(proc_holder_run.get('thread') and proc_holder_run['thread'].is_alive())
        if (not _log_queue.empty() or not _ui_action_queue.empty() or worker_alive) and not _log_flush_scheduled[0]:
            _log_flush_scheduled[0] = True
            root_run.after(30, _flush_log_queue)

    def append_log_run(msg, color=None, bold=False):
        """Thread-safe batched log append to prevent event-queue flooding on restore/maximize"""
        _log_queue.put((msg, color, bold))
        if threading.get_ident() == _main_thread_id and not _log_flush_scheduled[0]:
            _log_flush_scheduled[0] = True
            try:
                root_run.after(25, _flush_log_queue)
            except Exception:
                pass

    # Std redirect
    orig_stdout = sys.stdout
    orig_stderr = sys.stderr
    class StdRedirectorRun:
        def __init__(self, write_func, orig=None, prefix=''):
            self.write_func = write_func
            self.orig = orig
            self.prefix = prefix
            self._buffer = ''
        def write(self, s):
            if not s:
                return
            if self.orig:
                try:
                    self.orig.write(s)
                except Exception:
                    pass
            self._buffer += s
            while '\n' in self._buffer:
                line, self._buffer = self._buffer.split('\n', 1)
                try:
                    self.write_func(self.prefix + line)
                except Exception:
                    pass
        def flush(self):
            if self._buffer:
                try:
                    self.write_func(self.prefix + self._buffer)
                finally:
                    self._buffer = ''
            if self.orig:
                try:
                    self.orig.flush()
                except Exception:
                    pass
    sys.stdout = StdRedirectorRun(lambda m: append_log_run(m, 'red' if ('LogBB' in m or 'Peff' in m) else None), orig=orig_stdout)
    sys.stderr = StdRedirectorRun(lambda m: append_log_run(m), orig=orig_stderr, prefix='[ERR] ')

    proc_holder_run = {}

    def clear_run_outputs():
        """Reset logs and graphs before starting a new calculation (must run on main GUI thread)."""
        while not _log_queue.empty():
            try:
                _log_queue.get_nowait()
            except queue.Empty:
                break
        # Close previously embedded matplotlib figures
        current_figs = proc_holder_run.get('figures')
        if current_figs:
            for fig in current_figs:
                try:
                    fig.clf()
                    plt.close(fig)
                except Exception:
                    pass
            proc_holder_run['figures'] = []

        # Remove graph widgets from the canvas frame
        for child in plot_frame_run.winfo_children():
            try:
                child.destroy()
            except Exception:
                pass
        try:
            bbox = plot_canvas.bbox('all') or (0, 0, 0, 0)
            plot_canvas.configure(scrollregion=bbox)
        except Exception:
            pass

        # Clear the log text widget
        try:
            log_box_run.delete('1.0', tk.END)
        except Exception:
            pass

        # Reset result display boxes
        logpeff_var.set('—')
        logbb_var.set('—')

        # Clear the terminal/console window without spawning a blocking shell process
        try:
            if orig_stdout:
                orig_stdout.write('\033[2J\033[H')
                orig_stdout.flush()
        except Exception:
            pass

    def create_graph_context_menu(canvas_widget, figure, graph_name):
        """Create right-click context menu for graph"""
        menu = tk.Menu(canvas_widget, tearoff=0)
        
        def save_as_image():
            filetypes = [
                ('PNG files', '*.png'),
                ('PDF files', '*.pdf'),
                ('SVG files', '*.svg'),
                ('JPEG files', '*.jpg'),
                ('All files', '*.*')
            ]
            filepath = filedialog.asksaveasfilename(
                defaultextension='.png',
                filetypes=filetypes,
                initialfile=f'{graph_name}.png',
                title=f'Save {graph_name}'
            )
            if filepath:
                try:
                    figure.savefig(filepath, dpi=300, bbox_inches='tight')
                    append_log_run(f'Graph saved: {filepath}')
                except Exception as e:
                    append_log_run(f'Failed to save graph: {e}')
        
        def copy_to_clipboard():
            try:
                import io
                buf = io.BytesIO()
                figure.savefig(buf, format='png', dpi=150, bbox_inches='tight')
                buf.seek(0)
                img = Image.open(buf)
                
                # Copy to clipboard (Windows, macOS, Linux, with temp-file fallback)
                try:
                    import win32clipboard
                    output = io.BytesIO()
                    img.convert('RGB').save(output, 'BMP')
                    data = output.getvalue()[14:]  # Remove BMP header
                    output.close()
                    
                    win32clipboard.OpenClipboard()
                    win32clipboard.EmptyClipboard()
                    win32clipboard.SetClipboardData(win32clipboard.CF_DIB, data)
                    win32clipboard.CloseClipboard()
                    append_log_run(f'{graph_name} copied to clipboard')
                except ImportError:
                    import tempfile
                    temp_path = os.path.join(tempfile.gettempdir(), f'{graph_name}_temp.png')
                    figure.savefig(temp_path, dpi=150, bbox_inches='tight')
                    copied_external = False
                    if sys.platform == 'darwin':
                        res_clip = subprocess.run(
                            ['osascript', '-e', f'set the clipboard to (read (POSIX file "{temp_path}") as «class PNGf»)'],
                            capture_output=True
                        )
                        copied_external = (res_clip.returncode == 0)
                    elif sys.platform.startswith('linux'):
                        for cmd in (
                            ['xclip', '-selection', 'clipboard', '-t', 'image/png', '-i', temp_path],
                            ['wl-copy', '--type', 'image/png']
                        ):
                            try:
                                if cmd[0] == 'wl-copy':
                                    with open(temp_path, 'rb') as f_png:
                                        res_clip = subprocess.run(cmd, stdin=f_png, capture_output=True)
                                else:
                                    res_clip = subprocess.run(cmd, capture_output=True)
                                if res_clip.returncode == 0:
                                    copied_external = True
                                    break
                            except FileNotFoundError:
                                continue
                    if copied_external:
                        append_log_run(f'{graph_name} copied to clipboard')
                    else:
                        append_log_run(f'{graph_name} saved to: {temp_path}')
            except Exception as e:
                append_log_run(f'Failed to copy graph: {e}')
        
        menu.add_command(label='Save as Image...', command=save_as_image)
        menu.add_command(label='Copy to Clipboard', command=copy_to_clipboard)
        
        def show_menu(event):
            menu.tk_popup(event.x_root, event.y_root)
        
        canvas_widget.bind('<Button-3>', show_menu)  # Right-click
        if sys.platform == 'darwin':
            canvas_widget.bind('<Button-2>', show_menu)
            canvas_widget.bind('<Control-Button-1>', show_menu)
        return menu

    def do_run():
        # Pre-check that run_simulation exists
        rs = globals().get('run_simulation')
        if not callable(rs):
            tk.messagebox.showerror('Error', 'Internal function run_simulation not available. Please run smoke-test or restart the script.')
            append_log_run('ERROR: run_simulation not available in globals')
            return

        folder = folder_var.get().strip()
        if not folder:
            tk.messagebox.showerror('Error', 'Select a simulation folder first')
            return
        
        # Check if temperature input is empty or invalid
        temp_input = temp_entry_var_run.get().strip()
        if not temp_input or temp_input == "0.00":
            tk.messagebox.showwarning('Warning', 'Temperature field is empty. Please enter a temperature value in Kelvin.')
            return
        
        try:
            Tval = float(temp_input)
            if Tval < 200.0 or Tval > 1000.0:
                tk.messagebox.showerror('Error', 'Temperature must be between 200 K and 1000 K')
                return
        except Exception:
            tk.messagebox.showerror('Error', 'Temperature must be numeric')
            return

        interval_input = interval_size_var_run.get().strip()
        
        # Check if auto-optimize is enabled
        if auto_optimize_interval_var.get():
            precomputed = recommended_interval_points_run.get()
            if precomputed and precomputed > 0:
                interval_size_points = precomputed
            else:
                interval_size_points = 0  # Fallback: optimise during the run
        else:
            try:
                interval_size_points = int(float(interval_input))
                if interval_size_points <= 0:
                    raise ValueError('Interval size must be positive')
            except Exception:
                tk.messagebox.showerror('Error', 'Interval size must be a positive integer (points).')
                return
        
            if interval_size_points > 15000:
                response = tk.messagebox.askquestion(
                    'Large Interval Size Warning',
                    f'Interval size ({interval_size_points} points) is very large and may lead to:\n\n'
                    '• Too few blocks per window for reliable averaging\n'
                    '• Unreliable diffusion coefficient estimates\n'
                    '• Potential calculation errors\n\n'
                    'Recommended: 500-5000 points for typical simulations.\n\n'
                    'Do you want to continue anyway?',
                    icon='warning'
                )
                if response != 'yes':
                    return
        
        ionizes_significant = ionizes_var_run.get()
        pka = pka_var_run.get().strip() or None
        is_acid = is_acid_var_run.get() if ionizes_significant else False
        is_base = is_base_var_run.get() if ionizes_significant else False
        if not ionizes_significant:
            pka = None
        
        if not apply_logbb_regression():
            return

        regression_intercept = float(logbb_intercept_var.get().strip())
        regression_slope = float(logbb_slope_var.get().strip())

        pmf_ion = pmf_ionized_var_run.get().strip() or None
        pmf_neutral_auto = pmf_neutral_var_run.get().strip() or None

        def valid_auto_path(path):
            return bool(path) and not path.startswith('No ')

        if ionizes_significant and (is_acid or is_base):
            pmf = pmf_ion if valid_auto_path(pmf_ion) else None
            pmf_neutral = pmf_neutral_auto if valid_auto_path(pmf_neutral_auto) else None
        else:
            pmf = pmf_neutral_auto if valid_auto_path(pmf_neutral_auto) else (pmf_ion if valid_auto_path(pmf_ion) else None)
            pmf_neutral = None

        if ionizes_significant and (is_acid or is_base):
            if not pmf:
                tk.messagebox.showerror('Error', 'Auto PMF (ionized) not found in ionized subfolder (required).')
                return
            if not pmf_neutral:
                tk.messagebox.showerror('Error', 'Auto PMF (neutral) not found in neutral subfolder (required for correction).')
                return
            if not pka:
                tk.messagebox.showerror('Error', 'Enter a pKa value for acid/base correction (required).')
                return
        elif not pmf:
            tk.messagebox.showerror('Error', 'No PMF file detected. Provide at least one PMF (neutral or ionized).')
            return
        
        def find_umbrella_folder(options):
            for folder_type, path in options:
                if os.path.isdir(path):
                    return folder_type, path
            return None, None

        if ionizes_significant and (is_acid or is_base):
            umbrella_type, umbrella_folder = find_umbrella_folder([
                ('ionized', os.path.join(folder, 'ionized'))
            ])
            if not umbrella_folder:
                tk.messagebox.showerror('Error', 'Required subfolder not found: ionized/')
                return
        else:
            search_order = [
                ('neutral', os.path.join(folder, 'neutral')),
                ('ionized', os.path.join(folder, 'ionized')),
                ('main', folder)
            ]
            umbrella_type, umbrella_folder = find_umbrella_folder(search_order)
            if not umbrella_folder:
                tk.messagebox.showerror('Error', 'No umbrella sampling folder found (checked ionized/, neutral/, and main folder).')
                return
        
        monitor_flag = True
        ionized_arg = umbrella_folder if umbrella_type == 'ionized' else None
        neutral_arg = umbrella_folder if umbrella_type in ('neutral', 'main') else None
        neutral_data_folder = os.path.join(folder, 'neutral')
        if not os.path.isdir(neutral_data_folder):
            neutral_data_folder = None
        opt_mode = optimize_mode_var.get().lower()

        clear_run_outputs()
        if pmf_neutral_auto and pmf_neutral_auto.startswith('No neutral'):
            append_log_run('Check your folder structure', color='red')
        status_label_run.config(text='Status: Running...', bg=success_color, fg='white')
        start_button_run.config(state='disabled')
        stop_button_run.config(state='normal')
        auto_optimize_check.config(state='disabled')
        optimize_mode_combo.config(state='disabled')

        stop_event = threading.Event()
        proc_holder_run['stop_event'] = stop_event

        def gui_logger(m=None, tag=None, bold=None):
            append_log_run(m if m is not None else "", color=tag, bold=bool(bold))
            if m:
                if 'Corrected LogPeff:' in m and tag == 'red':
                    try:
                        value_str = m.split('Corrected LogPeff:')[1].strip()
                        _ui_action_queue.put(lambda v=value_str: logpeff_var.set(v))
                    except Exception:
                        pass
                elif m.startswith('LogPeff:') and tag == 'red':
                    try:
                        value_str = m.split('LogPeff:')[1].strip()
                        _ui_action_queue.put(lambda v=value_str: logpeff_var.set(v))
                    except Exception:
                        pass
                elif 'LogBB (corrected):' in m and tag == 'logbb_highlight':
                    try:
                        value_str = m.split('LogBB (corrected):')[1].strip().rstrip('|').strip()
                        _ui_action_queue.put(lambda v=value_str: logbb_var.set(v))
                    except Exception:
                        pass
                elif 'LogBB:' in m and m.startswith('|') and tag == 'logbb_highlight':
                    try:
                        value_str = m.split('LogBB:')[1].strip().rstrip('|').strip()
                        _ui_action_queue.put(lambda v=value_str: logbb_var.set(v))
                    except Exception:
                        pass

        def _finish_on_main_thread(res, err):
            try:
                _flush_log_queue()
                if err is not None:
                    append_log_run(f'Runtime error: {err}')
                elif res is None:
                    append_log_run('Simulation did not produce results or was stopped')
                else:
                    for child in plot_frame_run.winfo_children():
                        child.destroy()

                    graph_names = res.get('graph_names') or []
                    row_map = {}
                    next_row = 0

                    for i, fig in enumerate(res['figs']):
                        canvas = FigureCanvasTkAgg(fig, master=plot_frame_run)
                        canvas.draw_idle()
                        widget = canvas.get_tk_widget()
                        graph_name = graph_names[i] if i < len(graph_names) else f'graph_{i+1}'

                        base_name = graph_name.split('_', 1)[1] if '_' in graph_name else graph_name
                        is_neutral = 'Neutral' in graph_name
                        is_ionized = 'Ionized' in graph_name

                        if is_ionized:
                            row = row_map.setdefault(base_name, next_row)
                            if row == next_row:
                                next_row += 1
                            col = 0
                        elif is_neutral:
                            row = row_map.get(base_name)
                            if row is None:
                                row = row_map.setdefault(base_name, next_row)
                                next_row += 1
                            col = 1
                        else:
                            row = next_row
                            next_row += 1
                            col = 0

                        widget.grid(row=row, column=col, padx=10, pady=10, sticky='nsew')
                        create_graph_context_menu(widget, fig, graph_name)
                        _bind_scroll_events(widget)

                    proc_holder_run['figures'] = list(res['figs'])
                    plot_frame_run.update_idletasks()
                    plot_canvas.configure(scrollregion=plot_canvas.bbox('all'))

                    append_log_run('\n' + '='*60, color='cyan')
                    append_log_run('Calculation finished successfully.', color='cyan')
                    append_log_run('You can perform another calculation or close the program.', color='cyan')
                    append_log_run('='*60, color='cyan')
            finally:
                stop_event.set()
                start_button_run.config(state='normal')
                stop_button_run.config(state='disabled')
                auto_optimize_check.config(state='normal')
                if auto_optimize_interval_var.get():
                    optimize_mode_combo.config(state='readonly')
                status_label_run.config(text='Status: Idle', bg=primary_color, fg='white')

        def _compute_worker():
            res = None
            err = None
            try:
                if ionizes_significant and (is_acid or is_base):
                    res = rs(
                        folder,
                        Tval,
                        pmf_path=pmf,
                        pmf_neutral_path=pmf_neutral,
                        pKa=pka,
                        is_acid=is_acid,
                        is_base=is_base,
                        monitor=monitor_flag,
                        logger=gui_logger,
                        stop_event=stop_event,
                        ionized_folder=umbrella_folder,
                        neutral_folder=neutral_data_folder,
                        regression_intercept=regression_intercept,
                        regression_slope=regression_slope,
                        interval_size_points=interval_size_points,
                        optimize_mode=opt_mode
                    )
                else:
                    res = rs(
                        folder,
                        Tval,
                        pmf_path=pmf,
                        pmf_neutral_path=pmf_neutral,
                        pKa=pka,
                        is_acid=is_acid,
                        is_base=is_base,
                        monitor=monitor_flag,
                        logger=gui_logger,
                        stop_event=stop_event,
                        ionized_folder=ionized_arg,
                        neutral_folder=neutral_arg,
                        regression_intercept=regression_intercept,
                        regression_slope=regression_slope,
                        interval_size_points=interval_size_points,
                        optimize_mode=opt_mode
                    )
            except Exception as e:
                err = e
            _ui_action_queue.put(lambda r=res, ex=err: _finish_on_main_thread(r, ex))

        t = threading.Thread(target=_compute_worker, daemon=True)
        proc_holder_run['thread'] = t
        t.start()
        if not _log_flush_scheduled[0]:
            _log_flush_scheduled[0] = True
            root_run.after(25, _flush_log_queue)

    def do_stop():
        se = proc_holder_run.get('stop_event')
        if se:
            append_log_run('Stop requested...')
            se.set()
            status_label_run.config(text='Status: Stopping...', bg='#E67E22', fg='white')
        else:
            append_log_run('No active run to stop')

    def restore_and_close_run():
        try:
            sys.stdout.flush()
            sys.stderr.flush()
        except Exception:
            pass
        sys.stdout = orig_stdout
        sys.stderr = orig_stderr
        root_run.destroy()

    start_button_run.config(command=do_run)
    stop_button_run.config(command=do_stop)
    root_run.protocol("WM_DELETE_WINDOW", restore_and_close_run)
    _bind_controls_scroll_events(left_container)

    def _set_initial_sash():
        try:
            root_run.update_idletasks()
            for _w in (
                root_run,
                main_paned,
                left_container,
                controls_canvas,
                top_frame,
                right_column,
                log_frame_run,
                log_box_run,
                plot_container,
                plot_canvas,
            ):
                _set_win32_class_bg(_w, '#fafafa')

            # Force Stage 0 (full 1-row layout) before measuring required left width
            _update_left_pane_responsive_layout(2000)
            root_run.update()
            total_w = main_paned.winfo_width()
            if total_w <= 1:
                total_w = init_width
            needed_left = top_frame.winfo_reqwidth() + controls_scrollbar.winfo_reqwidth() + 26
            sash_x = max(needed_left, int(total_w * 0.59))
            sash_x = min(sash_x, max(500, total_w - 340))

            right_h = right_column.winfo_height()
            if right_h > 200:
                right_column.sash_place(0, 0, max(160, int(right_h * 0.44)))
                root_run.update()

            main_paned.sash_place(0, sash_x, 0)
            root_run.update()
            canvas_w = max(120, controls_canvas.winfo_width())
            _last_controls_width[0] = canvas_w
            _update_left_pane_responsive_layout(canvas_w)
            controls_canvas.itemconfig(top_frame_window, width=canvas_w)
            controls_canvas.configure(scrollregion=controls_canvas.bbox('all'))
        except Exception:
            pass

    root_run.after(20, _set_initial_sash)
    root_run.mainloop()

if not args.smoke_test:
    start_run_window()
    sys.exit(0)