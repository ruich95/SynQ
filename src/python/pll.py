from typing import Callable
import numpy as np

def nco_gen(initial_phase: float = 0,
            lut_size: int        = 2**14,
            phase_acc_width: int = 24) -> Callable[[np.uint32], np.uint16]:

  msk = (2 ** phase_acc_width) - 1
  phase_acc_val = np.uint32(initial_phase * (2 ** phase_acc_width))
  lut = np.uint16((-1 * np.sin(np.linspace(0, 1, lut_size) * 2 * np.pi))  * ((2**15) - 1) + (2**15))

  def nco(step: np.uint32) -> np.uint16:
    nonlocal phase_acc_val

    # next acc value
    phase_acc_val = ((phase_acc_val & msk) + (step & msk)) & msk

    # the index (higher 14 bits) of a waveform lut
    output_idx = (phase_acc_val & msk) >> 10

    return lut[output_idx]

  return nco

def dff_gen()-> Callable[[bool, bool, bool], bool]:
  prev_out: bool = False
  prev_clk: bool = False

  def dff(input: bool, clear :bool, clk: bool) -> bool:
    nonlocal prev_out
    nonlocal prev_clk
    if clk and (not prev_clk):
      output   = 0 if clear else input
      prev_out = output
      prev_clk = clk
      return output

    prev_clk = clk
    prev_out = 0 if clear else prev_out
    return prev_out

  return dff

def lpf1_gen():
  prev_out: np.int16 = 0 # s1q14

  def lpf(input: np.int8) -> np.int16:
    nonlocal prev_out
    # only accept +/-1 (+/- 1/64 under s1q14) or 0 as input
    if input > 0:
      input = 256
    elif input < 0:
      input = -256
    else:
      input = 0

    # (y[n] = 31/32 * y[n-1] + 1/32 x[n])
    if prev_out >= 0:
      output = (prev_out - (prev_out >> 6)) + input
    else:
      prev_out *= -1
      output = input - (prev_out - (prev_out >> 6))

    prev_out = output
    return output
  return lpf

def pfd_gen():
  dff_a = dff_gen()
  dff_b = dff_gen()
  prev_clear: bool = False

  def pfd(a: bool, b: bool) -> np.int16:
    nonlocal dff_a
    nonlocal dff_b
    nonlocal prev_clear

    out_a = dff_a(True, prev_clear, a)
    out_b = dff_b(True, prev_clear, b)

    prev_clear = out_a and out_b

    out_a = 1  if out_a else 0
    out_b = -1 if out_b else 0

    output = out_a + out_b
    return output

  return pfd

def acc_gen():
  acc_val: np.int32 = 0

  def acc(input: np.int8) -> np.int32:
    nonlocal acc_val
    output = acc_val + np.int32(input)
    acc_val = output
    return acc_val
  return acc

def mav_gen(width = 32):
  fifo = [0 for i in range(width-1)]
  def mav(input: np.int16):
    nonlocal fifo
    fifo.append(input)
    output = np.mean(fifo)
    fifo = fifo[1:]
    return output
  return mav

def div2_gen():
  dff = dff_gen()
  n_prev_out: bool = True
  def div2(input: bool) -> bool:
    nonlocal n_prev_out
    output = dff(n_prev_out, False, input)
    n_prev_out = not output
    return output
  return div2

def pll_gen():
  base_step = np.uint32(2**20) # base frequency = fs/16
  msk = (2 ** 24) - 1

  ctrl: np.int32 = 0
  nco = nco_gen()
  pfd  = pfd_gen()
  acc  = acc_gen()
  div2 = div2_gen()

  def pll(input: np.uint16) -> np.uint16:
    '''
    input 16 bits waveform
    return 14 bits indix of the waveform lut
    '''
    nonlocal ctrl
    nonlocal nco
    nonlocal pfd
    nonlocal acc
    nonlocal div2

    output: np.uint32  = nco(base_step + ctrl)
    output_b: bool     = (output & (2**13)) >> 13
    output_b_div2:bool = div2(output_b)
    input_b : bool     = (input & 2**15) >> 15
    pfd_out: np.int8   = pfd(input_b, output_b_div2)
    acc_out: np.int32  = acc(pfd_out)
    ctrl = (np.int32(pfd_out) << 16) + (acc_out << 10)

    return output

  return pll

