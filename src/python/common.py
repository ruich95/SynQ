import numpy as np

def to_number(num_str:str, nbits: np.uint8) -> np.uint64:
    """Convert a Verilog-style numeric literal to a signed np.uint64 value using two’s complement.

    Parameters
    ----------
    num_str : str
        String containing the numeric value, expected in the form "<prefix>'<base><digits>".
    nbits : np.uint8
        Bit width used to mask the literal and determine the sign bit.

    Returns
    -------
    np.uint64
        The two’s-complement interpreted numeric value constrained to the specified bit width."""
    ''''''
    mask = np.uint64((1 << nbits) - 1)
    val = np.uint64(num_str[num_str.find("\'")+2:]) & mask
    sign_bit = np.uint64(1 << (nbits - 1))
    if (val & sign_bit):
       val = val | (~mask)
    return val

def width_convert(value: np.uint64, from_bits: np.uint8, to_bits: np.uint8) -> np.uint64:
    """Convert a signed q_{1.from_bits-1} value to a signed q_{1.to_bits-1} value using two’s complement. 
    Parameters
    ----------
    value : np.uint64
        The input value in q_{1.from_bits-1} format, with sign extended higher bits.
    from_bits : np.uint8
        The bit width of the input value.
    to_bits : np.uint8
        The desired bit width of the output value, with sign extended higher bits.

    Returns
    -------
    np.uint64
        The converted value in q_{1.to_bits-1} format with sign extended higher bits.
    """
    to_mask = np.uint64((1 << to_bits) - 1)
    to_sign_bit = np.uint64(1 << (to_bits - 1))

    if from_bits == to_bits:
        return value
    elif from_bits < to_bits:
        return value << np.uint64(to_bits - from_bits) 
    else:
        val = value >> np.uint64(from_bits - to_bits)
        if (val & to_sign_bit):
            val = val | (~to_mask)
        return val