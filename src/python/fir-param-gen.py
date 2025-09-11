import numpy as np

coefs = np.array([442, 1284, 1094, -119, -1154, 
                 -261, 1446, 1072, -1765, -2804, 1982, 10196, 
                 14323, 10196, 1982, -2804, -1765, 1072, 
                 1446, -261, -1154, -119, 1094, 1284, 442], 
                 dtype=np.int16)

coefs = coefs.astype(np.uint16)

def print_coef(coefs, name="coefs"):
    print("{}: Vect {} Bits64".format(name, len(coefs)))
    coefs_str = ["{}, ".format(c) for c in coefs[:-1]]
    coefs_str.append(str(coefs[-1]))
    coefs_str = "".join(coefs_str)
    print("{} = [{}]".format(name, coefs_str))

if __name__ == "__main__":
    print_coef(coefs)
