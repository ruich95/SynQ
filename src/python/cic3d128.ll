@outputs = private global [2 x i64] zeroinitializer

@st81 = private global i37 0
@st82 = private global i37 0
@st83 = private global i37 0
@st84 = private global i7 0
@st85 = private global i1 0
@st86 = private global i37 0
@st87 = private global i37 0
@st88 = private global i37 0
@st89 = private global i37 0

define ptr @cic3d128(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i16

    %x1.0 = lshr i16 %x0, 15
    %x1 = trunc i16 %x1.0 to i1
    %x2 = xor i21 0, -1
    %x3.1 = zext i21 %x2 to i37
    %x3.2 = shl i37 %x3.1, 16
    %x3.3 = zext i16 %x0 to i37
    %x3 = or i37 %x3.2, %x3.3
    %x4.4 = zext i21 0 to i37
    %x4.5 = shl i37 %x4.4, 16
    %x4.6 = zext i16 %x0 to i37
    %x4 = or i37 %x4.5, %x4.6
    %x5 = select i1  %x1, i37 %x3, i37 %x4
    %x7 = load i37, ptr @st81
    %x9.7 = zext i37 %x7 to i38
    %x9.8 = zext i37 %x5 to i38
    %x9 = add i38 %x9.7, %x9.8
    %x10.9 = lshr i38 %x9, 0
    %x10 = trunc i38 %x10.9 to i37
    store i37 %x10, ptr @st81
    %x15 = load i37, ptr @st82
    %x17.10 = zext i37 %x15 to i38
    %x17.11 = zext i37 %x10 to i38
    %x17 = add i38 %x17.10, %x17.11
    %x18.12 = lshr i38 %x17, 0
    %x18 = trunc i38 %x18.12 to i37
    store i37 %x18, ptr @st82
    %x23 = load i37, ptr @st83
    %x25.13 = zext i37 %x23 to i38
    %x25.14 = zext i37 %x18 to i38
    %x25 = add i38 %x25.13, %x25.14
    %x26.15 = lshr i38 %x25, 0
    %x26 = trunc i38 %x26.15 to i37
    store i37 %x26, ptr @st83
    %x33 = load i7, ptr @st84
    %x34 = load i1, ptr @st85
    %x35 = load i37, ptr @st86
    %x39.16 = zext i7 %x33 to i8
    %x39.17 = zext i7 1 to i8
    %x39 = add i8 %x39.16, %x39.17
    %x40.18 = lshr i8 %x39, 0
    %x40 = trunc i8 %x40.18 to i7
    %x41 = select i1  1, i7 %x40, i7 %x33
    %x42 = icmp eq i7 %x33, 0
    %x43 = and i1 1, %x42
    %x46 = select i1  %x43, i37 %x26, i37 %x35
    store i7 %x41, ptr @st84
    store i1 %x43, ptr @st85
    store i37 %x46, ptr @st86
    %x50 = load i37, ptr @st87
    %x52 = select i1  %x34, i37 %x35, i37 %x50
    store i37 %x52, ptr @st87
    %x54 = xor i37 %x50, -1
    %x55.19 = zext i37 %x54 to i38
    %x55.20 = zext i37 1 to i38
    %x55 = add i38 %x55.19, %x55.20
    %x56.21 = lshr i38 %x55, 0
    %x56 = trunc i38 %x56.21 to i37
    %x57.22 = zext i37 %x35 to i38
    %x57.23 = zext i37 %x56 to i38
    %x57 = add i38 %x57.22, %x57.23
    %x58.24 = lshr i38 %x57, 0
    %x58 = trunc i38 %x58.24 to i37
    %x61 = load i37, ptr @st88
    %x63 = select i1  %x34, i37 %x58, i37 %x61
    store i37 %x63, ptr @st88
    %x65 = xor i37 %x61, -1
    %x66.25 = zext i37 %x65 to i38
    %x66.26 = zext i37 1 to i38
    %x66 = add i38 %x66.25, %x66.26
    %x67.27 = lshr i38 %x66, 0
    %x67 = trunc i38 %x67.27 to i37
    %x68.28 = zext i37 %x58 to i38
    %x68.29 = zext i37 %x67 to i38
    %x68 = add i38 %x68.28, %x68.29
    %x69.30 = lshr i38 %x68, 0
    %x69 = trunc i38 %x69.30 to i37
    %x72 = load i37, ptr @st89
    %x74 = select i1  %x34, i37 %x69, i37 %x72
    store i37 %x74, ptr @st89
    %x76 = xor i37 %x72, -1
    %x77.31 = zext i37 %x76 to i38
    %x77.32 = zext i37 1 to i38
    %x77 = add i38 %x77.31, %x77.32
    %x78.33 = lshr i38 %x77, 0
    %x78 = trunc i38 %x78.33 to i37
    %x79.34 = zext i37 %x69 to i38
    %x79.35 = zext i37 %x78 to i38
    %x79 = add i38 %x79.34, %x79.35
    %x80.36 = lshr i38 %x79, 0
    %x80 = trunc i38 %x80.36 to i37

    %x34.oe = sext i1 %x34 to i64
    %x34.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x34.oe, ptr %x34.optr
    %x80.oe = sext i37 %x80 to i64
    %x80.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x80.oe, ptr %x80.optr
    ret ptr @outputs
}
