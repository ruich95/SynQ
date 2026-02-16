@outputs = private global [2 x i64] zeroinitializer

@st120 = private global i44 0
@st121 = private global i37 0
@st122 = private global i31 0
@st123 = private global i26 0
@st124 = private global i7 0
@st125 = private global i1 0
@st126 = private global i23 0
@st127 = private global i23 0
@st128 = private global i22 0
@st129 = private global i21 0
@st130 = private global i20 0

define ptr @cic4d128(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i16

    %x1.0 = lshr i16 %x0, 15
    %x1 = trunc i16 %x1.0 to i1
    %x2 = xor i28 0, -1
    %x3.1 = zext i28 %x2 to i44
    %x3.2 = shl i44 %x3.1, 16
    %x3.3 = zext i16 %x0 to i44
    %x3 = or i44 %x3.2, %x3.3
    %x4.4 = zext i28 0 to i44
    %x4.5 = shl i44 %x4.4, 16
    %x4.6 = zext i16 %x0 to i44
    %x4 = or i44 %x4.5, %x4.6
    %x5 = select i1  %x1, i44 %x3, i44 %x4
    %x7 = load i44, ptr @st120
    %x9.7 = zext i44 %x7 to i45
    %x9.8 = zext i44 %x5 to i45
    %x9 = add i45 %x9.7, %x9.8
    %x10.9 = lshr i45 %x9, 0
    %x10 = trunc i45 %x10.9 to i44
    store i44 %x10, ptr @st120
    %x15.10 = lshr i44 %x10, 7
    %x15 = trunc i44 %x15.10 to i37
    %x17 = load i37, ptr @st121
    %x19.11 = zext i37 %x17 to i38
    %x19.12 = zext i37 %x15 to i38
    %x19 = add i38 %x19.11, %x19.12
    %x20.13 = lshr i38 %x19, 0
    %x20 = trunc i38 %x20.13 to i37
    store i37 %x20, ptr @st121
    %x25.14 = lshr i37 %x20, 6
    %x25 = trunc i37 %x25.14 to i31
    %x27 = load i31, ptr @st122
    %x29.15 = zext i31 %x27 to i32
    %x29.16 = zext i31 %x25 to i32
    %x29 = add i32 %x29.15, %x29.16
    %x30.17 = lshr i32 %x29, 0
    %x30 = trunc i32 %x30.17 to i31
    store i31 %x30, ptr @st122
    %x35.18 = lshr i31 %x30, 5
    %x35 = trunc i31 %x35.18 to i26
    %x37 = load i26, ptr @st123
    %x39.19 = zext i26 %x37 to i27
    %x39.20 = zext i26 %x35 to i27
    %x39 = add i27 %x39.19, %x39.20
    %x40.21 = lshr i27 %x39, 0
    %x40 = trunc i27 %x40.21 to i26
    store i26 %x40, ptr @st123
    %x45.22 = lshr i26 %x40, 3
    %x45 = trunc i26 %x45.22 to i23
    %x49 = load i7, ptr @st124
    %x50 = load i1, ptr @st125
    %x51 = load i23, ptr @st126
    %x55.23 = zext i7 %x49 to i8
    %x55.24 = zext i7 1 to i8
    %x55 = add i8 %x55.23, %x55.24
    %x56.25 = lshr i8 %x55, 0
    %x56 = trunc i8 %x56.25 to i7
    %x57 = select i1  1, i7 %x56, i7 %x49
    %x58 = icmp eq i7 %x49, 0
    %x59 = and i1 1, %x58
    %x62 = select i1  %x59, i23 %x45, i23 %x51
    store i7 %x57, ptr @st124
    store i1 %x59, ptr @st125
    store i23 %x62, ptr @st126
    %x66 = load i23, ptr @st127
    %x68 = select i1  %x50, i23 %x51, i23 %x66
    store i23 %x68, ptr @st127
    %x70 = xor i23 %x66, -1
    %x71.26 = zext i23 %x70 to i24
    %x71.27 = zext i23 1 to i24
    %x71 = add i24 %x71.26, %x71.27
    %x72.28 = lshr i24 %x71, 0
    %x72 = trunc i24 %x72.28 to i23
    %x73.29 = zext i23 %x51 to i24
    %x73.30 = zext i23 %x72 to i24
    %x73 = add i24 %x73.29, %x73.30
    %x74.31 = lshr i24 %x73, 0
    %x74 = trunc i24 %x74.31 to i23
    %x77.32 = lshr i23 %x74, 1
    %x77 = trunc i23 %x77.32 to i22
    %x80 = load i22, ptr @st128
    %x82 = select i1  %x50, i22 %x77, i22 %x80
    store i22 %x82, ptr @st128
    %x84 = xor i22 %x80, -1
    %x85.33 = zext i22 %x84 to i23
    %x85.34 = zext i22 1 to i23
    %x85 = add i23 %x85.33, %x85.34
    %x86.35 = lshr i23 %x85, 0
    %x86 = trunc i23 %x86.35 to i22
    %x87.36 = zext i22 %x77 to i23
    %x87.37 = zext i22 %x86 to i23
    %x87 = add i23 %x87.36, %x87.37
    %x88.38 = lshr i23 %x87, 0
    %x88 = trunc i23 %x88.38 to i22
    %x91.39 = lshr i22 %x88, 1
    %x91 = trunc i22 %x91.39 to i21
    %x94 = load i21, ptr @st129
    %x96 = select i1  %x50, i21 %x91, i21 %x94
    store i21 %x96, ptr @st129
    %x98 = xor i21 %x94, -1
    %x99.40 = zext i21 %x98 to i22
    %x99.41 = zext i21 1 to i22
    %x99 = add i22 %x99.40, %x99.41
    %x100.42 = lshr i22 %x99, 0
    %x100 = trunc i22 %x100.42 to i21
    %x101.43 = zext i21 %x91 to i22
    %x101.44 = zext i21 %x100 to i22
    %x101 = add i22 %x101.43, %x101.44
    %x102.45 = lshr i22 %x101, 0
    %x102 = trunc i22 %x102.45 to i21
    %x105.46 = lshr i21 %x102, 1
    %x105 = trunc i21 %x105.46 to i20
    %x108 = load i20, ptr @st130
    %x110 = select i1  %x50, i20 %x105, i20 %x108
    store i20 %x110, ptr @st130
    %x112 = xor i20 %x108, -1
    %x113.47 = zext i20 %x112 to i21
    %x113.48 = zext i20 1 to i21
    %x113 = add i21 %x113.47, %x113.48
    %x114.49 = lshr i21 %x113, 0
    %x114 = trunc i21 %x114.49 to i20
    %x115.50 = zext i20 %x105 to i21
    %x115.51 = zext i20 %x114 to i21
    %x115 = add i21 %x115.50, %x115.51
    %x116.52 = lshr i21 %x115, 0
    %x116 = trunc i21 %x116.52 to i20
    %x119.53 = lshr i20 %x116, 2
    %x119 = trunc i20 %x119.53 to i18

    %x50.oe = sext i1 %x50 to i64
    %x50.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x50.oe, ptr %x50.optr
    %x119.oe = sext i18 %x119 to i64
    %x119.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x119.oe, ptr %x119.optr
    ret ptr @outputs
}
