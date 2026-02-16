@outputs = private global [2 x i64] zeroinitializer

@st128 = private global i44 0
@st129 = private global i37 0
@st130 = private global i31 0
@st131 = private global i26 0
@st132 = private global i7 0
@st133 = private global i1 0
@st134 = private global i23 0
@st135 = private global i23 0
@st136 = private global i1 0
@st137 = private global i23 0
@st138 = private global i22 0
@st139 = private global i1 0
@st140 = private global i22 0
@st141 = private global i21 0
@st142 = private global i1 0
@st143 = private global i21 0
@st144 = private global i20 0
@st145 = private global i1 0
@st146 = private global i20 0

define ptr @pipe_cic_4d_128(i64 %x0.i){
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
    %x7 = load i44, ptr @st128
    %x9.7 = zext i44 %x7 to i45
    %x9.8 = zext i44 %x5 to i45
    %x9 = add i45 %x9.7, %x9.8
    %x10.9 = lshr i45 %x9, 0
    %x10 = trunc i45 %x10.9 to i44
    store i44 %x10, ptr @st128
    %x13.10 = lshr i44 %x7, 7
    %x13 = trunc i44 %x13.10 to i37
    %x15 = load i37, ptr @st129
    %x17.11 = zext i37 %x15 to i38
    %x17.12 = zext i37 %x13 to i38
    %x17 = add i38 %x17.11, %x17.12
    %x18.13 = lshr i38 %x17, 0
    %x18 = trunc i38 %x18.13 to i37
    store i37 %x18, ptr @st129
    %x21.14 = lshr i37 %x15, 6
    %x21 = trunc i37 %x21.14 to i31
    %x23 = load i31, ptr @st130
    %x25.15 = zext i31 %x23 to i32
    %x25.16 = zext i31 %x21 to i32
    %x25 = add i32 %x25.15, %x25.16
    %x26.17 = lshr i32 %x25, 0
    %x26 = trunc i32 %x26.17 to i31
    store i31 %x26, ptr @st130
    %x29.18 = lshr i31 %x23, 5
    %x29 = trunc i31 %x29.18 to i26
    %x31 = load i26, ptr @st131
    %x33.19 = zext i26 %x31 to i27
    %x33.20 = zext i26 %x29 to i27
    %x33 = add i27 %x33.19, %x33.20
    %x34.21 = lshr i27 %x33, 0
    %x34 = trunc i27 %x34.21 to i26
    store i26 %x34, ptr @st131
    %x37.22 = lshr i26 %x31, 3
    %x37 = trunc i26 %x37.22 to i23
    %x41 = load i7, ptr @st132
    %x42 = load i1, ptr @st133
    %x43 = load i23, ptr @st134
    %x47.23 = zext i7 %x41 to i8
    %x47.24 = zext i7 1 to i8
    %x47 = add i8 %x47.23, %x47.24
    %x48.25 = lshr i8 %x47, 0
    %x48 = trunc i8 %x48.25 to i7
    %x49 = select i1  1, i7 %x48, i7 %x41
    %x50 = icmp eq i7 %x41, 0
    %x51 = and i1 1, %x50
    %x54 = select i1  %x51, i23 %x37, i23 %x43
    store i7 %x49, ptr @st132
    store i1 %x51, ptr @st133
    store i23 %x54, ptr @st134
    %x58 = load i23, ptr @st135
    %x59 = load i1, ptr @st136
    %x60 = load i23, ptr @st137
    %x64 = select i1  %x42, i23 %x43, i23 %x58
    %x65 = xor i23 %x58, -1
    %x66.26 = zext i23 %x65 to i24
    %x66.27 = zext i23 1 to i24
    %x66 = add i24 %x66.26, %x66.27
    %x67.28 = lshr i24 %x66, 0
    %x67 = trunc i24 %x67.28 to i23
    %x68.29 = zext i23 %x43 to i24
    %x68.30 = zext i23 %x67 to i24
    %x68 = add i24 %x68.29, %x68.30
    %x69.31 = lshr i24 %x68, 0
    %x69 = trunc i24 %x69.31 to i23
    store i23 %x64, ptr @st135
    store i1 %x42, ptr @st136
    store i23 %x69, ptr @st137
    %x73.32 = lshr i23 %x60, 1
    %x73 = trunc i23 %x73.32 to i22
    %x76 = load i22, ptr @st138
    %x77 = load i1, ptr @st139
    %x78 = load i22, ptr @st140
    %x82 = select i1  %x59, i22 %x73, i22 %x76
    %x83 = xor i22 %x76, -1
    %x84.33 = zext i22 %x83 to i23
    %x84.34 = zext i22 1 to i23
    %x84 = add i23 %x84.33, %x84.34
    %x85.35 = lshr i23 %x84, 0
    %x85 = trunc i23 %x85.35 to i22
    %x86.36 = zext i22 %x73 to i23
    %x86.37 = zext i22 %x85 to i23
    %x86 = add i23 %x86.36, %x86.37
    %x87.38 = lshr i23 %x86, 0
    %x87 = trunc i23 %x87.38 to i22
    store i22 %x82, ptr @st138
    store i1 %x59, ptr @st139
    store i22 %x87, ptr @st140
    %x91.39 = lshr i22 %x78, 1
    %x91 = trunc i22 %x91.39 to i21
    %x94 = load i21, ptr @st141
    %x95 = load i1, ptr @st142
    %x96 = load i21, ptr @st143
    %x100 = select i1  %x77, i21 %x91, i21 %x94
    %x101 = xor i21 %x94, -1
    %x102.40 = zext i21 %x101 to i22
    %x102.41 = zext i21 1 to i22
    %x102 = add i22 %x102.40, %x102.41
    %x103.42 = lshr i22 %x102, 0
    %x103 = trunc i22 %x103.42 to i21
    %x104.43 = zext i21 %x91 to i22
    %x104.44 = zext i21 %x103 to i22
    %x104 = add i22 %x104.43, %x104.44
    %x105.45 = lshr i22 %x104, 0
    %x105 = trunc i22 %x105.45 to i21
    store i21 %x100, ptr @st141
    store i1 %x77, ptr @st142
    store i21 %x105, ptr @st143
    %x109.46 = lshr i21 %x96, 1
    %x109 = trunc i21 %x109.46 to i20
    %x112 = load i20, ptr @st144
    %x113 = load i1, ptr @st145
    %x114 = load i20, ptr @st146
    %x118 = select i1  %x95, i20 %x109, i20 %x112
    %x119 = xor i20 %x112, -1
    %x120.47 = zext i20 %x119 to i21
    %x120.48 = zext i20 1 to i21
    %x120 = add i21 %x120.47, %x120.48
    %x121.49 = lshr i21 %x120, 0
    %x121 = trunc i21 %x121.49 to i20
    %x122.50 = zext i20 %x109 to i21
    %x122.51 = zext i20 %x121 to i21
    %x122 = add i21 %x122.50, %x122.51
    %x123.52 = lshr i21 %x122, 0
    %x123 = trunc i21 %x123.52 to i20
    store i20 %x118, ptr @st144
    store i1 %x95, ptr @st145
    store i20 %x123, ptr @st146
    %x127.53 = lshr i20 %x114, 2
    %x127 = trunc i20 %x127.53 to i18

    %x113.oe = sext i1 %x113 to i64
    %x113.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x113.oe, ptr %x113.optr
    %x127.oe = sext i18 %x127 to i64
    %x127.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x127.oe, ptr %x127.optr
    ret ptr @outputs
}
