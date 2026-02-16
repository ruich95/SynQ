@outputs = private global [2 x i64] zeroinitializer

@st60 = private global i33 0
@st61 = private global i1 0
@st62 = private global i33 0
@st63 = private global i1 0
@st64 = private global i32 0

define ptr @unwrap_diff(i64 %x0.i, i64 %x1.i){
entry:
    %x0 = trunc i64 %x0.i to i1
    %x1 = trunc i64 %x1.i to i32

    %x2.0 = lshr i32 %x1, 31
    %x2 = trunc i32 %x2.0 to i1
    %x3.1 = zext i1 %x2 to i33
    %x3.2 = shl i33 %x3.1, 32
    %x3.3 = zext i32 %x1 to i33
    %x3 = or i33 %x3.2, %x3.3
    %x6 = load i33, ptr @st60
    %x8 = select i1  %x0, i33 %x3, i33 %x6
    store i33 %x8, ptr @st60
    %x10 = xor i33 %x6, -1
    %x11.4 = zext i33 %x10 to i34
    %x11.5 = zext i33 1 to i34
    %x11 = add i34 %x11.4, %x11.5
    %x12.6 = lshr i34 %x11, 0
    %x12 = trunc i34 %x12.6 to i33
    %x13.7 = zext i33 %x3 to i34
    %x13.8 = zext i33 %x12 to i34
    %x13 = add i34 %x13.7, %x13.8
    %x14.9 = lshr i34 %x13, 0
    %x14 = trunc i34 %x14.9 to i33
    %x17 = load i1, ptr @st61
    %x18 = load i33, ptr @st62
    store i1 %x0, ptr @st61
    store i33 %x14, ptr @st62
    %x24 = icmp slt i33 %x18, 1686629713
    %x29 = icmp slt i33 6903304879, %x18
    %x30 = and i1 %x24, %x29
    %x35 = xor i1 %x24, -1
    %x40 = and i1 %x35, %x29
    %x41 = xor i33 3373259426, -1
    %x42.10 = zext i33 %x41 to i34
    %x42.11 = zext i33 1 to i34
    %x42 = add i34 %x42.10, %x42.11
    %x43.12 = lshr i34 %x42, 0
    %x43 = trunc i34 %x43.12 to i33
    %x44.13 = zext i33 %x18 to i34
    %x44.14 = zext i33 %x43 to i34
    %x44 = add i34 %x44.13, %x44.14
    %x45.15 = lshr i34 %x44, 0
    %x45 = trunc i34 %x45.15 to i33
    %x46.16 = zext i33 %x18 to i34
    %x46.17 = zext i33 3373259426 to i34
    %x46 = add i34 %x46.16, %x46.17
    %x47.18 = lshr i34 %x46, 0
    %x47 = trunc i34 %x47.18 to i33
    %x48 = select i1  %x40, i33 %x45, i33 %x47
    %x49 = select i1  %x30, i33 %x18, i33 %x48
    %x52.19 = lshr i33 %x49, 0
    %x52 = trunc i33 %x52.19 to i32
    %x55 = load i1, ptr @st63
    %x56 = load i32, ptr @st64
    store i1 %x17, ptr @st63
    store i32 %x52, ptr @st64

    %x55.oe = sext i1 %x55 to i64
    %x55.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x55.oe, ptr %x55.optr
    %x56.oe = sext i32 %x56 to i64
    %x56.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x56.oe, ptr %x56.optr
    ret ptr @outputs
}
