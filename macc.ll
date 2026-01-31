@outputs = private global [1 x i64] zeroinitializer

@st31 = private global i18 0
@st32 = private global i18 0
@st33 = private global i36 0
@st34 = private global i48 0

define ptr @macc(i64 %x0.i, i64 %x1.i, i64 %x2.i){
entry:
    %x0 = trunc i64 %x0.i to i1
    %x1 = trunc i64 %x1.i to i18
    %x2 = trunc i64 %x2.i to i18

    %x3 = load i18, ptr @st31
    %x4 = load i18, ptr @st32
    store i18 %x1, ptr @st31
    store i18 %x2, ptr @st32
    %x8.0 = zext i18 %x3 to i36
    %x8.1 = zext i18 %x4 to i36
    %x8 = mul i36 %x8.0, %x8.1
    %x10 = load i36, ptr @st33
    %x12 = load i48, ptr @st34
    %x14.2 = lshr i36 %x10, 35
    %x14 = trunc i36 %x14.2 to i1
    %x15 = xor i12 0, -1
    %x16.3 = zext i12 %x15 to i48
    %x16.4 = shl i48 %x16.3, 36
    %x16.5 = zext i36 %x10 to i48
    %x16 = or i48 %x16.4, %x16.5
    %x17.6 = zext i12 0 to i48
    %x17.7 = shl i48 %x17.6, 36
    %x17.8 = zext i36 %x10 to i48
    %x17 = or i48 %x17.7, %x17.8
    %x18 = select i1  %x14, i48 %x16, i48 %x17
    %x24.9 = zext i48 %x12 to i49
    %x24.10 = zext i48 %x18 to i49
    %x24 = add i49 %x24.9, %x24.10
    %x25.11 = lshr i49 %x24, 0
    %x25 = trunc i49 %x25.11 to i48
    %x26 = select i1  %x0, i48 %x18, i48 %x25
    store i48 %x26, ptr @st34
    store i36 %x8, ptr @st33

    %x12.oe = sext i48 %x12 to i64
    %x12.optr = getelementptr [1 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x12.oe, ptr %x12.optr
    ret ptr @outputs
}
