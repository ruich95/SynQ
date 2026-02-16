@outputs = private global [2 x i64] zeroinitializer

@st25 = private global i24 0

define ptr @iqMixer(i64 %x0.i, i64 %x1.i){
entry:
    %x0 = trunc i64 %x0.i to i24
    %x1 = trunc i64 %x1.i to i16

    %x3 = load i24, ptr @st25
    %x5.0 = zext i24 %x3 to i25
    %x5.1 = zext i24 %x0 to i25
    %x5 = add i25 %x5.0, %x5.1
    %x6.2 = lshr i25 %x5, 0
    %x6 = trunc i25 %x6.2 to i24
    store i24 %x6, ptr @st25
    %x8.3 = lshr i24 %x3, 23
    %x8 = trunc i24 %x8.3 to i1
    %x9 = xor i1 %x8, -1
    %x10 = shl i24 1, 22
    %x11.4 = zext i24 %x3 to i25
    %x11.5 = zext i24 %x10 to i25
    %x11 = add i25 %x11.4, %x11.5
    %x12.6 = lshr i25 %x11, 0
    %x12 = trunc i25 %x12.6 to i24
    %x13.7 = lshr i24 %x12, 23
    %x13 = trunc i24 %x13.7 to i1
    %x14 = xor i1 %x13, -1
    %x17 = xor i16 %x1, -1
    %x18.8 = zext i16 %x17 to i17
    %x18.9 = zext i16 1 to i17
    %x18 = add i17 %x18.8, %x18.9
    %x19.10 = lshr i17 %x18, 0
    %x19 = trunc i17 %x19.10 to i16
    %x20 = select i1  %x9, i16 %x1, i16 %x19
    %x24 = select i1  %x14, i16 %x1, i16 %x19

    %x20.oe = sext i16 %x20 to i64
    %x20.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x20.oe, ptr %x20.optr
    %x24.oe = sext i16 %x24 to i64
    %x24.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x24.oe, ptr %x24.optr
    ret ptr @outputs
}
