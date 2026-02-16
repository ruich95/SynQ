@outputs = private global [2 x i64] zeroinitializer

@st11 = private global i24 0

define ptr @nco(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i24

    %x1 = load i24, ptr @st11
    %x3.0 = zext i24 %x1 to i25
    %x3.1 = zext i24 %x0 to i25
    %x3 = add i25 %x3.0, %x3.1
    %x4.2 = lshr i25 %x3, 0
    %x4 = trunc i25 %x4.2 to i24
    store i24 %x4, ptr @st11
    %x6.3 = lshr i24 %x1, 10
    %x6 = trunc i24 %x6.3 to i14
    %x7 = shl i24 1, 22
    %x8.4 = zext i24 %x1 to i25
    %x8.5 = zext i24 %x7 to i25
    %x8 = add i25 %x8.4, %x8.5
    %x9.6 = lshr i25 %x8, 0
    %x9 = trunc i25 %x9.6 to i24
    %x10.7 = lshr i24 %x9, 10
    %x10 = trunc i24 %x10.7 to i14

    %x6.oe = sext i14 %x6 to i64
    %x6.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x6.oe, ptr %x6.optr
    %x10.oe = sext i14 %x10 to i64
    %x10.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x10.oe, ptr %x10.optr
    ret ptr @outputs
}
