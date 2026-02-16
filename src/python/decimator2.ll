@outputs = private global [2 x i64] zeroinitializer

@st17 = private global i1 0
@st18 = private global i1 0
@st19 = private global i48 0

define ptr @decimator2(i64 %x0.i, i64 %x1.i){
entry:
    %x0 = trunc i64 %x0.i to i1
    %x1 = trunc i64 %x1.i to i48

    %x2 = load i1, ptr @st17
    %x3 = load i1, ptr @st18
    %x4 = load i48, ptr @st19
    %x8.0 = zext i1 %x2 to i2
    %x8.1 = zext i1 1 to i2
    %x8 = add i2 %x8.0, %x8.1
    %x9.2 = lshr i2 %x8, 0
    %x9 = trunc i2 %x9.2 to i1
    %x10 = select i1  %x0, i1 %x9, i1 %x2
    %x11 = icmp eq i1 %x2, 0
    %x12 = and i1 %x0, %x11
    %x15 = select i1  %x12, i48 %x1, i48 %x4
    store i1 %x10, ptr @st17
    store i1 %x12, ptr @st18
    store i48 %x15, ptr @st19

    %x3.oe = sext i1 %x3 to i64
    %x3.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x3.oe, ptr %x3.optr
    %x4.oe = sext i48 %x4 to i64
    %x4.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x4.oe, ptr %x4.optr
    ret ptr @outputs
}
