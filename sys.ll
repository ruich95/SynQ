@outputs = private global [2 x i64] zeroinitializer

@st12 = private global i7 0

define ptr @sys(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i7

    %x1 = load i7, ptr @st12
    %x3.0 = zext i7 %x1 to i8
    %x3.1 = zext i7 %x0 to i8
    %x3 = add i8 %x3.0, %x3.1
    %x4.2 = lshr i8 %x3, 0
    %x4 = trunc i8 %x4.2 to i7
    store i7 %x4, ptr @st12
    %x10 = ashr i7 %x4, 3
    %x11.3 = lshr i7 %x10, 1
    %x11 = trunc i7 %x11.3 to i6

    %x4.oe = sext i7 %x4 to i64
    %x4.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x4.oe, ptr %x4.optr
    %x11.oe = sext i6 %x11 to i64
    %x11.optr = getelementptr [2 x i64], ptr @outputs, i64 0, i64 1
    store i64 %x11.oe, ptr %x11.optr
    ret ptr @outputs
}
