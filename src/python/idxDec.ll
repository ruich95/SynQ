@outputs = private global [1 x i64] zeroinitializer

define ptr @idxDec(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i14

    %x1.0 = lshr i14 %x0, 12
    %x1 = trunc i14 %x1.0 to i1
    %x2.1 = lshr i14 %x0, 0
    %x2 = trunc i14 %x2.1 to i12
    %x3 = xor i12 %x2, -1
    %x4.2 = zext i12 %x3 to i13
    %x4.3 = zext i12 1 to i13
    %x4 = add i13 %x4.2, %x4.3
    %x5.4 = lshr i13 %x4, 0
    %x5 = trunc i13 %x5.4 to i12
    %x6.5 = zext i12 4095 to i13
    %x6.6 = zext i12 %x5 to i13
    %x6 = add i13 %x6.5, %x6.6
    %x7.7 = lshr i13 %x6, 0
    %x7 = trunc i13 %x7.7 to i12
    %x9 = select i1  %x1, i12 %x7, i12 %x2

    %x9.oe = sext i12 %x9 to i64
    %x9.optr = getelementptr [1 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x9.oe, ptr %x9.optr
    ret ptr @outputs
}
