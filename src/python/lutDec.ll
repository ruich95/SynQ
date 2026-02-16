@outputs = private global [1 x i64] zeroinitializer

define ptr @lutDec(i64 %x0.i, i64 %x1.i){
entry:
    %x0 = trunc i64 %x0.i to i14
    %x1 = trunc i64 %x1.i to i18

    %x2.0 = lshr i14 %x0, 13
    %x2 = trunc i14 %x2.0 to i1
    %x3 = xor i18 %x1, -1
    %x4.1 = zext i18 %x3 to i19
    %x4.2 = zext i18 1 to i19
    %x4 = add i19 %x4.1, %x4.2
    %x5.3 = lshr i19 %x4, 0
    %x5 = trunc i19 %x5.3 to i18
    %x6.4 = zext i18 262143 to i19
    %x6.5 = zext i18 %x5 to i19
    %x6 = add i19 %x6.4, %x6.5
    %x7.6 = lshr i19 %x6, 0
    %x7 = trunc i19 %x7.6 to i18
    %x8 = select i1  %x2, i18 %x1, i18 %x7

    %x8.oe = sext i18 %x8 to i64
    %x8.optr = getelementptr [1 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x8.oe, ptr %x8.optr
    ret ptr @outputs
}
