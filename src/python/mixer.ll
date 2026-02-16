@outputs = private global [1 x i64] zeroinitializer

@st11 = private global i18 0
@st12 = private global i18 0
@st13 = private global i36 0

define ptr @mixer(i64 %x0.i, i64 %x1.i){
entry:
    %x0 = trunc i64 %x0.i to i18
    %x1 = trunc i64 %x1.i to i16

    %x2 = load i18, ptr @st11
    %x3 = load i18, ptr @st12
    %x4 = load i36, ptr @st13
    %x8.0 = zext i16 %x1 to i18
    %x8.1 = shl i18 %x8.0, 2
    %x8.2 = zext i2 0 to i18
    %x8 = or i18 %x8.1, %x8.2
    %x9.3 = sext i18 %x2 to i36
    %x9.4 = sext i18 %x3 to i36
    %x9 = mul i36 %x9.3, %x9.4
    store i18 %x8, ptr @st11
    store i18 %x0, ptr @st12
    store i36 %x9, ptr @st13

    %x4.oe = sext i36 %x4 to i64
    %x4.optr = getelementptr [1 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x4.oe, ptr %x4.optr
    ret ptr @outputs
}
