@outputs = private global [1 x i64] zeroinitializer

@st57 = private global i33 0

define ptr @unwarp_diff(i64 %x0.i){
entry:
    %x0 = trunc i64 %x0.i to i33

    %x1 = load i33, ptr @st57
    store i33 %x0, ptr @st57
    %x5 = xor i33 %x1, -1
    %x6.0 = zext i33 %x5 to i34
    %x6.1 = zext i33 1 to i34
    %x6 = add i34 %x6.0, %x6.1
    %x7.2 = lshr i34 %x6, 0
    %x7 = trunc i34 %x7.2 to i33
    %x8.3 = zext i33 %x0 to i34
    %x8.4 = zext i33 %x7 to i34
    %x8 = add i34 %x8.3, %x8.4
    %x9.5 = lshr i34 %x8, 0
    %x9 = trunc i34 %x9.5 to i33
    %x11 = icmp slt i33 %x9, 1686629713
    %x21 = icmp slt i33 2608337583, %x9
    %x22 = and i1 %x11, %x21
    %x37 = xor i1 %x11, -1
    %x43 = xor i33 3373259426, -1
    %x44.6 = zext i33 %x43 to i34
    %x44.7 = zext i33 1 to i34
    %x44 = add i34 %x44.6, %x44.7
    %x45.8 = lshr i34 %x44, 0
    %x45 = trunc i34 %x45.8 to i33
    %x46.9 = zext i33 %x9 to i34
    %x46.10 = zext i33 %x45 to i34
    %x46 = add i34 %x46.9, %x46.10
    %x47.11 = lshr i34 %x46, 0
    %x47 = trunc i34 %x47.11 to i33
    %x53.12 = zext i33 %x9 to i34
    %x53.13 = zext i33 3373259426 to i34
    %x53 = add i34 %x53.12, %x53.13
    %x54.14 = lshr i34 %x53, 0
    %x54 = trunc i34 %x54.14 to i33
    %x55 = select i1  %x37, i33 %x47, i33 %x54
    %x56 = select i1  %x22, i33 %x9, i33 %x55

    %x56.oe = sext i33 %x56 to i64
    %x56.optr = getelementptr [1 x i64], ptr @outputs, i64 0, i64 0
    store i64 %x56.oe, ptr %x56.optr
    ret ptr @outputs
}
