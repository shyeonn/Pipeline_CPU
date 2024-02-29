start:  lw x4, 0(x0)
        lw x5, 8(x0)
        lw x6, 16(x0)
T1:     addi x7, x5, 6
        add x7, x5, x4
        sub x8, x5, x4
        and x9, x5, x4
        or x10, x5, x4
        xor x11, x5, x4
        addi x27, x4, 1
        addi x28, x4, -7
        andi x29, x4, 15
        ori x30, x4, 16
        xori x31, x4, 15
        beq x7, x8, T1
        sw x7, 24(x0)
        lw x11, 24(x0)
        bne x7, x11, T1
T2:     lw x4, 32(x0)
        lw x5, 40(x0)
        bge x4, x5, T2
        add x4, x4, x5
        blt x5, x4, T1
        sub x4, x4, x5