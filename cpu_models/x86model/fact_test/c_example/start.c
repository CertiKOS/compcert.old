int main();

void _start() {
    asm(
    /* main body of program: call main(), etc */
        "call main;"
    /* exit system call */
        "movl $1,%eax;"
        "xorl %ebx,%ebx;"
        "int  $0x80"
    );
}
