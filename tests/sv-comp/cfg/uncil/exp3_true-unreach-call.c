extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
        ERROR: __VERIFIER_error();
    }
    return;
}

int main()
{
    int x = 0;
    int y = (x == 0 ? (x == 0 ? x + 1 : 0) + 1 : 0) + 1;
    __VERIFIER_assert(y == 3);
    return 0;
}