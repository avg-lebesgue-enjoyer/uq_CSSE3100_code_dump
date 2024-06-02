method Test(x : nat, y : nat, z : nat)
    decreases y, x
{
    if (x == 0 || y == 0 || z == 0) {
        return;
    }
    Test(x - 1, y, z);
}