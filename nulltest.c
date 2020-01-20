#include "types.h"
#include "stat.h"
#include "user.h"

// this now returns "illegal mem access bc va mapped to pte which isn't present" after cow added
int 
main(int argc, char *argv[])
{
    printf(1, "Deref null ptr returns: %p\n", *((int*)0));
    exit();
}