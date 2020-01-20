#include "types.h"
#include "stat.h"
#include "user.h"

int a = 1;

int
main(void) {

    int pid = fork();

    if (pid == 0) {
        printf(1, "# of free pages in child 1 before changing variables: %d \n", numfreepgs());
        // update variable a in child 1, which should cause it to be written to a new page
        a = 2;
        printf(1, "# of free pages in child 1 after changing variables: %d \n", numfreepgs());
    }

    else
    {
        wait(); // wait for child 1 proc to finish running
        // and fork again
        pid = fork();
        
        if (pid == 0) {
            printf(1, "# of free pages in child 2 before changing variables: %d \n", numfreepgs());
            // update variable a in child 2, which should cause it to be written to a new page
            a = 2;
            printf(1, "# of free pages in child 2 after changing variables: %d \n", numfreepgs());
        }
        else
        {
            printf(1, "# of free pages in parent: %d \n", numfreepgs());
            wait();
        }
    }

    exit();
}