#include <stdio.h>

#define BUFFER_SIZE (1 << 16)

char buffer[BUFFER_SIZE];

char* colors[] = {
    "\033[0;91m",
    "\033[0;92m",
    "\033[0;93m",
    "\033[0;94m",
    "\033[0;95m",
    "\033[0;96m"
};

#define COLORS_COUNT (sizeof(colors) / sizeof(colors[0]))

char* color_reset = "\033[0m";

int main() {
    while (fgets(buffer, BUFFER_SIZE, stdin)) {
        int parens = 0;
        int i = 0;
        while (buffer[i] != '\0') {
            if (buffer[i] == ')') {
                --parens;
            }

            if (parens >= 0 && (buffer[i] == '(' || buffer[i] == ')')) {
                fputs(colors[parens % COLORS_COUNT], stdout);
            }

            if (buffer[i] == '(') {
                ++parens;
            }

            fputc(buffer[i], stdout);

            if (buffer[i] == '(' || buffer[i] == ')') {
                fputs(color_reset, stdout);
            }

            ++i;
        }
    }
    return 0;
}
