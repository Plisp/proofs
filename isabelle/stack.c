#define LEN 1000

unsigned int content[LEN];
unsigned int top = -1;     /* -1 means MAX_INT in unsigned */

int is_empty(void)
{
    return top == -1;
}

int has_capacity(void) {
    return top < LEN - 1;
}

void push(unsigned int data)
{
    top++;
    content[top] = data;
}

unsigned int pop(void)
{
    unsigned int result = content[top];
    top--;
    return result;
}

unsigned int sum(void)
{
    unsigned int result = 0;
    while (top != -1) {
      result += pop();
    }
    return result;
}
