havoc x, y; 
assume y >= 0; 
a := 0;
b := 0;
c := 0;
r := x;
while c < y inv c <= y and r = x + a * c - b * c do
{
r := r + a;
r := r - b;
c := c + 1 
};
assert r = x + a * y - b * y