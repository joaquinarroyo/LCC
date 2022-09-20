.data
a: .short 5

.text
.global main
main:
    shll $8, a
    ret