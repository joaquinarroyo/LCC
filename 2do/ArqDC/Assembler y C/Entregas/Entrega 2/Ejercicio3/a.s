.data
a: .long 1

.text
.global main
main:
    shll $31, a
    ret
