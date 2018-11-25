# 看了一部分，先写下来

G-machine 和之前的Template不同，在Template中是形成明显树形结构，将所有的函数保存在heap中，每次调用函数都会对树形结构进行遍历。而G-machine的目的
则是在将函数体转为一系列的指令，函数被转为一系列指令。
比如；2+3*4变为[INum 2, INum 3, INum 4, IMult, IPuls]这样的指令序列，这样的指令序列通过相关的栈操作完成求值。
再比如：f x y = K (g x)则利用一下栈操作[Push 1, Push 1, Mkap, Pushglobal K, Mkap, Slide 3, Unwind]
（这里没有看懂，先放在这里）

疑问：
1. 反复调用函数该怎么处理？如果不需要遍历
2. 这可能是lazy的吗？
3. 一般函数如何转换？这些操作该怎么实现？
