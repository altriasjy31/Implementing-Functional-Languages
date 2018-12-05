# 前言

G-machine 和之前的Template不同，在Template中是形成明显树形结构，将所有的函数保存在heap中，每次调用函数都会对树形结构进行遍历。而G-machine的目的
则是在将函数体转为一系列的指令，函数被转为一系列指令。
比如；2+3*4变为[INum 2, INum 3, INum 4, IMult, IPuls]这样的指令序列，这样的指令序列通过相关的栈操作完成求值。
再比如：f x y = K (g x)则利用一下栈操作[Push 1, Push 1, Mkap, Pushglobal K, Mkap, Slide 3, Unwind]
（这里没有看懂，先放在这里）

疑问：
1. 反复调用函数该怎么处理？如果不需要遍历
2. 这可能是lazy的吗？
3. 一般函数如何转换？这些操作该怎么实现

## minial G-machine

之前说了,G-machine的目的是将代码转换为一条条的指令，因此，在实现中，我们将定义
``` 
data Instrucion = Unwind | Pushglobal Name | Pushint Int | Push Int | Mkap | Slide Int
```
其实，和之前Template的实现类似，其过程相当于是tuples的变化，在这里我们定义GmState为
```
type GmState = (GmCode,　　　--当前的指令流，相当于当前调用的表达式转化而来的所有指令的一个列表
                GmStack,    --堆栈           
                GmHeap,     --由一系列节点构成的堆，这些节点也有对应这原文中的函数               
                GmGlobals,  --全局地址，相当于默认加载的可以Core-lang函数                
                GmStatistic)--用于统计
                
```
节点其实是对原有函数一种抽象
```
data Node
  = NNum Int        --数字，可以说表示求值的一种结果
  | NAp Addr Addr   --将表达式不断分解为两个部分，直到出现已经定义的函数，因而，可以简单理解为函数名所在地址和参数所在地址
  | NGlobal Int GmCode  --默认的函数定义
```

整个过程分为compile, eval, showResults

### eval
eval的目的就是使之前所说的一系列指令真正起作用，说白了实现这些指令对GmState进行的操作
>> Pushglobal f:i   s h m[f:a] 
>>
=>              i a:s h m
当前指令为Pushglobal时，在global中找到f对应所在的地址，将之入栈

>> Pushint n:i   s h           m
>>
=>           i a:s h[a:NNum n] m
当前指令为Pushint时，表示需要将数值插入heap，同时，对应的生成的地址要入栈

>> Mkap:i a1:a2:s h              m
>>
=>      i       s h[a:NAp a1 a2] m
遇到Mkap，表示要将栈顶两个地址合为一个NAp，并将之插入heap中

>> Slide n:i a0:...:an:s h m
>>
=>         i           s h m
这里，相当于释放掉栈顶n个地址

>> [Unwind]     (a:s) h[a:NNum n] m
=> [Unwind] (a1:a:s)  h           m

>> [Unwind]    (a:s) h[a:NAp a1 s2] m
=> [Unwind] (a1:a:s) h              m

>> [Unwind] (a0:...:an:s) h[a0:NGlobal n c] m
=>        c (a0:...:an:s) h                 m

Unwind分情况处理，栈顶节点若为NNum说明已经是最终结果了，当为NAp时说明还未找到已定义的函数因而，将a1入栈，相当于深入语法树。
遇到NGlobal时先要检查变量个数是否一致，而后才将对应的code取出，因为，global里都是已定义的函数，这些函数也是，指令流
