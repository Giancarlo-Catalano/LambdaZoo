# LambdaZoo
This is just a simple program to experiment with implementing lambda calculus somewhat efficiently, but also in a simple manner.

It uses De Bruijn indexing, and had the original purpose of finding how complex it is to enumerate lambda expressions.
Its main capabilities are:
* Alpha reduction and clean variable naming
* Calls expressions by their usual name if they are detected
* enumeration of lambda expressions by depth

The main function is `showZoo` , which takes an integer n as its parameter. It will show all the lambda expressions of depth at most n.
It tries to prune out all the identical expressions, but of course it cannot detect equality :<, damn computability.
