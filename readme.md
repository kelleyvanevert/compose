# Compose (🚧 WIP)

An attempt at a new live-coding language/IDE for sound synthesis, based primarily on the philosophy of **composition**.

It will consist of:

- Parser
- Language runtime
- Sound synthesis library
- IDE

I'm writing most of it in Rust, for performance (especially of the sound synthesis library) and as a pet project to learn Rust. The IDE will probably be web-based though, because it's easier to build UIs in web, and I want it to be actually used :P Rust will therefore run in webassembly.

Example code

```
let make_kick = fn(s) {
  (s + S) * E
};

let main = make_kick(S) * P;
```
