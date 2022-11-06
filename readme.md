# Compose (🚧 WIP)

An attempt at a new live-coding language/IDE for sound synthesis, based primarily on the philosophy:

- Everything can be composed and combined
  - Lots of overloading: most types can be combined with most operators, e.g. multiply samples by patterns, or other samples (FM), or effects, or effects by modulators, etc, etc.
- As high level as possible, to bridge the gap between code and actual listenable music
- "Bring your own samples" (and midi patterns etc)
  - (Real music is based on lots of data, let's not kid ourselves into thinking we can get away with only code)
- An actual programming language, that can be read first, executed second
  - Esoteric languages are fun, but not scalable/usable
  - Keep the syntax simple and elegant — I'm starting off from Rust syntax
  - You should be able to teach beginner coding with it. And it will be fun, because you can make music! 🎶
  - The IDE will be simple but helpful — it will have intellisense and syntax highlighting

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
