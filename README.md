# YAP
YAP - **Y**et **A**nother **P**arser - CirC's IR parser for PEEV project.

YAP parses the intermediate representation of [CirC](https://github.com/circify/circ) into the Operations List (OpL).
The OpL is used in [PEEV](https://github.com/OmarAlmighty/PEEV) to create a program based on the BGV homomorphic encryption scheme with [Rinocchio](https://github.com/zkFHE/ringSNARK/tree/main) ZKP.

# Structure
The [benchmarks](https://github.com/OmarAlmighty/YAP/tree/main/benchmarks) directory includes the programs used to evaluate the framework. Each subdirectory has 3 files:
* .zok - the source code of the program written in Z#.
* .ir - the intermediate repersentation of CirC.
* .opl - the parsed IR that is passed to PEEV.

The [parse.cpp](https://github.com/OmarAlmighty/YAP/blob/main/parse.cpp) file is the parser source code. YAP supports only instructions that are compatible with homomorphic encryption (e.g., addition and multiplication). The following list of instructions are parsed by YAP: `bvadd`, `bvsub`, `bvmul`, `bv2pf`, `select`, `array`, `store`, `=`, `not`, `ite`, `#` for defining a value, and `'` for referencing an index.

# How to run
## Build
```
git clone https://github.com/OmarAlmighty/YAP.git
cd YAP
mkdir build && cd build && cmake ..
cd .. && cmake --build build
```
## Run
Then navigate to the binary path and pass the IR file as a command-line argument.
e.g.,
```
Parser.exe dot_product_v8.ir
```
There will be two ouptut files: `.py` used for debugging and testing purposes, and `.opl` that is passed to PEEV.

If you want to write your program in CirC, you will need to modify it to print the IR:
1. Go to the `circ.rs` file: https://github.com/circify/circ/blob/6133414b44b8892e25f2c1803f2f87624ccf1d6e/examples/circ.rs#L298-L302
2. Append the following line: `println!("{0}", circ::ir::term::text::serialize_computation(cs));`
3. So, your code will look like this:
<pre><code>
                         <strong>...</strong>
   trace!("IR: {}", circ::ir::term::text::serialize_computation(cs));
   let mut r1cs = to_r1cs(cs, cfg());
   <strong>println!("{0}", circ::ir::term::text::serialize_computation(cs));</strong>
   println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
                         <strong>...</strong>
</code></pre>

# Requirements
The project needs [Boost](https://www.boost.org/) library.

## Acknowledgments
This work was supported by the National Science Foundation (Award #2239334).
