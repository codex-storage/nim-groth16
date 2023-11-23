pragma circom 2.0.0;

//
// prove a simple factorization
//

//------------------------------------------------------------------------------

template Product(n) {
  signal input  inp[n];
  signal output out;

  signal aux[n];
  aux[0] <== inp[0];
  for(var i=1; i<n; i++) {
    aux[i] <== aux[i-1] * inp[i];
  }

  out <== aux[n-1];
}

//------------------------------------------------------------------------------

// a[0]*a[1]*...*a[n-1] + b
template Main(n) {
  signal input  plus;
  signal input  inp[n];
  signal output out;

  component prod = Product(n);
  inp ==> prod.inp;
  out <== prod.out + plus;
  log("out =",out);

  out === 2023;
}

//------------------------------------------------------------------------------

component main {public [plus]} = Main(3);