Verifying Libsodium with VeriFast
=================================

I, [Bart Jacobs](http://www.cs.kuleuven.be/~bartj), am, in this [Libsodium](http://www.libsodium.org) fork,
adding [VeriFast](http://www.cs.kuleuven.be/~bartj/verifast/) annotations to some Libsodium functions
such that these functions are accepted by VeriFast, which implies that they are free from illegal memory accesses.

At this point, VeriFast accepts file `src/libsodium/crypto_sign/ed25519/ref10/sign.c`.
In particular, I inserted a specification (precondition and postcondition) for function `crypto_sign_ed25519_detached`.
(I did not insert a specification for the other function in this file, `crypto_sign_ed25519`, so this function is ignored by VeriFast.)
I also inserted prototypes, with specifications, of the functions called by `crypto_sign_ed25519_detached`.

To get VeriFast's partial C frontend to successfully parse and typecheck the file, I performed some transformations. For example, I commented out all `#include` directives,
I replaced `unsigned char` by `char`, `unsigned long long` by `unsigned int`, etc.

So, at this point, this is far from being any kind of evidence about the original libsodium code. Work in progress.

To run VeriFast yourself, download the version for your operating system from the [VeriFast website](http://www.cs.kuleuven.be/~bartj/verifast/),
unzip the archive, and type `bin/vfide path/to/sign.c`. Press the Play button to run the verifier. It should show a green bar.
To see that it is actually doing something, change the file in some significant way, such as changing the size of one of the arrays, and press Play again.
You should get a red bar.

Sodium
======

Sodium is a new, easy-to-use software library for encryption,
decryption, signatures, password hashing and more.

It is a portable, cross-compilable, installable, packageable
fork of [NaCl](http://nacl.cr.yp.to/), with a compatible API, and an
extended API to improve usability even further.

Its goal is to provide all of the core operations needed to build
higher-level cryptographic tools.

Sodium supports a variety of compilers and operating systems,
including Windows (with MingW or Visual Studio, x86 and x64), iOS and Android.

## Documentation

The documentation is a work-in-progress, and is being written using
Gitbook:

* [libsodium documentation](https://download.libsodium.org/doc/) -
online, requires Javascript.
* [offline documentation](https://www.gitbook.com/book/jedisct1/libsodium/details)
in PDF, MOBI and ePUB formats.

## Community

A mailing-list is available to discuss libsodium.

In order to join, just send a random mail to `sodium-subscribe` {at}
`pureftpd` {dot} `org`.

## License

[ISC license](https://en.wikipedia.org/wiki/ISC_license).
