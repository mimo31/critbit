UROP project @ Programming Languages & Verification @ MIT CSAIL

## File Structure
- `GenerUtil.v`: basic general utilities
- `KeyUtil.v`: utilities specific to the trees' keys (`list bool`)
- `SeqAccess.v`: more general utilies for working with lists and zero-extended sequences
- `PrefixCritical.v`: utilities for working with prefixes of `list bool` and with critical bits of pairs of tree keys
- `Front.v`: (roughly) the definition of crit-bit trees and the unverified operations on them
- `Main.v`: (roughly) the proof internals
- `Theorem.v`: (roughly) the key theorems specifying the behavior of the definitions in `Front`


-> "(roughly)" because the boundaries between `Front`, `Main`, and `Theorem` are not very sharp
