- Removed invariant that bound variables are positive and free variables are negative
  This is too difficult to maintain (and generate reliably).
  
- Fixed bug in "unique" name conversion. Need to store the map in an environment monad
  instead of a state monad to correctly handle cases like (\x1. (\x1. x1) x1)
  Also, with change to free variables above, initialized renaming with max free var + 1.

- Added "unique" based alpha-equality. Traversal over the two terms to map corresponding 
  variable names to the same identifier.
