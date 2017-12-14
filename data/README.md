| File              | tcoq git       | Features                           | 
| ----------------- | -------------- | ---------------------------------- |
| odd-order-build6  | 4dda4fd309826e | ML/Notation has try/catch          |
| odd-order-build7  | 3700f3d0074338 | Name has uid, Name has try/catch   |
| odd-order-build12 | cd34e1ab88adb8 | Compressed format                  |
| odd-order-build14 | 10381cbddcc75f | See Note-Build-14                  |
| odd-order-build15 | 1eae82d6672fed | See Note-Build-15                  |

Notes:
- odd-order-build6 technically between 4dda4fd309826e and 3700f3d0074338

Note-Build-14:
- Compressed format:
  * Local contexts are compressed to use only identifiers.
  * Identifier table at end.
  * Fresh local context identifiers generated in different proof branches
  * Expressions are shared
  
Note-Build-15:
- Compressed format:
  * Expressions are shared.
  * Local contexts have identifiers and expression indicies
  * This takes care of shadowing appropriately (because we were not alpha-converting the rest of the context before)
