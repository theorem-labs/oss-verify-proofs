From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require RowsHtUbsan HULeafTail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ubsan_closed := RowsHtUbsan.strong_universal_error_free_hashtable_ubsan HULeafTail.h0_leaf_tail.
