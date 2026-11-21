(* THE SHARED SIGNATURE OF THE LAYOUT TEXT, THE LIST FORM (edition 3 of the
   signature; editions 1 and 2 had predicates for the maps and stay on disk).
   Field NAMES and TYPES only: no value, no image fact. Each image's layout text is
   `Module L <: LAYOUT. <the fields' values> End L.` (the check seals nothing).
   EVERY FIELD IS DATA: a numeral (a label, a size) or a LIST.
   The names are the walk's own of today. THE MAPS' NAMES OF TODAY NAME THE LISTS HERE; the predicates of the
   same names stand in the shared base text, defined by the meaning function over these lists.
   A MAP FIELD HOLDS THE JOIN POINT's OWN ENTRIES; the shared base text says which shared pieces (s_fix, s_vars)
   a join point's map takes in besides, as today's base text does.
   SIX FIELDS ARE NEW NAMES (each is a join point whose register facts today stand inline in a continuation
   statement or under two flags): s_regs_reload_a1, s_regs_reload_ra (with s_regs_reload: the three entries of
   the reload place), s_regs_badmsg_s11, s_regs_badmsg_s10, s_regs_badmsg_a3 (the three error places). *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import SQuant.
Import ListNotations.
Open Scope Z_scope.

