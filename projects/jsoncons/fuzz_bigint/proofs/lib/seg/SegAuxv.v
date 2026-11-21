(* SPDX-License-Identifier: MIT *)
(* The auxiliary vector of the LPS 727298f3 launch as the throw-path segment
   certificates' start knowledge states it.  [auxt r] is the vector's type words in
   [StackLayout.auxv_entries]' order (27 pairs, 29 under CONFIG_RSEQ, [r]), the same
   list as [L5ParseSpecs.auxv_types]; musl's [dl_iterate_phdr] reads every type word up
   to AT_NULL and the value of each type below AUX_CNT, then AT_PHDR, AT_PHENT and
   AT_PHNUM (pairs 13, 14, 15).  The other values are only readable ([KUnk]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition auxt (r : bool) : list Z :=
  [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
  ++ (if r then [27; 28] else []) ++ [0].
(* the vector's length in bytes: 432, or 464 under CONFIG_RSEQ *)
Definition auxlen (r : bool) : Z := 16 * Z.of_nat (length (auxt r)).
(* the facts about the vector at [EVar 32], the value of [__auxv]; [phnum] is the
   image's program-header count *)
Definition aux_kn (r : bool) (phnum : Z) : list kentry :=
  map (fun i => KWord (SA (EVar 32) (16 * Z.of_nat i)) 8 (ELit (nth i (auxt r) 0))) (seq 0 (length (auxt r)))
  ++ [KWord (SA (EVar 32) 216) 8 (ELit 65600); KWord (SA (EVar 32) 232) 8 (ELit 56); KWord (SA (EVar 32) 248) 8 (ELit phnum);
      KUnk (SA (EVar 32) 0) (ELit (auxlen r))].
