(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PM_fz1Cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz2_ranges : list (Z * nat) := [(245216, 41%nat); (245804, 9%nat); (249260, 3%nat); (249292, 7%nat); (249372, 5%nat); (332632, 5%nat); (734320, 24%nat); (734448, 18%nat); (803736, 2%nat); (804012, 5%nat); (804084, 2%nat); (804116, 2%nat); (804696, 5%nat); (806952, 3%nat); (807456, 1%nat); (807600, 3%nat)].
Definition fz2_IT : itab := APC.mk_itab_ranges psegs fz2_ranges.
Lemma fz2_IT_ok : itab_sound psegs fz2_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz2_ENTRY : Z := 249372.   (* [comment removed for export] *)
Definition fz2_RET : Z := 245536.     (* [comment removed for export] *)
Definition fz2_KEEP : list fpwin := [(EVar 2, -336, 4096); (ELit 0, 827392, 852792); (ELit 0, 852800, 932228); (ELit 0, 932232, 932528); (ELit 0, 1063528, 1064088); (ELit 0, 1064096, 1064120); (ELit 0, 1065432, 1067548); (ELit 0, 1067552, 1069056)].
Definition fz2_kn0 : list kentry :=
  kn_keep fz2_KEEP (s_know fz1_ssF) ++
  [KRange (EVar 33) 16 140737479966712;
   KAlign (EVar 33) 16;
   KWr (SA (EVar 33) 0) (ELit 8);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (ELit 0) 65536) (ELit 1003520);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (EVar 2) (-8192)) (ELit 16384);
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWr (SA (ELit 0) 827392) (ELit 241664);
   KWord (SA (ELit 0) 1064123) 1 (ELit 0);
   KImg 65536 827392].
Definition fz2_sr0 : list expr := [ELit 0; ELit 249372; EAlu ALU_ADD (EVar 2) (ELit (-336)); EVar 3; ELit 932392; EVar 34; EVar 35; EVar 36; ELit 1; ELit 923664; EVar 33; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; ELit 923672; ELit 0; ELit 2305843009213693951; ELit 9223372036854775800; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_ss0 : sym_state := SS fz2_ENTRY fz2_sr0 [] fz2_kn0 48%nat.
Definition fz2_W : list fpwin := [(EVar 2, -4096, 0); (EVar 33, 0, 8); (ELit 0, 923568, 923570); (ELit 0, 923576, 923600); (ELit 0, 1063544, 1063548); (ELit 0, 1063584, 1063592); (ELit 0, 1063840, 1063848)].
Definition fz2_ssF : sym_state := match srun psegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 with Some (ss', _) => ss' | None => fz2_ss0 end.
Definition fz2_srF : list expr := [ELit 0; ELit 245836; EAlu ALU_ADD (EVar 2) (ELit (-208)); EVar 3; ELit 932392; EVar 34; EVar 35; EVar 36; EVar 11; EVar 10; ELit 923568; ELit 1; ELit 16; ELit 0; ELit 0; ELit 0; EVar 42; EVar 43; ELit 923568; ELit 923576; ELit 923568; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_exports : list (Z * list byte) := [].
Definition fz2_wexports : list wexp := [(EVar 2, -80, 8%nat, EVar 24); (EVar 2, -72, 8%nat, EVar 23); (EVar 2, -64, 8%nat, EVar 22); (EVar 2, -56, 8%nat, EVar 21); (EVar 2, -48, 8%nat, EVar 20); (EVar 2, -40, 8%nat, EVar 19); (EVar 2, -32, 8%nat, EVar 18); (EVar 2, -24, 8%nat, EVar 9); (EVar 2, -16, 8%nat, EVar 8); (EVar 2, -8, 8%nat, ELit 244752); (EVar 33, 0, 8%nat, ELit 923744); (ELit 0, 923568, 1%nat, ELit 1); (ELit 0, 923569, 1%nat, ELit 1); (ELit 0, 923576, 8%nat, EVar 33); (ELit 0, 923584, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 923592, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 923744, 8%nat, ELit 828984); (ELit 0, 1063536, 1%nat, ELit 0); (ELit 0, 1063537, 3%nat, ELit 0); (ELit 0, 1063540, 4%nat, ELit 0); (ELit 0, 1063544, 4%nat, ELit 3); (ELit 0, 1063552, 8%nat, ELit 1063560); (ELit 0, 1063560, 8%nat, ELit 0); (ELit 0, 1063568, 8%nat, ELit 481520); (ELit 0, 1063576, 8%nat, ELit 734716); (ELit 0, 1063584, 8%nat, ELit 245432); (ELit 0, 1063824, 8%nat, ELit 924360); (ELit 0, 1063832, 8%nat, ELit 244892); (ELit 0, 1063840, 8%nat, ELit 923576)].
(* [comment removed for export] *)
Lemma fz2_cert : scheck psegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 fz2_W fz2_RET fz2_srF fz2_exports fz2_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
