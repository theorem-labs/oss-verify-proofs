(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import PM_fz1Cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz2_ranges : list (Z * nat) := [(245400, 14%nat); (245648, 29%nat); (246188, 9%nat); (251228, 91%nat); (251616, 2%nat); (251644, 1%nat); (251708, 5%nat); (375692, 5%nat); (777380, 24%nat); (777508, 18%nat); (846796, 2%nat); (847072, 5%nat); (847144, 2%nat); (847176, 2%nat); (847756, 5%nat); (850012, 3%nat); (850516, 1%nat); (850660, 3%nat)].
Definition fz2_IT : itab := APC.mk_itab_ranges usegs fz2_ranges.
Lemma fz2_IT_ok : itab_sound usegs fz2_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz2_ENTRY : Z := 251708.   (* [comment removed for export] *)
Definition fz2_RET : Z := 245896.     (* [comment removed for export] *)
Definition fz2_KEEP : list fpwin := [(EVar 2, -384, 4096); (ELit 0, 868352, 895848); (ELit 0, 895856, 976052); (ELit 0, 976056, 976352); (ELit 0, 1107352, 1107912); (ELit 0, 1107920, 1107944); (ELit 0, 1109256, 1111372); (ELit 0, 1111376, 1114112)].
Definition fz2_kn0 : list kentry :=
  kn_keep fz2_KEEP (s_know fz1_ssF) ++
  [KRange (EVar 33) 16 140737479966712;
   KAlign (EVar 33) 16;
   KWr (SA (EVar 33) 0) (ELit 8);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (ELit 0) 65536) (ELit 1048576);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (EVar 2) (-8192)) (ELit 16384);
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWr (SA (ELit 0) 868352) (ELit 245760);
   KWord (SA (ELit 0) 1107947) 1 (ELit 0);
   KImg 65536 868352].
Definition fz2_sr0 : list expr := [ELit 0; ELit 251708; EAlu ALU_ADD (EVar 2) (ELit (-384)); EVar 3; ELit 976216; EVar 34; EVar 35; EVar 36; ELit 1; ELit 0; EVar 33; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; ELit 967496; ELit 0; ELit 18446744073709551608; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_ss0 : sym_state := SS fz2_ENTRY fz2_sr0 [] fz2_kn0 48%nat.
Definition fz2_W : list fpwin := [(EVar 2, -4096, 0); (EVar 33, 0, 8); (ELit 0, 967392, 967394); (ELit 0, 967400, 967424); (ELit 0, 1107368, 1107372); (ELit 0, 1107408, 1107416); (ELit 0, 1107664, 1107672)].
Definition fz2_ssF : sym_state := match srun usegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 with Some (ss', _) => ss' | None => fz2_ss0 end.
Definition fz2_srF : list expr := [ELit 0; ELit 246220; EAlu ALU_ADD (EVar 2) (ELit (-192)); EVar 3; ELit 976216; EVar 34; EVar 35; EVar 36; EVar 11; EVar 10; ELit 967392; ELit 1; ELit 16; ELit 0; ELit 0; ELit 0; ELit 0; EVar 43; ELit 967392; ELit 967400; ELit 967392; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_exports : list (Z * list byte) := [].
Definition fz2_wexports : list wexp := [(EVar 2, -80, 8%nat, EVar 24); (EVar 2, -72, 8%nat, EVar 23); (EVar 2, -64, 8%nat, EVar 22); (EVar 2, -56, 8%nat, EVar 21); (EVar 2, -48, 8%nat, EVar 20); (EVar 2, -40, 8%nat, EVar 19); (EVar 2, -32, 8%nat, EVar 18); (EVar 2, -24, 8%nat, EVar 9); (EVar 2, -16, 8%nat, EVar 8); (EVar 2, -8, 8%nat, ELit 245008); (EVar 33, 0, 8%nat, ELit 967568); (ELit 0, 967392, 1%nat, ELit 1); (ELit 0, 967393, 1%nat, ELit 1); (ELit 0, 967400, 8%nat, EVar 33); (ELit 0, 967408, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 967416, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 967568, 8%nat, ELit 872040); (ELit 0, 1107360, 1%nat, ELit 0); (ELit 0, 1107361, 3%nat, ELit 0); (ELit 0, 1107364, 4%nat, ELit 0); (ELit 0, 1107368, 4%nat, ELit 3); (ELit 0, 1107376, 8%nat, ELit 1107384); (ELit 0, 1107384, 8%nat, ELit 0); (ELit 0, 1107392, 8%nat, ELit 524580); (ELit 0, 1107400, 8%nat, ELit 777776); (ELit 0, 1107408, 8%nat, ELit 245792); (ELit 0, 1107648, 8%nat, ELit 968184); (ELit 0, 1107656, 8%nat, ELit 245148); (ELit 0, 1107664, 8%nat, ELit 967400)].
(* [comment removed for export] *)
Lemma fz2_cert : scheck usegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 fz2_W fz2_RET fz2_srF fz2_exports fz2_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
