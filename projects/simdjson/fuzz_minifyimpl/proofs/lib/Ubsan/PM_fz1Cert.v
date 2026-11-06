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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz1_ranges : list (Z * nat) := [(245268, 33%nat); (245496, 10%nat); (245576, 18%nat); (245824, 18%nat); (246152, 9%nat); (251184, 11%nat); (251676, 8%nat); (254380, 18%nat); (254476, 47%nat); (255116, 22%nat); (359780, 2%nat); (360424, 9%nat); (360480, 25%nat); (375612, 15%nat); (375692, 5%nat)].
Definition fz1_IT : itab := APC.mk_itab_ranges usegs fz1_ranges.
Lemma fz1_IT_ok : itab_sound usegs fz1_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz1_ENTRY : Z := 245824.   (* [comment removed for export] *)
Definition fz1_RET : Z := 867076.     (* [comment removed for export] *)
Definition fz1_kn0 : list kentry :=
  [KRange (EVar 2) 140735332499456 18446744073709551456;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (ELit 0) 872056) 8 (ELit 359780);
   KWord (SA (ELit 0) 872072) 8 (ELit 261996);
   KWord (SA (ELit 0) 895480) 8 (ELit 871496);
   KWord (SA (ELit 0) 871744) 8 (ELit 73242);
   KWord (SA (ELit 0) 1107947) 1 (ELit 0);
   KWord (SA (ELit 0) 1107360) 1 (ELit 0);
   KWord (SA (ELit 0) 1107361) 3 (ELit 0);
   KWord (SA (ELit 0) 1107364) 4 (ELit 0);
   KWord (SA (ELit 0) 1107368) 4 (ELit 2);
   KWord (SA (ELit 0) 1107376) 8 (ELit 1107384);
   KWord (SA (ELit 0) 1107384) 8 (ELit 0);
   KWord (SA (ELit 0) 1107392) 8 (ELit 524580);
   KWord (SA (ELit 0) 1107400) 8 (ELit 777776);
   KWord (SA (ELit 0) 1107408) 8 (ELit 0);
   KWord (SA (ELit 0) 1107648) 8 (ELit 968184);
   KWord (SA (ELit 0) 1107656) 8 (ELit 245148);
   KWord (SA (ELit 0) 1107664) 8 (ELit 0);
   KImg 65536 868352;
   KImg 967392 967616;
   KWr (SA (ELit 0) 868352) (ELit 245760)].
Definition fz1_sr0 : list expr := [ELit 0; ELit 245008; EVar 2; EVar 3; ELit 976216; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_ss0 : sym_state := SS fz1_ENTRY fz1_sr0 [] fz1_kn0 33%nat.
Definition fz1_W : list fpwin := [(EVar 2, -4096, 0); (ELit 0, 967392, 967616)].
Definition fz1_ssF : sym_state := match srun usegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 with Some (ss', _) => ss' | None => fz1_ss0 end.
Definition fz1_srF : list expr := [ELit 0; ELit 251708; EAlu ALU_ADD (EVar 2) (ELit (-384)); EVar 3; ELit 976216; EVar 5; EVar 6; EVar 7; ELit 1; ELit 0; ELit 8; ELit 1; ELit 0; ELit 967400; ELit 1; EVar 15; EVar 16; EVar 17; ELit 967496; ELit 0; ELit 18446744073709551608; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_exports : list (Z * list byte) := [].
Definition fz1_wexports : list wexp := [].
(* [comment removed for export] *)
Lemma fz1_cert : scheck_k usegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 fz1_W fz1_RET fz1_srF (s_know fz1_ssF) fz1_exports fz1_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
