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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz1_ranges : list (Z * nat) := [(245012, 51%nat); (245464, 18%nat); (245768, 9%nat); (249340, 8%nat); (251588, 18%nat); (251684, 38%nat); (252192, 22%nat); (319752, 2%nat); (320372, 9%nat); (320428, 25%nat); (332552, 15%nat); (332632, 5%nat)].
Definition fz1_IT : itab := APC.mk_itab_ranges psegs fz1_ranges.
Lemma fz1_IT_ok : itab_sound psegs fz1_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz1_ENTRY : Z := 245464.   (* [comment removed for export] *)
Definition fz1_RET : Z := 824016.     (* [comment removed for export] *)
Definition fz1_kn0 : list kentry :=
  [KRange (EVar 2) 140735332499456 18446744073709551456;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (ELit 0) 829000) 8 (ELit 319752);
   KWord (SA (ELit 0) 829016) 8 (ELit 257204);
   KWord (SA (ELit 0) 852424) 8 (ELit 828440);
   KWord (SA (ELit 0) 828688) 8 (ELit 73242);
   KWord (SA (ELit 0) 1064123) 1 (ELit 0);
   KWord (SA (ELit 0) 1063536) 1 (ELit 0);
   KWord (SA (ELit 0) 1063537) 3 (ELit 0);
   KWord (SA (ELit 0) 1063540) 4 (ELit 0);
   KWord (SA (ELit 0) 1063544) 4 (ELit 2);
   KWord (SA (ELit 0) 1063552) 8 (ELit 1063560);
   KWord (SA (ELit 0) 1063560) 8 (ELit 0);
   KWord (SA (ELit 0) 1063568) 8 (ELit 481520);
   KWord (SA (ELit 0) 1063576) 8 (ELit 734716);
   KWord (SA (ELit 0) 1063584) 8 (ELit 0);
   KWord (SA (ELit 0) 1063824) 8 (ELit 924360);
   KWord (SA (ELit 0) 1063832) 8 (ELit 244892);
   KWord (SA (ELit 0) 1063840) 8 (ELit 0);
   KImg 65536 827392;
   KImg 923568 923792;
   KWr (SA (ELit 0) 827392) (ELit 241664)].
Definition fz1_sr0 : list expr := [ELit 0; ELit 244752; EVar 2; EVar 3; ELit 932392; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_ss0 : sym_state := SS fz1_ENTRY fz1_sr0 [] fz1_kn0 33%nat.
Definition fz1_W : list fpwin := [(EVar 2, -4096, 0); (ELit 0, 923568, 923792)].
Definition fz1_ssF : sym_state := match srun psegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 with Some (ss', _) => ss' | None => fz1_ss0 end.
Definition fz1_srF : list expr := [ELit 0; ELit 249372; EAlu ALU_ADD (EVar 2) (ELit (-336)); EVar 3; ELit 932392; EVar 5; EVar 6; EVar 7; ELit 1; ELit 923664; ELit 8; ELit 1; ELit 1; ELit 0; EVar 14; EVar 15; EVar 16; EVar 17; ELit 923672; ELit 0; ELit 2305843009213693951; ELit 9223372036854775800; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_exports : list (Z * list byte) := [].
Definition fz1_wexports : list wexp := [].
(* [comment removed for export] *)
Lemma fz1_cert : scheck_k psegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 fz1_W fz1_RET fz1_srF (s_know fz1_ssF) fz1_exports fz1_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
