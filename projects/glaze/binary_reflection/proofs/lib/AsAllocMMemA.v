(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition ARB : word := Z_to_bv 64 0.
Lemma ARB_ok : (U ARB mod 2 = 0)%Z /\ (U ARB + 2 ^ 24 < 2 ^ 64)%Z.
Proof using. split; vm_compute; [reflexivity | exact eq_refl]. Qed.

(* [comment removed for export] *)
Definition asan_mp_tab : mp_tab := MPT ARB asan_ui_tab 0xff260 (Z_to_bv 64 0x108258) 0x10827c.
Lemma asan_mp_tab_ok : mp_tab_ok ASEGS asan_mp_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab ARB] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold mp_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tai_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold gmc_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold gpc_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6e58c D_6e58c F_6e590 D_6e590.
  - gaddr2_tac F_75bc0 D_75bc0 F_75bc4 D_75bc4.
  - gloadw_tac F_7693c D_7693c F_76940 D_76940.
  - exact asan_ui_tab_ok.
  - reflexivity.
  - exact ARB_ok.
Qed.

(* [comment removed for export] *)
Definition asan_am_tab : am_tab :=
  AMT ARB (Z_to_bv 64 0x103f18) 0x10490 (Z_to_bv 64 0x10500) (Z_to_bv 64 0x10600) 0x108258 0x1897e2.
Lemma asan_am_tab_ok : am_tab_ok ASEGS asan_am_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss asan_am_tab ARB] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold am_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold al_words in G in change_no_check G' end). code_ato_vm.
  - gauipc_addi_tac F_4bad4 D_4bad4 F_4bae0 D_4bae0.
  - gload_tac F_4bbdc D_4bbdc F_4bbe0 D_4bbe0.
  - gauipc_addi_tac F_4bbf0 D_4bbf0 F_4bbf8 D_4bbf8.
  - (lazymatch goal with |- ?G => let G' := eval unfold ain_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_74ca4 D_74ca4 F_74ca8 D_74ca8.
  - (lazymatch goal with |- ?G => let G' := eval unfold rss_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_7a96c D_7a96c F_7a970 D_7a970.
  - (lazymatch goal with |- ?G => let G' := eval unfold rzl_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_51170 D_51170 F_51174 D_51174.
  - gauipc_addi_tac F_51178 D_51178 F_51180 D_51180.
  - exact ARB_ok.
Qed.

(* [comment removed for export] *)
Lemma asan_HAL : code_ato ASEGS ARB 0x4bb24 al_words.
Proof using fx. exact (ato_al _ _ asan_am_tab_ok). Qed.
Lemma asan_HCB : code_ato ASEGS ARB 0x5027c cb_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold cb_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GTRB : gt_rb asan_gct_tab = ARB.
Proof using. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_HAL2 : code_ato ASEGS ARB 0x4bdc4 al2_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold al2_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GLSB : gload ASEGS ARB 0x4bee4 10 0xff270.
Proof using. gload_tac F_4bedc D_4bedc F_4bee0 D_4bee0. Qed.
Lemma asan_CPM : code_ato ASEGS ARB 0x6f5fc cpm_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold cpm_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GCPM : gloadb ASEGS ARB 0x6f5fc 10 0x106ddc.
Proof using. gload_tac F_6f5f4 D_6f5f4 F_6f5f8 D_6f5f8. Qed.
Lemma asan_GLSB2 : gload ASEGS ARB 0x4bfe8 10 0xff270.
Proof using. gload_tac F_4bfe0 D_4bfe0 F_4bfe4 D_4bfe4. Qed.
Lemma asan_GLMB : gload ASEGS ARB 0x4c00c 12 0xff278.
Proof using. gload_tac F_4c004 D_4c004 F_4c008 D_4c008. Qed.
Lemma asan_GLME : gload ASEGS ARB 0x4c014 13 0xff280.
Proof using. gload_tac F_4c00c D_4c00c F_4c010 D_4c010. Qed.
Lemma asan_GLHE : gload ASEGS ARB 0x4c030 13 0xff288.
Proof using. gload_tac F_4c028 D_4c028 F_4c02c D_4c02c. Qed.
Lemma asan_GLFL : gload ASEGS ARB 0x4c04c 11 0xff268.
Proof using. gload_tac F_4c044 D_4c044 F_4c048 D_4c048. Qed.
Lemma asan_GLFL3 : gload ASEGS ARB 0x4c1d0 10 0xff268.
Proof using. gload_tac F_4c1c8 D_4c1c8 F_4c1cc D_4c1cc. Qed.
Lemma asan_GLRMS : gload ASEGS ARB 0x4c1ec 11 0xff290.
Proof using. gload_tac F_4c1e4 D_4c1e4 F_4c1e8 D_4c1e8. Qed.

(* [comment removed for export] *)
Lemma asan_HAL3 : code_ato ASEGS ARB 0x4c204 al3_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold al3_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_HAM2 : code_ato ASEGS ARB 0x4baf4 am2_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold am2_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_HLSN : code_ato ASEGS ARB 0x9bf80 lsn_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold lsn_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GLSN : gload ASEGS ARB 0x9bf80 10 0xffec8.
Proof using. gload_tac F_9bf78 D_9bf78 F_9bf7c D_9bf7c. Qed.
Lemma asan_GMAG : gload ASEGS ARB 0x4c238 10 0x103b8.
Proof using. gload_tac F_4c230 D_4c230 F_4c234 D_4c234. Qed.

(* [comment removed for export] *)
Lemma asan_HGTS : code_ato ASEGS ARB 0x77588 gts_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gts_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_HRMH : code_ato ASEGS ARB 0x7cb90 rmh_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold rmh_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GRMH : gaddr2 ASEGS ARB 0x7cbb0 10 18 (Z_to_bv 64 0x199040).
Proof using. gaddr2_tac F_7cba8 D_7cba8 F_7cbac D_7cbac. Qed.
Lemma asan_HHK : code_ato ASEGS ARB 0x7cc48 [Some W_7cc40].
Proof using. code_ato_vm. Qed.

End FPGen.
End AsAllocMI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 AsAllocMI.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma rdn_wbytes_hitw : forall segs m (a v : word) (n : nat),
  (U a + Z.of_nat n <= 2 ^ 64)%Z -> rdn segs (wbytes m a (word_to_le_bytes n v)) a n = Some (word_to_le_bytes n v).
Proof using.
  intros segs m a v n Hnw. pose proof (rdn_wbytes_hit segs (word_to_le_bytes n v) m a) as H'.
  rewrite length_N_to_le_bytes in H'. apply H'. exact Hnw.
Qed.

(* [comment removed for export] *)
Definition ma_A (MP : word -> option byte) (S : word) (n : Z) (x18 x19 x22 x23 x24 x25 x26 x27 : word) : word -> option byte :=
  let sp := at_ S (-2128) in
  wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MP
      (at_ sp (-8)) (LE8 (at_ ARB 0x6e600))) (at_ sp (-16)) (LE8 S))
      (at_ sp (-24)) (LE8 (at_ ARB 0x4baf4))) (at_ sp (-32)) (LE8 S)) (at_ sp (-40)) (LE8 (Z_to_bv 64 n)))
      (at_ sp (-48)) (LE8 x18)) (at_ sp (-56)) (LE8 x19)) (at_ sp (-64)) (LE8 (at_ S (-2128))))
      (at_ sp (-72)) (LE8 (at_ S (-81)))) (at_ sp (-80)) (LE8 x22)) (at_ sp (-88)) (LE8 x23))
      (at_ sp (-96)) (LE8 x24)) (at_ sp (-104)) (LE8 x25)) (at_ sp (-112)) (LE8 x26))
      (at_ sp (-120)) (LE8 x27))
      (at_ sp (-136)) (LE8 (Z_to_bv 64 1))) (at_ sp (-128)) (LE8 (Z_to_bv 64 16)))
      (at_ sp (-152)) (LE8 (at_ ARB 0x4bca8))) (at_ sp (-152)) (LE8 (at_ ARB 0x4bcbc)).

(* [comment removed for export] *)
Definition ma_B (MA : word -> option byte) (S : word) (T n cnt : Z) (stw csz : word) : word -> option byte :=
  let sp := at_ S (-2272) in let thr := Z_to_bv 64 T in
  wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MA (at_ sp (-8)) (LE8 (at_ ARB 0x4bda8)))
      (at_ sp (-8)) (LE8 (at_ ARB 0x4bdc4))) (at_ sp (-16)) (LE8 (Z_to_bv 64 1))) (at_ sp (-24)) (LE8 (Z_to_bv 64 n)))
      (at_ sp (-32)) (LE8 (Z_to_bv 64 8))) (at_ sp (-40)) (LE8 (Z_to_bv 64 (needed n)))) (at_ sp (-48)) (LE8 (Z_to_bv 64 (rz n))))
    (at_ thr (208 + 80 * class_of (needed n))) (LE4 (cnt - 1))) (at_ thr 2784) (LE8 (v_add stw csz)).

(* [comment removed for export] *)
Definition ma_P2 (MP : word -> option byte) (S : word) (T n cnt : Z) (stw csz m : word) (b1 : byte)
           (x18 x19 x22 x23 x24 x25 x26 x27 : word) : word -> option byte :=
  amC_mem (ma_B (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27) S T n cnt stw csz) m b1 n.

(* [comment removed for export] *)
Lemma ma_A_eq : forall (MP : word -> option byte) (S : word) (n : Z) (r : bvmap 5 word),
  getr r 8 = S -> getr r 9 = Z_to_bv 64 n -> getr r 20 = at_ S (-2128) -> getr r 21 = at_ S (-81) ->
  am_m3 asan_am_tab r MP (at_ ARB 0x6e600) (at_ S (-2128))
  = ma_A MP S n (getr r 18) (getr r 19) (getr r 22) (getr r 23) (getr r 24) (getr r 25) (getr r 26) (getr r 27).
Proof using. intros MP S n r E8 E9 E20 E21. (lazymatch goal with |- ?G => let G' := eval unfold am_m3, am_m2, am_m1, ma_A in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [am_rb asan_am_tab] in G in change_no_check G' end). rewrite E8, E9, E20, E21. reflexivity. Qed.

Lemma ma_B_eq : forall (MA : word -> option byte) (S : word) (T n cnt : Z) (stw csz : word) (r : bvmap 5 word),
  getr r 8 = Z_to_bv 64 1 -> getr r 9 = Z_to_bv 64 n -> getr r 18 = Z_to_bv 64 8 -> getr r 19 = Z_to_bv 64 (needed n) ->
  getr r 20 = Z_to_bv 64 (rz n) ->
  amB_mem ARB r MA (at_ S (-2272)) (Z_to_bv 64 T) n cnt stw csz = ma_B MA S T n cnt stw csz.
Proof using. intros MA S T n cnt stw csz r E8 E9 E18 E19 E20. (lazymatch goal with |- ?G => let G' := eval unfold amB_mem, amB_frame, ma_B in G in change_no_check G' end). rewrite E8, E9, E18, E19, E20. reflexivity. Qed.

Section MEMA.
  Variables (MP : word -> option byte) (S : word) (T n cnt : Z) (stw csz m : word) (b1 : byte) (x18 x19 x22 x23 x24 x25 x26 x27 : word).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.   (* [comment removed for export] *)
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gm : (AIMGHI <= U m /\ U m + needed n <= U S - 3584)%Z.

  #[local] Abbreviation MA := (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27).
  #[local] Abbreviation MB := (ma_B MA S T n cnt stw csz).
  #[local] Abbreviation MC := (ma_P2 MP S T n cnt stw csz m b1 x18 x19 x22 x23 x24 x25 x26 x27).

  Lemma cofn_range : (1 <= class_of (needed n) <= 30)%Z.
  Proof using Gn. pose proof (needed_facts n Gn) as [N1 N2]. apply AsArith3.class_of_range. lia. Qed.
  Lemma rzn_range : (16 <= rz n <= 1024)%Z.
  Proof using Gn.
    pose proof (rz_log_range n). (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end).
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia.
  Qed.

  Lemma needed_rz : (rz n + 8 <= needed n)%Z /\ (needed n <= 65536)%Z.
  Proof using Gn.
    pose proof (needed_facts n Gn) as [N1 N2]. assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd : (8 <= rounded n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end); pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)); lia).
    lia.
  Qed.

  Lemma ma_A_outside : forall x : word, (U x < U S - 2280 \/ U S - 2128 <= U x)%Z -> MA x = MP x.
  Proof using GS.
    intros x Hx. pose proof (u64_range S). destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ma_A in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_at; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ma_A_grows : mem_grows MP MA.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ma_A in G in change_no_check G' end). do 19 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma ma_B_outside : forall x : word,
    (U x < U S - 2320 \/ U S - 2272 <= U x)%Z ->
    (U x < T + 208 + 80 * class_of (needed n) \/ T + 208 + 80 * class_of (needed n) + 4 <= U x)%Z ->
    (U x < T + 2784 \/ T + 2792 <= U x)%Z ->
    MB x = MA x.
  Proof using Gn GT GS.
    intros x Hx Hy Hz. pose proof (u64_range S). destruct GS as [G1 G2]. destruct GT as [G3 G4]. pose proof cofn_range. (lazymatch goal with |- ?G => let G' := eval unfold ma_B in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_at; rewrite ?at_u; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ma_B_grows : mem_grows MA MB.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ma_B in G in change_no_check G' end). do 9 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma ma_P2_outside : forall x : word, (U x < U m + rz n - 15 \/ U m + rz n - 8 <= U x)%Z -> MC x = MB x.
  Proof using Gm Gn GS.
    intros x Hx. pose proof (u64_range m). pose proof (u64_range S). destruct Gm as [G1 G2]. pose proof rzn_range. pose proof needed_rz. (lazymatch goal with |- ?G => let G' := eval unfold ma_P2, amC_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity.
  Qed.
  Lemma ma_P2_grows : mem_grows MB MC.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ma_P2, amC_mem in G in change_no_check G' end). do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Definition ma_footA (x : word) : Prop :=
    (U S - 2320 <= U x < U S - 2128)%Z
    \/ (T + 208 + 80 * class_of (needed n) <= U x < T + 208 + 80 * class_of (needed n) + 4)%Z
    \/ (T + 2784 <= U x < T + 2792)%Z
    \/ (U m + rz n - 15 <= U x < U m + rz n - 8)%Z.
  Lemma ma_P2_foot : forall x : word, MC x <> MP x -> ma_footA x.
  Proof using Gm Gn GT GS.
    intros x NE. (lazymatch goal with |- ?G => let G' := eval unfold ma_footA in G in change_no_check G' end).
    destruct (decide (MC x = MB x)) as [E1|N1]; [| pose proof (u64_range x); destruct (Z.lt_ge_cases (U x) (U m + rz n - 15)); [exfalso; apply N1; apply ma_P2_outside; lia|];
                                             destruct (Z.lt_ge_cases (U x) (U m + rz n - 8)); [lia | exfalso; apply N1; apply ma_P2_outside; lia]].
    rewrite E1 in NE.
    destruct (decide (MB x = MA x)) as [E2|N2].
    - rewrite E2 in NE. destruct (Z.lt_ge_cases (U x) (U S - 2280)); [exfalso; apply NE; apply ma_A_outside; lia|].
      destruct (Z.lt_ge_cases (U x) (U S - 2128)); [lia | exfalso; apply NE; apply ma_A_outside; lia].
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (U x) (U S - 2320)) as [L1|L1]; destruct (Z.lt_ge_cases (U x) (U S - 2272)) as [L2|L2];
      destruct (Z.lt_ge_cases (U x) (T + 208 + 80 * class_of (needed n))) as [L3|L3];
      destruct (Z.lt_ge_cases (U x) (T + 208 + 80 * class_of (needed n) + 4)) as [L4|L4];
      destruct (Z.lt_ge_cases (U x) (T + 2784)) as [L5|L5]; destruct (Z.lt_ge_cases (U x) (T + 2792)) as [L6|L6]; try lia;
      exfalso; apply N2; apply ma_B_outside; lia.
  Qed.
  Lemma ma_P2_grows_all : mem_grows MP MC.
  Proof using. eapply mem_grows_trans; [apply ma_A_grows|]. eapply mem_grows_trans; [apply ma_B_grows | apply ma_P2_grows]. Qed.

  (* [comment removed for export] *)
  Definition ma_slotsA : list (Z * word) :=
    [(-2136, at_ ARB 0x6e600); (-2144, S); (-2152, at_ ARB 0x4baf4); (-2160, S); (-2168, Z_to_bv 64 n); (-2176, x18); (-2184, x19);
     (-2192, at_ S (-2128)); (-2200, at_ S (-81)); (-2208, x22); (-2216, x23); (-2224, x24); (-2232, x25); (-2240, x26); (-2248, x27);
     (-2256, Z_to_bv 64 16); (-2264, Z_to_bv 64 1)]%Z.
  Lemma ma_P2_slotsA : forall (k : Z) (v : word), In (k, v) ma_slotsA -> rdn ASEGS MC (at_ S k) 8 = Some (LE8 v).
  Proof using Gm Gn GT GS.
    intros k v Hin. pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct GT as [G3 G4]. destruct Gm as [G5 G6].
    pose proof cofn_range. pose proof rzn_range. pose proof needed_rz.
    unfold ma_slotsA in Hin. cbn [In] in Hin.
    assert (OUT : forall k', (-2272 <= k' /\ k' + 8 <= -2128)%Z -> rdn ASEGS MC (at_ S k') 8 = rdn ASEGS MA (at_ S k') 8).
    { intros k' Hk'. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
      rewrite ma_P2_outside by lia. apply ma_B_outside; lia. }
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite OUT by lia; (lazymatch goal with |- ?G => let G' := eval unfold ma_A in G in change_no_check G' end); rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]).
    destruct Hin.
  Qed.
  Lemma ma_slotsA_range : forall (k : Z) (v : word), In (k, v) ma_slotsA -> (-2264 <= k /\ k + 8 <= -2128)%Z.
  Proof using.
    intros k v Hin. unfold ma_slotsA in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma ma_P2_above : forall x : word, (U S - 2128 <= U x)%Z -> MC x = MP x.
  Proof using Gm Gn GT GS.
    intros x Hx. pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct GT as [G3 G4]. destruct Gm as [G5 G6].
    pose proof cofn_range. pose proof rzn_range. pose proof needed_rz.
    rewrite ma_P2_outside by lia. rewrite ma_B_outside by lia. apply ma_A_outside. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ma_P2_hdr :
    MC (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))))
    /\ rdn ASEGS MC (at_ m (rz n - 14)) 2 = Some (LE2 0)
    /\ rdn ASEGS MC (at_ m (rz n - 12)) 4 = Some (LE4 n).
  Proof using Gm Gn GS.
    pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct Gm as [G5 G6]. pose proof rzn_range. pose proof needed_rz.
    (lazymatch goal with |- ?G => let G' := eval unfold ma_P2, amC_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). split; [|split].
    - rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite at_u; lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia].
      rewrite Z.sub_diag. reflexivity.
    - rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ma_P2_cnt : (U m + needed n <= T \/ T + 4096 <= U m)%Z ->
    rdn ASEGS MC (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) 4 = Some (LE4 (cnt - 1)).
  Proof using Gm Gn GT GS.
    intros GmT. pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct GT as [G3 G4]. destruct Gm as [G5 G6].
    pose proof cofn_range as Hc. pose proof rzn_range. pose proof needed_rz. pose proof (needed_facts n Gn) as [N1 N2].
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd : (8 <= rounded n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end); pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)); lia).
    assert (HB : rdn ASEGS MB (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) 4 = Some (LE4 (cnt - 1))).
    { (lazymatch goal with |- ?G => let G' := eval unfold ma_B in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. apply rdn_wbytes_hitw. rewrite at_u by (wd_ulia). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    eapply (rd_same ASEGS); [| rewrite at_u by (wd_ulia); wd_ulia_c | exact HB].
    intros x Hx. rewrite at_u in Hx by (wd_ulia). revert Hx; unorm; intros Hx. cbn in Hx. apply ma_P2_outside. lia.
  Qed.
End MEMA.
End FPGen.
