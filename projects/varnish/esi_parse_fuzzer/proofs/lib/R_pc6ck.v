(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.

Module R_pc9y1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_poqgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma seg_end : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (FMT : list cell) (m0 : word -> option byte) (off cnt l i : Z) (o : list byte) ms,
  pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0 off cnt l i o ms ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  (forall m, ro_cells rsegs m A FMT -> ro_cells rsegs m (A + off) [C1 (Z_to_bv 8 0)]) -> (0 <= off /\ off + 1 <= Z.of_nat (cells_size FMT))%Z ->
  (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l = Z.of_nat (length o))%Z -> (Z.of_nat (length o) < 2^31)%Z ->
  evt rsegs (pc2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp B D n mode VA slots HS hs i o canary m0) ms.
Proof.
  intros until ms. intros TOP LAY HZ HOFF C0 L0 CL OL.
  unpack_top TOP. pose proof (HZ _ HF) as FZ.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PC_TOP, INT_MAX, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof (ro_cells_bound _ _ _ _ FZ) as AB0. cbn [cells_size csize Nat.add] in AB0.
  remember (A + off)%Z as A0 eqn:EA0.
  zs. zs. zs. sx. br K. clear K.
  zs. zs. zs. sx. zs. br K. clear K.
  (* [comment removed for export] *) zs. br K. clear K.
  (* [comment removed for export] *)
  zto 0x26fc8%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
  lazymatch type of FR1 with rw_cells _ ?mq _ ?cs1 => lazymatch type of FRA with rw_cells _ _ _ ?csa => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
    assert (FR : rw_cells rsegs mq (bv_unsigned sp + -544) (cs1 ++ csa ++ cs2));
    [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR1|]; cbn [cells_size csize Nat.add];
      apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split;
      [ eapply rwc_eq; [exact FRA| lia]
      | cbn [cells_size csize Nat.add]; eapply rwc_eq; [exact FR2| lia] ]
    | clear FR1 FRA FR2; cbn [app] in FR ] end end end.
  do 16 zs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold pc2_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  replace (l + cnt)%Z with (Z.of_nat (length o)) by lia.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SNK|]. split; [exact HO|].
  split; [exact APC|]. split; [exact VAA|]. split; [assumption|]. split; assumption.
Qed.
End R_pc9y1.


Module R_pcgt7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_poqgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@BUF; @CKC; @DST; @FL]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Definition LIT_HOST : list cell :=     (* [comment removed for export] *)
  [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32);
   C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46)].
Definition TXT_HOST : list byte := [Z_to_bv 8 72; Z_to_bv 8 111; Z_to_bv 8 115; Z_to_bv 8 116; Z_to_bv 8 58; Z_to_bv 8 32].
Definition LIT_SLASH : list cell := [C1 (Z_to_bv 8 47); C1 (Z_to_bv 8 0)].

Lemma seg_lit_host : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (FMT : list cell) (m0 : word -> option byte) (off cnt l i : Z) (o : list byte) ms,
  pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0 off cnt l i o ms ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  (forall m, ro_cells rsegs m A FMT -> ro_cells rsegs m (A + off) LIT_HOST) -> (0 <= off /\ off + 8 <= Z.of_nat (cells_size FMT))%Z ->
  (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + 6 < 2^31)%Z ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0
               (off + 6) (cnt + l) 6 i (o ++ TXT_HOST)) ms.
Proof.
  intros until ms. intros TOP LAY HZ HOFF C0 L0 CL.
  unpack_top TOP. pose proof (HZ _ HF) as FZ.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PC_TOP, INT_MAX, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof (ro_cells_bound _ _ _ _ FZ) as AB0. cbn [cells_size csize Nat.add] in AB0.
  pose proof (sink_plen _ _ _ _ _ _ _ _ SNK) as PL.
  unpack_sink SNK FL CKC BUF DST.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
  unfold LIT_HOST in FZ.
  remember (A + off)%Z as A0 eqn:EA0.
  (* [comment removed for export] *)
  zs. zs. zs. sx. br K. clear K.
  zs. zs. zs. sx.
  zto 0x26300%Z. sub_norm. zs. sx. br K. clear K.
  zs. sx. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  pose proof (bytes_at_prefix rsegs _ _ TXT_HOST [Z_to_bv 8 37; Z_to_bv 8 46] (ro_cells_bytes_at _ _ _ _ FZ)) as SRC.
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SRC); call_fwritex.
  zto 0x26290%Z.
  replace (l + cnt)%Z with (cnt + l)%Z by lia. replace (A0 + 6)%Z with (A + (off + 6))%Z by lia.
  apply evt_done. pack_top.
  - reflexivity.
  - rewrite fwx_total, <- HO, <- app_assoc. reflexivity.
Qed.

Lemma seg_lit_slash : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (FMT : list cell) (m0 : word -> option byte) (off cnt l i : Z) (o : list byte) ms,
  pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0 off cnt l i o ms ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  (forall m, ro_cells rsegs m A FMT -> ro_cells rsegs m (A + off) LIT_SLASH) -> (0 <= off /\ off + 2 <= Z.of_nat (cells_size FMT))%Z ->
  (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + 1 < 2^31)%Z ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0
               (off + 1) (cnt + l) 1 i (o ++ [Z_to_bv 8 47])) ms.
Proof.
  intros until ms. intros TOP LAY HZ HOFF C0 L0 CL.
  unpack_top TOP. pose proof (HZ _ HF) as FZ.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PC_TOP, INT_MAX, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof (ro_cells_bound _ _ _ _ FZ) as AB0. cbn [cells_size csize Nat.add] in AB0.
  pose proof (sink_plen _ _ _ _ _ _ _ _ SNK) as PL.
  unpack_sink SNK FL CKC BUF DST.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
  unfold LIT_SLASH in FZ.
  remember (A + off)%Z as A0 eqn:EA0.
  zs. zs. zs. sx. br K. clear K.
  zs. zs. zs. sx.
  zto 0x26300%Z. sub_norm. zs. sx. br K. clear K.
  zs. sx. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  pose proof (bytes_at_prefix rsegs _ _ [Z_to_bv 8 47] [Z_to_bv 8 0] (ro_cells_bytes_at _ _ _ _ FZ)) as SRC.
  call_fwritex.
  zto 0x26290%Z.
  replace (l + cnt)%Z with (cnt + l)%Z by lia. replace (A0 + 1)%Z with (A + (off + 1))%Z by lia.
  apply evt_done. pack_top.
  - reflexivity.
  - rewrite fwx_total, <- HO, <- app_assoc. reflexivity.
Qed.
End R_pcgt7.


Module R_pcajc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_poqgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma seg_dir_c : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (FMT : list cell) (m0 : word -> option byte) (off cnt l i : Z) (o : list byte) ms (ch : word),
  pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0 off cnt l i o ms ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  (forall m, ro_cells rsegs m A FMT -> ro_cells rsegs m (A + off) DIR_C) -> (0 <= off /\ off + 2 <= Z.of_nat (cells_size FMT))%Z ->
  nth_error slots (Z.to_nat i) = Some ch -> (0 <= i)%Z ->
  (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + 1 < 2^31)%Z ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0
               (off + 2) (cnt + l) 1 (i + 1) (o ++ out_c ch)) ms.
Proof.
  intros until ch. intros TOP LAY HZ HOFF Hch I0 C0 L0 CL.
  unpack_top TOP. pose proof (HZ _ HF) as FZ. unfold DIR_C in FZ.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PC_TOP, INT_MAX, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof (ro_cells_bound _ _ _ _ FZ) as AB0. cbn [cells_size csize Nat.add] in AB0.
  pose proof (nth_error_lt _ _ _ Hch) as IL.
  pose proof (sink_plen _ _ _ _ _ _ _ _ SNK) as PL.
  unpack_sink SNK FL CKC BUF DST.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
  remember (A + off)%Z as A0 eqn:EA0.
  (* [comment removed for export] *)
  zs. zs. zs. sx. br K. clear K.
  zs. zs. zs. sx.
  zto 0x26300%Z. sub_norm. zs. sx. br K. clear K.
  zs. sx. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_fwritex.
  (* [comment removed for export] *)
  zto 0x266a8%Z. zs. br K. clear K.
  zto 0x27010%Z.
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRA); call_lit pop_arg_int_spec by
    (first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact FRA | exact VAA | exact Hch | assumption | lia | exact APC ]).
  try clear FRA; try clear APC; try clear VAA. rename PC into FRA. rename PC0 into APC. rename POST0 into VAA. unfold va_area in VAA.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  rewrite (le1_byte (sx32 ch)), sx32_mod256. mem_after_store_opt.
  (* [comment removed for export] *)
  zto 0x26b70%Z. zs. sx. br K. clear K.
  zto 0x26c04%Z. rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_fwritex.
  zto 0x26ca8%Z.
  pose proof (rw_cells_read4_C8 rsegs _ _ _ 16 _ (Z_to_bv 64 (bv_unsigned sp + -544 + 16)) FR1 eq_refl ltac:(unfold wa; f_equal; lia)) as RD4.
  zto 0x26d2c%Z. clear RD4. rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  pose proof (rw_cells_bytes_at_cell rsegs _ _ _ 47 _ FR2 eq_refl) as BCH. cbn [cbytes] in BCH.
  replace (bv_unsigned sp + -416 + Z.of_nat 47)%Z with (bv_unsigned sp + -369)%Z in BCH by lia.
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_fwritex.
  (* [comment removed for export] *)
  zto 0x26290%Z.
  replace (l + cnt)%Z with (cnt + l)%Z by lia. replace (A0 + 2)%Z with (A + (off + 2))%Z by lia.
  apply fr1_recast in FR1. apply fra_recast in FRA. apply fr2_recast3 in FR2. cbn [Nat.add] in FR2.
  apply evt_done. pack_top.
  - reflexivity.
  - rewrite fwx_total, <- HO, <- app_assoc. reflexivity.
Qed.
End R_pcajc.


Module R_stmbf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition strnlen_entry := 0x2b41c%Z.

(* [comment removed for export] *)
Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt rsegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b41c) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call memchr_spec.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
End R_stmbf.

Module R_pc429.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0 R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_stmbf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_poqgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma strnlen_res_bound : forall p hs A, (0 <= p)%Z -> memchr_ok A 0 p hs ->
  (0 <= strnlen_res p hs <= p /\ strnlen_res p hs <= Z.of_nat (length hs))%Z.
Proof.
  intros p hs A Hp OK. unfold strnlen_res, memchr_ok in *.
  destruct (find_byte 0 (firstn (Z.to_nat p) hs)) as [j|] eqn:E.
  - pose proof (proj1 (find_byte_Some _ _ _ E)) as L. rewrite firstn_length in L. lia.
  - lia.
Qed.

Lemma lxor_sign_small : forall y, (0 <= y < 9223372036854775808)%Z ->
  Z.lxor y 9223372036854775808 = (y + 9223372036854775808)%Z.
Proof. intros. change 9223372036854775808%Z with (2^63)%Z. apply zb_lxor_pow2_small; lia. Qed.

Lemma seg_dir_s : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (FMT : list cell) (m0 : word -> option byte) (off cnt l i : Z) (o : list byte) ms (P : word),
  pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0 off cnt l i o ms ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  (forall m, ro_cells rsegs m A FMT -> ro_cells rsegs m (A + off) DIR_S) -> (0 <= off /\ off + 4 <= Z.of_nat (cells_size FMT))%Z ->
  nth_error slots (Z.to_nat i) = Some P -> nth_error slots (Z.to_nat (i + 1)) = Some (Z_to_bv 64 HS) -> (0 <= i)%Z ->
  (0 <= sint32 P < INT_MAX)%Z -> (0 < HS)%Z -> memchr_ok HS 0 (sint32 P) hs ->
  (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + Z.of_nat (length hs) < 2^31)%Z ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m0
               (off + 4) (cnt + l) (strnlen_res (sint32 P) hs) (i + 2) (o ++ out_s P hs)) ms.
Proof.
  intros until P. intros TOP LAY HZ HOFF HP HSs I0 P0 HS0 OK C0 L0 CL.
  unpack_top TOP. pose proof (HZ _ HF) as FZ. unfold DIR_S in FZ.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PC_TOP, INT_MAX, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof (ro_cells_bound _ _ _ _ FZ) as AB0. cbn [cells_size csize Nat.add] in AB0.
  pose proof (nth_error_lt _ _ _ HP) as IL. pose proof (nth_error_lt _ _ _ HSs) as IL2.
  pose proof (sint32_range P) as PR.
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK) as LR.
  pose proof (sink_plen _ _ _ _ _ _ _ _ SNK) as PL.
  unpack_sink SNK FL CKC BUF DST.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
  remember (A + off)%Z as A0 eqn:EA0.
  (* [comment removed for export] *)
  zs. zs. zs. sx. br K. clear K.
  zs. zs. zs. sx.
  zto 0x26300%Z. sub_norm. zs. sx. br K. clear K.
  zs. sx. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  call_fwritex.
  (* [comment removed for export] *)
  zto 0x265d0%Z. zs. br K. clear K.
  zs. zs. zs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    pose proof (rw_cells_store_ok_at rsegs mq (bv_unsigned sp) _ 0 _ 8 sp APC eq_refl eq_refl
                  ltac:(symmetry; apply wa_of_var; lia)) as STOK end.
  step. clear STOK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq sp ?bs) _) =>
    replace (write_to_mem mq sp bs) with (write_to_mem mq (wa (bv_unsigned sp + Z.of_nat 0)) bs)
      by (f_equal; (apply wa_of_var + (symmetry; apply wa_of_var)); lia) end.
  zsimp. fix_bstore. mem_after_store.
  pose proof (va_read4 _ VA slots i P (Z_to_bv 64 (VA + 8 * i)) VAA HP I0 eq_refl) as RD.
  zs. clear RD. change (sx32 P) with (Z_to_bv 64 (sint32 P)).
  zs.
  (* [comment removed for export] *)
  zs. rewrite lxor_sign_small by lia.
  match goal with |- context [(?a <? ?b)%Z] => replace (a <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia) end. cbn [Z.b2z].
  zs.
  (* [comment removed for export] *)
  zto 0x266a8%Z. zs. br K. clear K.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
  zto 0x27010%Z.
  call_lit pop_arg_ptr_spec by
    (first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact FRA | exact VAA | exact HSs | assumption | lia | exact APC ]).
  try clear FRA; try clear APC; try clear VAA. rename PC into FRA. rename PC0 into APC. rename POST0 into VAA. unfold va_area in VAA.
  (* [comment removed for export] *)
  rdf. zto 0x267c4%Z. zs. br K. clear K.
  zs. zs. br K. clear K.
  zto 0x2b41c%Z.
  call_lit strnlen_spec by (idtac;
    lazymatch goal with
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; exact HSB
    | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; exact OK
    | |- mem_inv _ _ => assumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  try match goal with H : bytes_at _ _ (bv_unsigned _) _ |- _ => rewrite ?unsigned_lit in H by lia end.
  set (L := strnlen_res (sint32 P) hs) in *.
  (* [comment removed for export] *)
  zs. zs. br K. clear K.
  (* [comment removed for export] *)
  zto 0x26b3c%Z. sub_norm. sx. zs. br K. clear K.
  zs. zs. sx. zs. zs. sx. zs. br K. clear K.
  zs. zs. zs. sx. zs. zs. zs. br K. clear K.
  zs. zs. br K. clear K.
  zto 0x26b88%Z. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  call_fwritex.
  zto 0x26ca8%Z.
  pose proof (rw_cells_read4_C8 rsegs _ _ _ 16 _ (Z_to_bv 64 (bv_unsigned sp + -544 + 16)) FR1 eq_refl ltac:(unfold wa; f_equal; lia)) as RD4.
  zs. clear RD4. unfold sx32. zsimp. sx. zs. br K. clear K.
  rdf. zto 0x258a4%Z.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    assert (SRC : bytes_at rsegs mq HS (firstn (Z.to_nat L) hs))
      by (apply (bytes_at_prefix rsegs mq HS (firstn (Z.to_nat L) hs) (skipn (Z.to_nat L) hs)); rewrite firstn_skipn; assumption) end.
  call_fwritex.
  (* [comment removed for export] *)
  zto 0x26290%Z.
  replace (l + cnt)%Z with (cnt + l)%Z by lia. replace (A0 + 4)%Z with (A + (off + 4))%Z by lia.
  replace (0 + L)%Z with L by lia. replace (i + 1 + 1)%Z with (i + 2)%Z in APC by lia.
  apply fr1_recast in FR1. apply fra_recast in FRA.
  apply evt_done. pack_top.
  - reflexivity.
  - rewrite fwx_total, <- HO, <- app_assoc. reflexivity.
Qed.
End R_pc429.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_poqgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pc9y1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcajc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pc429.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Definition PRE_C (slots : list word) (HS : Z) (hs : list byte) : Prop := exists ch, nth_error slots 0 = Some ch.
Definition OUT_C (slots : list word) (hs : list byte) : list byte :=
  match nth_error slots 0 with Some ch => out_c ch | None => [] end.

(* [comment removed for export] *)
Definition str_arg_ok (P : word) (HS : Z) (hs : list byte) : Prop :=
  (0 <= sint32 P < INT_MAX)%Z /\ (0 < HS)%Z /\ memchr_ok HS 0 (sint32 P) hs /\ (Z.of_nat (length hs) < 2^31 - 16)%Z.
Definition PRE_PFX (slots : list word) (HS : Z) (hs : list byte) : Prop :=
  exists P, nth_error slots 0 = Some P /\ nth_error slots 1 = Some (Z_to_bv 64 HS) /\ str_arg_ok P HS hs.
Definition OUT_PFX (slots : list word) (hs : list byte) : list byte :=
  match nth_error slots 0 with Some P => out_s P hs ++ [Z_to_bv 8 47] | None => [] end.
Definition PRE_HOST (slots : list word) (HS : Z) (hs : list byte) : Prop :=
  exists P ch, nth_error slots 0 = Some P /\ nth_error slots 1 = Some (Z_to_bv 64 HS) /\ nth_error slots 2 = Some ch /\ str_arg_ok P HS hs.
Definition OUT_HOST (slots : list word) (hs : list byte) : list byte :=
  match nth_error slots 0, nth_error slots 2 with
  | Some P, Some ch => TXT_HOST ++ out_s P hs ++ out_c ch
  | _, _ => []
  end.

Lemma ro_cells_sub : forall segs m A cs pre mid post off,
  cs = pre ++ mid ++ post -> Z.of_nat (cells_size pre) = off -> ro_cells segs m A cs -> ro_cells segs m (A + off) mid.
Proof.
  intros segs m A cs pre mid post off -> <- H.
  apply (proj1 (ro_cells_app segs m A pre (mid ++ post))) in H. destruct H as [_ H].
  apply (proj1 (ro_cells_app segs m _ mid post)) in H. destruct H as [H _]. exact H.
Qed.

Lemma out_s_length : forall P HS hs, str_arg_ok P HS hs -> Z.of_nat (length (out_s P hs)) = strnlen_res (sint32 P) hs.
Proof.
  (intros P HS hs; (first [ intro dR_3; dand4 dR_3 as P0 _ OK _ | intros (P0 & _ & OK & _) ])). unfold out_s.
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK). rewrite firstn_length. lia.
Qed.

Ltac lay := unfold pc_layout; cbv zeta; cbn [cells_size csize Nat.add]; unfold RO_TOP, GLOBALS_TOP, PC2_DEPTH, dst_ok, IMG_LO, IMG_HI in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia].
Ltac hz pre mid post := intros mm Hm; exact (ro_cells_sub rsegs mm _ _ pre mid post _ eq_refl eq_refl Hm).

Lemma pc2_c : pass2_stmt FMT_C 3 1 PRE_C OUT_C.
Proof.
  unfold pass2_stmt. intros until canary. cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 ST HF SSP SNK APC VAA HSB [ch Hch] MI HFp HB LO GT VLO VHI ARL ART GD DLO HSL HSD.
  unfold OUT_C. rewrite Hch.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (LAY : pc_layout sp lo A Fp B D n VA slots HS hs FMT_C) by lay.
  eapply evt_cut. { eapply seg_entry; eassumption. }
  cbv beta. intros ms1 T1.
  eapply evt_cut.
  { eapply (seg_dir_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_C _ 0 0 0 0 []);
    [ exact T1 | exact LAY | hz (@nil cell) DIR_C [C1 (Z_to_bv 8 0)] | cbn; lia | exact Hch | lia | lia | lia | lia ]. }
  cbv beta. intros ms2 T2. cbn [app Z.add] in T2.
  eapply (seg_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_C);
    [ exact T2 | exact LAY | hz DIR_C [C1 (Z_to_bv 8 0)] (@nil cell) | cbn; lia | lia | lia | cbn; lia | cbn; lia ].
Qed.

Lemma pc2_pfx : pass2_stmt FMT_PFX 6 2 PRE_PFX OUT_PFX.
Proof.
  unfold pass2_stmt. intros until canary. cbv zeta.
  (intros Ha0 Ha1 Ha2 Ha3 Ha4 ST HF SSP SNK APC VAA HSB; (first [ intro dR_4; dand4 dR_4 as P HP HSs OKS | intros (P & HP & HSs & OKS) ]); intros MI HFp HB LO GT VLO VHI ARL ART GD DLO HSL HSD).
  unfold OUT_PFX. rewrite HP. pose proof (out_s_length _ _ _ OKS) as OL. (first [ dand4 OKS as P0 HS0 OK LH | destruct OKS as (P0 & HS0 & OK & LH) ]).
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK) as LR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (LAY : pc_layout sp lo A Fp B D n VA slots HS hs FMT_PFX) by lay.
  eapply evt_cut. { eapply seg_entry; eassumption. }
  cbv beta. intros ms1 T1.
  eapply evt_cut.
  { eapply (seg_dir_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_PFX _ 0 0 0 0 []);
    [ exact T1 | exact LAY | hz (@nil cell) DIR_S [C1 (Z_to_bv 8 47); C1 (Z_to_bv 8 0)] | cbn; lia
    | exact HP | exact HSs | lia | exact P0 | exact HS0 | exact OK | lia | lia | lia ]. }
  cbv beta. intros ms2 T2. cbn [app Z.add] in T2.
  eapply evt_cut.
  { eapply (seg_lit_slash _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_PFX);
    [ exact T2 | exact LAY | hz DIR_S LIT_SLASH (@nil cell) | cbn; lia | lia | lia | lia ]. }
  cbv beta. intros ms3 T3.
  eapply (seg_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_PFX);
    [ exact T3 | exact LAY | hz (DIR_S ++ [C1 (Z_to_bv 8 47)]) [C1 (Z_to_bv 8 0)] (@nil cell) | cbn; lia | lia | lia
    | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia ].
Qed.

Lemma pc2_host : pass2_stmt FMT_HOST 13 3 PRE_HOST OUT_HOST.
Proof.
  unfold pass2_stmt. intros until canary. cbv zeta.
  (intros Ha0 Ha1 Ha2 Ha3 Ha4 ST HF SSP SNK APC VAA HSB; (first [ intro dR_5; dand6 dR_5 as P ch HP HSs Hch OKS | intros (P & ch & HP & HSs & Hch & OKS) ]); intros MI HFp HB LO GT VLO VHI ARL ART GD DLO HSL HSD).
  unfold OUT_HOST. rewrite HP, Hch. pose proof (out_s_length _ _ _ OKS) as OL. (first [ dand4 OKS as P0 HS0 OK LH | destruct OKS as (P0 & HS0 & OK & LH) ]).
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK) as LR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (LAY : pc_layout sp lo A Fp B D n VA slots HS hs FMT_HOST) by lay.
  eapply evt_cut. { eapply seg_entry; eassumption. }
  cbv beta. intros ms1 T1.
  eapply evt_cut.
  { eapply (seg_lit_host _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_HOST _ 0 0 0 0 []);
    [ exact T1 | exact LAY | hz (@nil cell) LIT_HOST [C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99); C1 (Z_to_bv 8 0)]
    | cbn; lia | lia | lia | lia ]. }
  cbv beta. intros ms2 T2. cbn [app Z.add] in T2.
  eapply evt_cut.
  { eapply (seg_dir_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_HOST);
    [ exact T2 | exact LAY
    | hz [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32)]
         DIR_S [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99); C1 (Z_to_bv 8 0)]
    | cbn; lia | exact HP | exact HSs | lia | exact P0 | exact HS0 | exact OK | lia | lia | lia ]. }
  cbv beta. intros ms3 T3. cbn [Z.add] in T3.
  eapply evt_cut.
  { eapply (seg_dir_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_HOST);
    [ exact T3 | exact LAY
    | hz [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32);
          C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115)]
         DIR_C [C1 (Z_to_bv 8 0)]
    | cbn; lia | exact Hch | lia | lia | lia | lia ]. }
  cbv beta. intros ms4 T4. cbn [Z.add] in T4. rewrite <- !app_assoc in T4.
  eapply (seg_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FMT_HOST);
    [ exact T4 | exact LAY
    | hz [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32);
          C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99)]
         [C1 (Z_to_bv 8 0)] (@nil cell)
    | cbn; lia | lia | lia
    | unfold TXT_HOST, out_c; rewrite !length_app; cbn [length Nat.add]; lia
    | unfold TXT_HOST, out_c; rewrite !length_app; cbn [length Nat.add]; lia ].
Qed.
