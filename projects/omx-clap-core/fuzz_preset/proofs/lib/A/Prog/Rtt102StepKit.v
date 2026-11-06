(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 312 of its 359 lines of code are new or changed and 881 lines of the source are left out. *)
(* fuzz_preset: the IMAGE-GENERIC concrete steps of round_trip_text's register-only code, over {L : ptable asym}
   {PL : PAListing L} {PA : PAImg L}. Lane RttFR1 (WalkRtt102 for the text owner).
   WHY THIS FILE REPLACES Rtt102FR1KitA.v's STEPS. The B' R5 porter's B' port of this lane (the B' row R5 port at
   d1f87944c9fe, Rtt102JalB.v) measured the defect: RttFR1's first steps took the slot's word and the decoded fields
   as EVARS and discharged `plookup pl_tpi k = Some (PW ?w)` / `decode_any (Z_to_bv 32 ?w) = Some (.., ?imm, 4)` by
   `vm_compute; reflexivity`. A vm_compute over a goal with evars cannot run on the bytecode VM; at B' it TIMES OUT,
   and at A' it was this lane's whole build cost. THE FIX, as the B' R5 porter did it for addi and jal: state each slot's
   shape as ONE CLOSED BOOLEAN over the listing (`rtt_ok_*`), so the check is `vm_compute; reflexivity` on a closed
   goal, and read a call's / a relocated slot's facts off the LISTING'S OWN CERTIFICATE (YP0b.v pi_slot_check through
   YC1fP.v cert_slot) instead of recomputing them per image. rttb_jal_pcall / rttb_addi are the B' R5 porter's (B' row R5);
   the branch, auipc (PHi) and load (PLdHi) steps here are the same construction for the slots F needs, which no B'
   row had a twin for. The step proofs themselves are H5RttS4.v :118-255 (the H2H5 walk head
   1934271f1f40) through this lane's copy, at the checked word.
   A RELOCATED PAIR, GENERICALLY: `auipc rd, %hi(g)` then `l?u rd', off(rd)` is a PHi / PLdHi slot pair of the
   listing. PHi's certificate says the word is `auipc rd imm` with auipc_val pc imm = pa_val (A_HI j); PLdHi's says
   the word is a load of the asked size and sign with pa_val (A_HI j) + bv_signed imm = pa_val a + off. So the load's
   ADDRESS is pa_val a + off BY THE LISTING, at every image: no per-image offset arithmetic (A' used -0x5e4 by hand).
   rule 24: proves no function (kind: step lemma).
   Numerals: 4 (LENGTH: instruction), 12 (LENGTH: auipc's shift), 2 ^ 12 / 2 ^ 20 / 2 ^ 32 / 2 ^ 40 / 2 ^ 64
   (LENGTH). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YN2e YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation VAL := (@pa_val _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ L PI).

(* ---- the closed slot checks ---- *)
Definition rtt_ok_addi (k : Z) (rd0 rs0 : bv 5) (i0 : Z) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (OpImm ALU_ADD rd rs imm, isz) => bv_eqb rd rd0 && bv_eqb rs rs0 && (bv_signed imm =? i0) && (isz =? 4)
      | _ => false
      end
  | _ => false
  end.
Lemma rtt_ok_addi_spec : forall k rd0 rs0 i0, rtt_ok_addi k rd0 rs0 i0 = true ->
  exists w imm, plookup pl_tpi k = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd0 rs0 imm, 4%Z) /\ bv_signed imm = i0.
Proof.
intros k rd0 rs0 i0 H. unfold rtt_ok_addi in H.
destruct (plookup pl_tpi k) as [[w | | | | |] |] eqn:Hpl; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz] |] eqn:Hdec; try discriminate H.
destruct i; try discriminate H.
repeat match type of H with context [match ?o with _ => _ end] => destruct o; try discriminate H end.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hi]. apply andb_prop in H as [Hrd Hrs].
unfold bv_eqb in Hrd, Hrs. apply Z.eqb_eq in Hrd, Hrs, Hi, H4. apply bv_eq in Hrd. apply bv_eq in Hrs. subst.
exists w, imm. auto.
Qed.

(* ---- the steps ---- *)
Lemma rtt_addi : forall (W : world SEGS) regs mem md Q k (rd0 rs0 : bv 5) (i0 : Z),
  rtt_ok_addi k rd0 rs0 i0 = true -> bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_addi (getr regs rs0) i0))
               (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rd0 rs0 i0 Hok Hrd Hk0 Hk4 HK.
destruct (rtt_ok_addi_spec k rd0 rs0 i0 Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Ei.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

(* `jal ra, s` at a `PCall s 1` slot, by the listing's certificate (the B' R5 porter's Rtt102JalB.v rttb_jal_pcall) *)
Lemma rtt_jal_pcall : forall (W : world SEGS) regs mem md Q k s,
  plookup pl_tpi k = Some (PCall s 1%bv) -> 0 <= k -> k + 4 < 2 ^ 40 ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx (regupd regs 1%bv (Z_to_bv 64 (BASE + (k + 4))))
               (Z_to_bv 64 (SIGMA s)) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k s Hpl Hk0 Hk4 HK.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) (@pa_val _ L PI) SIGMA L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (@pa_val _ L PI A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as [Hck Htg]. apply andb_prop in Hck as [Hrd _].
unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq in Hrd. subst rd.
apply Z.eqb_eq in Htg.
assert (H10 : bv_eqb (1%bv : bv 5) 0 = false) by (vm_compute; reflexivity).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 wz) 1%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite H10. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  assert (Htgt : btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 (SIGMA s)).
  { unfold btgt, v_addi. rewrite unsigned_lit_small by lia.
    rewrite <- Htg. unfold zcanon, M64. rewrite Z_to_bv64_mod. reflexivity. }
  rewrite Htgt.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

(* a load at a plain PW slot: the slot's size, sign, registers and offset, closed *)
Definition rtt_ok_ld (k : Z) (rd0 rs0 : bv 5) (i0 : Z) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Load SZ8 true rd rs imm, isz) => bv_eqb rd rd0 && bv_eqb rs rs0 && (bv_signed imm =? i0) && (isz =? 4)
      | _ => false
      end
  | _ => false
  end.
Definition rtt_ok_lw (k : Z) (rd0 rs0 : bv 5) (i0 : Z) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Load SZ4 true rd rs imm, isz) => bv_eqb rd rd0 && bv_eqb rs rs0 && (bv_signed imm =? i0) && (isz =? 4)
      | _ => false
      end
  | _ => false
  end.
Lemma rtt_ok_ld_spec : forall k rd0 rs0 i0, rtt_ok_ld k rd0 rs0 i0 = true ->
  exists w imm, plookup pl_tpi k = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd0 rs0 imm, 4%Z) /\ bv_signed imm = i0.
Proof.
intros k rd0 rs0 i0 H. unfold rtt_ok_ld in H.
destruct (plookup pl_tpi k) as [[w | | | | |] |] eqn:Hpl; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz] |] eqn:Hdec; try discriminate H.
destruct i; try discriminate H.
repeat match type of H with context [match ?o with _ => _ end] => destruct o; try discriminate H end.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hi]. apply andb_prop in H as [Hrd Hrs].
unfold bv_eqb in Hrd, Hrs. apply Z.eqb_eq in Hrd, Hrs, Hi, H4. apply bv_eq in Hrd. apply bv_eq in Hrs. subst.
exists w, imm. auto.
Qed.
Lemma rtt_ok_lw_spec : forall k rd0 rs0 i0, rtt_ok_lw k rd0 rs0 i0 = true ->
  exists w imm, plookup pl_tpi k = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd0 rs0 imm, 4%Z) /\ bv_signed imm = i0.
Proof.
intros k rd0 rs0 i0 H. unfold rtt_ok_lw in H.
destruct (plookup pl_tpi k) as [[w | | | | |] |] eqn:Hpl; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz] |] eqn:Hdec; try discriminate H.
destruct i; try discriminate H.
repeat match type of H with context [match ?o with _ => _ end] => destruct o; try discriminate H end.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hi]. apply andb_prop in H as [Hrd Hrs].
unfold bv_eqb in Hrd, Hrs. apply Z.eqb_eq in Hrd, Hrs, Hi, H4. apply bv_eq in Hrd. apply bv_eq in Hrs. subst.
exists w, imm. auto.
Qed.

Lemma rtt_ld : forall (W : world SEGS) regs mem md Q k (rd0 rs0 : bv 5) (i0 a v : Z),
  rtt_ok_ld k rd0 rs0 i0 = true -> bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
  v_addi (getr regs rs0) i0 = Z_to_bv 64 a -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx (regupd regs rd0 (Z_to_bv 64 v))
               (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rd0 rs0 i0 a v Hok Hrd Hk0 Hk4 Ea Hv HK.
destruct (rtt_ok_ld_spec k rd0 rs0 i0 Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs0) (bv_signed imm)) 8 = Some (YN2e.le_list v 8)).
{ rewrite Ei, Ea. exact (YN2e.rdn_cell SEGS _ a v 8 Hv). }
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_ld SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (YN2e.le_list v 8) (Z_to_bv 64 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hr (YN2e.word_mem_value_mod v)).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

Lemma rtt_lw : forall (W : world SEGS) regs mem md Q k (rd0 rs0 : bv 5) (i0 a v : Z),
  rtt_ok_lw k rd0 rs0 i0 = true -> bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
  v_addi (getr regs rs0) i0 = Z_to_bv 64 a -> val_mem SEGS (mrestrict (w_H W) mem) a 4 v ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_lw (Z_to_bv 64 (v mod 2 ^ 32))))
               (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rd0 rs0 i0 a v Hok Hrd Hk0 Hk4 Ea Hv HK.
destruct (rtt_ok_lw_spec k rd0 rs0 i0 Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs0) (bv_signed imm)) 4 = Some (YN2e.le_list v 4)).
{ rewrite Ei, Ea. exact (YN2e.rdn_cell SEGS _ a v 4 Hv). }
assert (Hb : bytes_le_to_Z (YN2e.le_list v 4) = bv_unsigned (Z_to_bv 64 (v mod 2 ^ 32))).
{ rewrite YN2e.bytes_le_to_Z_le_list. change (8 * Z.of_nat 4) with 32. rewrite unsigned_lit_small; [reflexivity|].
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). lia. }
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_lw SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (YN2e.le_list v 4) (Z_to_bv 64 (v mod 2 ^ 32)) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hr Hb).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

(* a branch `beqz rs, off` / `bnez rs, off` (b<eq|ne> rs, x0, off): the slot's shape AND its offset, closed *)
Definition rtt_ok_beqz (k : Z) (rs0 : bv 5) (off : Z) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Branch BC_EQ rs r0 imm, isz) =>
          bv_eqb rs rs0 && bv_eqb r0 (Z_to_bv 5 0) && (bv_signed imm =? off) && (isz =? 4)
      | _ => false
      end
  | _ => false
  end.
Definition rtt_ok_bnez (k : Z) (rs0 : bv 5) (off : Z) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Branch BC_NE rs r0 imm, isz) =>
          bv_eqb rs rs0 && bv_eqb r0 (Z_to_bv 5 0) && (bv_signed imm =? off) && (isz =? 4)
      | _ => false
      end
  | _ => false
  end.
Lemma rtt_ok_beqz_spec : forall k rs0 off, rtt_ok_beqz k rs0 off = true ->
  exists w imm, plookup pl_tpi k = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs0 (Z_to_bv 5 0) imm, 4%Z) /\ bv_signed imm = off.
Proof.
intros k rs0 off H. unfold rtt_ok_beqz in H.
destruct (plookup pl_tpi k) as [[w | | | | |] |] eqn:Hpl; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz] |] eqn:Hdec; try discriminate H.
destruct i; try discriminate H.
repeat match type of H with context [match ?o with _ => _ end] => destruct o; try discriminate H end.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hi]. apply andb_prop in H as [Hrs Hr0].
unfold bv_eqb in Hrs, Hr0. apply Z.eqb_eq in Hrs, Hr0, Hi, H4. apply bv_eq in Hrs. apply bv_eq in Hr0. subst.
exists w, imm. auto.
Qed.
Lemma rtt_ok_bnez_spec : forall k rs0 off, rtt_ok_bnez k rs0 off = true ->
  exists w imm, plookup pl_tpi k = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs0 (Z_to_bv 5 0) imm, 4%Z) /\ bv_signed imm = off.
Proof.
intros k rs0 off H. unfold rtt_ok_bnez in H.
destruct (plookup pl_tpi k) as [[w | | | | |] |] eqn:Hpl; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz] |] eqn:Hdec; try discriminate H.
destruct i; try discriminate H.
repeat match type of H with context [match ?o with _ => _ end] => destruct o; try discriminate H end.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H Hi]. apply andb_prop in H as [Hrs Hr0].
unfold bv_eqb in Hrs, Hr0. apply Z.eqb_eq in Hrs, Hr0, Hi, H4. apply bv_eq in Hrs. apply bv_eq in Hr0. subst.
exists w, imm. auto.
Qed.

Lemma rtt_beqz_tk : forall (W : world SEGS) regs mem md Q k (rs0 : bv 5) off tgt,
  rtt_ok_beqz k rs0 off = true -> 0 <= k -> k + 4 < 2 ^ 40 ->
  btgt (Z_to_bv 64 (BASE + k)) off = Z_to_bv 64 tgt ->
  c_eq (getr regs rs0) (Z_to_bv 64 0) = true ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rs0 off tgt Hok Hk0 Hk4 Htgt Hc HK.
destruct (rtt_ok_beqz_spec k rs0 off Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hz0 : getr regs (Z_to_bv 5 0) = Z_to_bv 64 0)
  by (replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); apply getr_zero).
rewrite <- Hz0 in Hc.
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_tk SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 (Z_to_bv 5 0) imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Ei, Htgt. apply HK.
Qed.

Lemma rtt_beqz_ft : forall (W : world SEGS) regs mem md Q k (rs0 : bv 5) off,
  rtt_ok_beqz k rs0 off = true -> 0 <= k -> k + 4 < 2 ^ 40 ->
  c_eq (getr regs rs0) (Z_to_bv 64 0) = false ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rs0 off Hok Hk0 Hk4 Hc HK.
destruct (rtt_ok_beqz_spec k rs0 off Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hz0 : getr regs (Z_to_bv 5 0) = Z_to_bv 64 0)
  by (replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); apply getr_zero).
rewrite <- Hz0 in Hc.
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 (Z_to_bv 5 0) imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

Lemma rtt_bnez_tk : forall (W : world SEGS) regs mem md Q k (rs0 : bv 5) off tgt,
  rtt_ok_bnez k rs0 off = true -> 0 <= k -> k + 4 < 2 ^ 40 ->
  btgt (Z_to_bv 64 (BASE + k)) off = Z_to_bv 64 tgt ->
  c_eq (getr regs rs0) (Z_to_bv 64 0) = false ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rs0 off tgt Hok Hk0 Hk4 Htgt Hc HK.
destruct (rtt_ok_bnez_spec k rs0 off Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hz0 : getr regs (Z_to_bv 5 0) = Z_to_bv 64 0)
  by (replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); apply getr_zero).
rewrite <- Hz0 in Hc.
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_bne_tk SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 (Z_to_bv 5 0) imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Ei, Htgt. apply HK.
Qed.

Lemma rtt_bnez_ft : forall (W : world SEGS) regs mem md Q k (rs0 : bv 5) off,
  rtt_ok_bnez k rs0 off = true -> 0 <= k -> k + 4 < 2 ^ 40 ->
  c_eq (getr regs rs0) (Z_to_bv 64 0) = true ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k rs0 off Hok Hk0 Hk4 Hc HK.
destruct (rtt_ok_bnez_spec k rs0 off Hok) as (w & imm & Hpl & Hdec & Ei).
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hz0 : getr regs (Z_to_bv 5 0) = Z_to_bv 64 0)
  by (replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); apply getr_zero).
rewrite <- Hz0 in Hc.
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_bne_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 (Z_to_bv 5 0) imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
End s.
