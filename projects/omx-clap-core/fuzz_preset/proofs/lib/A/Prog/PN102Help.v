(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the SUPPORT LEMMAS of the walk of parse_noting
   (row N10-PNA; cut table lib/A/Prog/PN102Cuts.v). No function is proved here: the concrete step rules over the
   whole-program listing at PL_prog_A / PI_prog_A (addi, jal, the conditional branch, ld, the return), the call rules
   of a callee TEXT over YCbqG's journal at a caller budget (the batch kit's wild budget: plain, float, the budgeted float and the
   budgeted caller-window form at window 0), the pc of the body, and the keep of parse_noting's saved words across a
   callee.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk 13970867e0c9, its one
   announced re-bind). This file: support lemmas of that walk only.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   TAKEN BY PATH (image-free; each restated under a pn_ name):
   - pn_step_addi / pn_step_call / pn_pc4: lib/A/Prog/Ent102L6AfLem.v l6f_step_addi / l6f_step_call / l6f_pc4
     (a working branch b1bc025047ea), at the listing instance PL_prog_A in place of PL_102_A;
   - pn_step_branch: lib/A/Prog/Ent102CallA.v ec_step_branch (same branch), at PL_prog_A;
   - pn_call / pn_callF: lib/A/Prog/Ent102L2AHelp.v l2_call / l2_callF (same branch), at a caller budget WS0 through
     YCbqGwild.afn_pre_x_at_w and YCbqG.ajournal_xw_sub; pn_callFb: the same with YCbqGwild.v aj_call_xbF's budget;
   - pn_step_ret: lib/Reusable/YA0o.v SRr_ret_raw's proof at the listing's ret slot.
   NUMERALS: 4 (an instruction), 8 (a word), 48 (the frame), 8 .. 40 (the save slots), 2 ^ 40 / 2 ^ 64 (the engine's
   code-span and word ranges). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Tactics: register disequality, the listing slot at an offset and its decoding (Ent102L6AfLem.v's, at
      PL_prog_A). *)
Ltac pn_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E;
  lazymatch type of E with ?p = ?q =>
    let vp := eval vm_compute in p in let vq := eval vm_compute in q in
    replace p with vp in E by (vm_compute; reflexivity); replace q with vq in E by (vm_compute; reflexivity) end;
  discriminate E.
Ltac pn_fd k Hpl Hd :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch r with
  | Some (PW ?w) =>
    assert (Hpl : plookup (@pl_tpi _ PL_prog_A) k = Some (PW w)) by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "pn_fd: no plain word at offset" k
  end.
Ltac pn_fdc k Hpl :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch r with
  | Some (PCall ?s ?rd) =>
    assert (Hpl : plookup (@pl_tpi _ PL_prog_A) k = Some (PCall s rd)) by (vm_compute; reflexivity)
  | _ => fail "pn_fdc: no call slot at offset" k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. The concrete steps at the A' instance. *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).

(* parse_noting's entry is the listing's base plus PN_SLOT0 *)
Lemma pn_sigma : SIGMA AS_parse_noting = BASE + PN_SLOT0.
Proof. vm_compute. reflexivity. Qed.
Lemma pn_slot0_range : 0 <= PN_SLOT0 /\ PN_SLOT0 + PN_RET < 2 ^ 40.
Proof. split; vm_compute; congruence. Qed.
Lemma pn_cfg_eq : forall (fy : YK11.FPState) off regs mem md,
  pn_cfg (PA := PA) fy off regs mem md =
  mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + (PN_SLOT0 + off))) mem (YK11.seg_rom SEGS)) md.
Proof. intros fy off regs mem md. unfold pn_cfg, cfg_at, w64. rewrite pn_sigma. f_equal. f_equal. f_equal. lia. Qed.

Lemma pn_pc4 : forall k, 0 <= k < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof.
intros k Hk. pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma pn_step_addi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_prog_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' v Hk Hpl Hd Hrd Erd Hv HK. subst rd'.
pose proof (pa_fetch_pw (PL := PL_prog_A) (PI := PA) k w Hpl) as Hf.
eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_addi_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (pn_pc4 k Hk). apply HK.
Qed.

Lemma pn_step_call : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) (s : asym) (rd rd' : bv 5),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_prog_A) k = Some (PCall s rd) -> rd = rd' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 (BASE + (k + 4))))
     (Z_to_bv 64 (SIGMA s)) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k s rd rd' Hk Hpl Erd HK. subst rd'.
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- (@pl_tpi_eq _ PL_prog_A) in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA A_prog_listing pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with decode_any _ = Some (Jal ?r ?im, _) => rename r into rdj; rename im into immj end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd Hnz].
apply reg_eqb_eq in Hrd. subst rdj. apply Z.eqb_eq in Ht.
assert (Hrd0 : bv_eqb rd (0%bv : bv 5) = false).
{ destruct (bv_eqb rd (Z_to_bv 5 0)) eqn:E3; [discriminate Hnz|]. rewrite <- E3. unfold bv_eqb. reflexivity. }
pose proof (pa_fetch_ok (PI := PA) _ _ Hl) as Hf.
eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_jal_link (fx := fx) SEGS regs (Z_to_bv 64 (VAL A_TEXT + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 wz) rd immj Hf (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd0. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (pn_pc4 k Hk).
  replace (btgt (Z_to_bv 64 (VAL A_TEXT + k)) (bv_signed immj)) with (Z_to_bv 64 (SIGMA s)).
  + apply HK.
  + unfold btgt, v_addi. rewrite unsigned_lit_small by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    rewrite <- Ht. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma pn_step_branch : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w tgt : Z) (c : branch_cond) (rs1 rs2 : bv 5) (imm : bv 13),
  0 <= k < 2 ^ 40 -> 0 <= tgt < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_prog_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  k + bv_signed imm = tgt ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall X,
     SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + tgt)) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall X,
     SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w tgt c rs1 rs2 imm Hk Ht Hpl Hd Etg HT HF.
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
pose proof (pa_fetch_pw (PL := PL_prog_A) (PI := PA) k w Hpl) as Hf.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hc.
- eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_tk_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (BASE + tgt)).
    * apply HT. reflexivity.
    * unfold btgt, v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
- eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_ft_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    rewrite (pn_pc4 k Hk). apply HF. reflexivity.
Qed.

(* the `ret` slot: the pc becomes ra, and the post holds of that configuration *)
Lemma pn_step_ret : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z),
  plookup (@pl_tpi _ PL_prog_A) k = Some (PW RET_WORD_r) ->
  (forall X, Q W (mkCfg (@YK11.mkst fx regs (v_jalr (getr regs 1) 0) mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md))) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k Hpl HQ.
pose proof (pa_fetch_pw (PL := PL_prog_A) (PI := PA) k RET_WORD_r Hpl) as Hf.
eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)). change 0 with (bv_signed (0%bv : bv 12)).
  eapply (step_jalr_x0 (fx := fx) SEGS _ _ _ _ (Z_to_bv 32 RET_WORD_r) 1 (0%bv : bv 12)).
  + exact Hf.
  + reflexivity.
  + exact decode_ret_r.
  + reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply SRr_ret. apply HQ.
Qed.

(* the reader's eight bytes, in the representation a load reads (Ent102L6AEnt.v l6_rd64_val) *)
Lemma pn_rd64_val : forall (H : word -> bool) (m : word -> option byte) a v,
  rd64 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 8 v.
Proof.
intros H m a v Hr k Hk.
specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb;
cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hr. f_equal.
transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. exact Hr.
Qed.
End S.

(* ---------------------------------------------------------------------- *)
(* 3. THE CALL RULES (Ent102L2AHelp.v l2_call / l2_callF, at a caller budget WS0 - the batch kit's wild budget, YCbqG.v
      ajournal_xw): a callee's TEXT applied at its entry, from a caller state its journal describes. pn_call /
      pn_callF: a callee with no wild site (its post at the empty budget), the caller's journal after the call at WS0
      (YCbqG.v ajournal_xw_sub with WS1 = []). pn_callFb: a BUDGETED float callee (YCbqGwild.v apost_base_xbF P), the
      caller's journal after the call at WS0 ++ WS1 for the callee's WS1 with P WS1 (YCbqGwild.v aj_call_xbF's shape).
      The caller-window post at window 0 is the float post (pn_fpostWF0b).
      OVER A WORLD RELATION Rw (the free / realloc move: a run that crosses a free ends at YA0nH.wle' segs RZ_cf, not
      at wle). Both rules are used only after pj_parse's free or across it, so each is restated in place over Rw:
      pn_call takes the caller's journal at Rw (ajournal_xwR, Rw containing wle and transitive) and a plain callee
      (its text an SRr over the empty-budget post), so it is the rule for a call AFTER a free; pn_callFb takes the
      caller's journal and a budgeted float callee's text both over Rw (SRrG Rw, apost_base_xbFR Rw), as pj_parse at
      Rw := wle' segs RZ_cf, and its run is SRrG Rw. Both compose by YCbqG.v ajournal_xw_subR. *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma pn_call : forall (Rw : world segs -> world segs -> Prop),
  (forall W1 W2, wle W1 W2 -> Rw W1 W2) -> (forall W1 W2 W3, Rw W1 W2 -> Rw W2 W3 -> Rw W1 W3) ->
  forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k WS0
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xwR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (apost_base_x (SK := SK) segs B PST ARx STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, wle W W2 ->
     ajournal_xwR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
       WS0 ->
     ajournal_x (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRr segs W (cfg_at segs f regs mem md) R.
Proof.
intros Rw Hsub Htr W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k WS0 STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply SRr_bind.
{ apply Hcallee.
  exact (YCbqGwild.afn_pre_x_at_wR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md
    k WS0 regs STK1 o ch HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle); [|exact HJ1 | exact HP | exact HQ].
assert (HJ1w : ajournal_xwR (SK := SK) segs B PST ARx (@wle segs) STK1 (sp0 + o) FP1 ly S Hp W mem md []
  ly2 S2 Hp2 W2 mem2 md2 k1 []) by exact HJ1.
rewrite <- (app_nil_r WS0). change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low Rw Htr);
  [exact HJ | exact (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) Rw Hsub
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1w) | lia | lia | exact HF].
Qed.

Lemma pn_callF : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k WS0
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (apost_base_xF (SK := SK) segs B PST ARx STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, wle W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
     ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 ->
     ajournal_x (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRr segs W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRr segs W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k WS0 STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply SRr_bind.
{ apply Hcallee.
  exact (YCbqGwild.afn_pre_x_at_w (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k
    WS0 regs STK1 o ch HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK); [|exact HJ1 | exact HP | exact HQ].
rewrite <- (app_nil_r WS0). change own with ([] ++ own).
eapply (ajournal_xw_sub segs B PST ARx LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* the budgeted float callee (pj_parse): its post at a budget WS1 it chooses, with P WS1; the caller's journal, the
   callee's text and the run at Rw *)
Lemma pn_callFb : forall (Rw : world segs -> world segs -> Prop),
  (forall W1 W2 W3, Rw W1 W2 -> Rw W2 W3 -> Rw W1 W3) ->
  forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  WS0 STK1 FP1 (o : Z) ch (f : Z) (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xwR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRrG segs Rw W (cfg_at segs f regs mem md)
       (YCbqGwild.apost_base_xbFR (fx := fx) (SK := SK) segs B PST ARx Rw P STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1, Rw W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> P WS1 ->
     ajournal_xwR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
       (WS0 ++ WS1) ->
     ajournal_xwR (SK := SK) segs B PST ARx Rw STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs Rw W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs Rw W (cfg_at segs f regs mem md) R.
Proof.
intros Rw Htr W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k WS0 STK1 FP1 o ch f P Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs Rw Htr).
{ apply Hcallee.
  exact (YCbqGwild.afn_pre_x_at_wR (SK := SK) segs B PST ARx Rw STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md
    k WS0 regs STK1 o ch HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS1 Hle HFZ HFK HPW); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low Rw Htr); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* a callee footprint that is empty, or that is the caller's own *)
Lemma pn_fp_sub_nil : forall STK sp0 FP ly S own lyc Sc, fp_sub_x B STK sp0 FP [] ly S own lyc Sc.
Proof. intros STK sp0 FP ly S own lyc Sc a (r & Hr & _). destruct Hr. Qed.
Lemma pn_fp_sub_same : forall STK sp0 FP ly S own lyc Sc, fp_sub_x B STK sp0 FP FP ly S own lyc Sc.
Proof. intros STK sp0 FP ly S own lyc Sc a Ha. left. exact Ha. Qed.
End C.

(* the budgeted caller-window post (PRH_Base.v fpostWFb) at window 0 is the budgeted float post (YCbqGwild.v
   apost_base_xbFR). fpostWFb is an AFTER-FREE-ONLY family (PRH_Base.v, the R FAMILIES: its journal at wle' segs
   RZ_cf), so this is restated in place at the same relation; its one user is pj_parse's call (PN102S2.v) *)
Section WF. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L} {SK : YI16.sink_head}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Lemma pn_fpostWF0b : forall P STK FP regs ly S Hp (W : world pa_segs) mem md Q W' c',
  fpostWFb B ARx SK P STK 0 FP regs ly S Hp W mem md Q W' c' ->
  YCbqGwild.apost_base_xbFR (fx := fx) (SK := SK) pa_segs B prh_pst ARx (wle' pa_segs YGcfRehidePost.RZ_cf)
    P STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros P STK FP regs ly S Hp W mem md Q W' c'
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hz & Hk & HP & HJ & _ & Hpr & HQ).
rewrite !Z.add_0_r in HJ.
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HP|]. split; [exact HJ|].
split; [exact Hpr | exact HQ].
Qed.
End WF.

(* ---------------------------------------------------------------------- *)
(* 4. parse_noting's saved words across a callee: the callee's journal (any budget) runs at sp0 - 48 and below, so
      the five words at sp0 - 8 .. sp0 - 40 (above the callee's window, above the ceiling) are kept. *)
Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Lemma pn_above_kept : forall STK1 sp1 FP1 ly S Hp (W : world segs) mem md ly2 S2 Hp2 (W2 : world segs) mem2 md2 k1 WS1 a,
  ajournal_xw (SK := SK) segs B PST ARx STK1 sp1 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  YM05.alloc_ceiling <= a < 2 ^ 64 -> sp1 <= a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a.
Proof.
intros STK1 sp1 FP1 ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 k1 WS1 a HJ Ha Hs.
apply (ajx_hi HJ); lia.
Qed.
Lemma pn_rd64_kept : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rd64 rd a v -> rd64 rd' a v.
Proof. intros rd rd' a v Hk H k Hk8. rewrite Hk by lia. exact (H k Hk8). Qed.
End K.
