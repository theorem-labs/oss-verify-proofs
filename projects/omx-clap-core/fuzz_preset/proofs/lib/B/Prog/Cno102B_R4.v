(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1165 of its 1242 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_E2.v, with its module paths and module names changed; 856 of its 961 lines of code are new or changed and 1137 lines of the source are left out. *)
(* rule 24: no function proved *)
(* rule 24: proves no function (kind: segment lemma) *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): segments CB4 / CB5 / CB6 (Read1-3, the GUARD
   parts) of the re-walk of check_no_overread (cno, entry 0x819f0) against the kit's text tcheck_no_overread_specX. Sub-lane
   CnoB102rR.CutR4 of lane CnoB102r (a Theorem Labs lane, the internal file PLAN-cno-caw-102.md 5.2 rows CB4-CB6). The port of image A''s
   Cno102A_R6.v (CA6-CA8, a working branch 41dfdb047827) to B'. Each segment ends at the parse_noting
   call state (cnb_ex_pn1 / pn2 / pn3, the `jal parse_noting`, which the PN steps take) or at the next cut.
   INPUTS (by path): the contract lib/B/Prog/Cno102B_Base.v (a working branch 75415fdb6e76, blob
   20c89a1d4da2: the kit CUT a working branch 7cdbb61b5fa0; cnb_pre CTX0 D without DW, cnb_base .. k wk over
   the budgeted journal cnb_J D wk and their forms cnb_baseR / cnb_JR at a world relation R (cnb_baseR_mono between two
   relations), each cut X beside its form XR at R (cnb_at_read2R .. cnb_at_freeR, cnb_ex_read3R .. cnb_ex_freeR),
   cnb_cdead D, cnb_fo D W mem Lam o d st, the hull stage suffixes cnb_hrest_* and their split equations); the
   step kit lib/B/Prog/Cno102B_Ro.v (CutRo: cnb_hs_*,
   cnb_ro_call, cnb_base_mat, cnb_base_mono, cnb_J_rebase, cnb_J_fixed and their R forms cnb_hs_*R, cnb_ro_callR,
   cnb_base_matR, cnb_base_monoR, cnb_J_rebaseR, cnb_J_fixedR; cnb_fo_keep, cnb_entry_facts, cnb_rcslot_agree,
   cnb_prog_eq); listing
   lib/B/Listing_prog.v through the Base's PL_cno_B / B_prog_tpi_cno; the cut's PRH_FnAlloc.v 4d8aeba047e5
   (tfuzz_alloc_ran_out_specX, the Section hypothesis HRO, the kit's form), PRH_FnCheck.v c40cf3fdcd2a (ck_cno_ranout),
   PRH_Base.v ef7c8ca98529 (prh_ledger and its named projections), PRH_PjOrder.v e5917626b82b (the order list cnb_fo
   reads), YCbqG.v 219748197d6b (ajournal_xw read by its ajx_* projections, ajournal_xwR by its ajxR_* projections;
   ajournal_x_exec / ajournal_x_execR); YA0nH.v / YSRrG.v (SRrG, wle' and SRr', SRr'_bind / SRr'_ret), YC80x.v
   (SRr_step_invR); lib/Spec/PresetHullBudget.v (hull_budget, hull_budget_app, hull_used_refl).
   Re-fit of the f97c file (b3de1968a565 / 2700059a3579) to the cut: the cuts' spent wild budget is 0 at read1 / pn1, 2
   at read2 / pn2, 4 at read3 / pn3, 6 at cmp / free; these segments call only the FIXED-trace fuzz_alloc_ran_out, so the
   budget is kept along each stretch and raised by the kit's cnb_base_mono (CB4, r4_mono) / cnb_base_monoR (CB5 / CB6,
   r4_monoR) where a reading is skipped (read1 -> free 0 -> 6, read2 -> read3 2 -> 4, read3 -> cmp 4 -> 6). The rc-slot
   stores keep the journal at wle' SEGS RZ_cf by the kit's FIXED recipe (cnb_J_rebaseR / ajournal_x_execR /
   cnb_J_fixedR, r4_base_store). cnb_fo crosses the stores by r4_fo_low (the kit's cnb_fo_keep: the stores write the
   real stack, above the trees' footprint) and the ran-out call by the kit's cnb_ro_call (CB4) / cnb_ro_callR at wle'
   SEGS RZ_cf (CB5 / CB6); a skipped reading's struct is None (cnb_fo trivial). The CB4 free exit carries read1's
   own0 <> 0 -> cnb_cdead D into free's ownl <> 0 arm.
   THE FREE / REALLOC MOVE: a parse_noting call can free or realloc a live block and so hide shadow again; the kit's
   tparse_noting_specX concludes SRr' SEGS RZ_cf with its post at wle' SEGS RZ_cf. So the cuts after the first reading
   are taken at their R forms at wle' SEGS RZ_cf (cnb_at_read2R / read3R / cmpR / freeR / pn2R / pn3R, base cnb_baseR),
   and a segment that starts at one concludes SRr' SEGS RZ_cf: cnb_read2_seg / cnb_read3_seg, whose hand steps are the
   kit's R forms at wle' (cnb_hs_*R, r4_hs_sd, r4_sd_cut) and whose binds / exits are SRr'_bind / SRr'_ret.
   cnb_read1_seg runs before any reading (cnb_at_read1 / pn1 at wle): it concludes SRr; its free exit is CNB_FREE's
   cut at wle' SEGS RZ_cf (cnb_ex_freeR), the base lifted by the Base's cnb_baseR_mono (wle_wle').
   THE HULL: each cut carries the last conjunct `PresetHullBudget.hull_budget S (cnb_hrest_<stage> (bi_x D))` (copies
   at read1 / pn1, rd1 at read2 / pn2, rd2 at read3 / pn3, rd0 at cmp / free). No allocator call runs here and
   fuzz_alloc_ran_out keeps S, so the conjunct rides to a parse_noting call state at its stage; a skipped reading pays
   nothing, so a skip arm drops that reading's events (r4_hull_rd1 / r4_hull_rd2 / r4_hull_rd0: hull_budget_app with
   nothing used, over the Base's split equations; read1 -> free drops all three).
   THE CODE (DERIVED offsets inside cno, Listing_prog.v slot = 201 + off / 4; the B' disassembly of check_no_overread):
     CB4  592 auipc s8 (PHi 24 9) | 596 lbu a0 (PLdHi, B_OBJ 13) | 600 bnez a0 -> 736 | 604 jal fuzz_alloc_ran_out |
          608 beqz a0 -> 620 | 612 li a0, -1 | 616 j -> 636 | 620 mv a0, s9 | 624 mv a1, s7 | 628 mv a2, s6 |
          632 jal parse_noting (CNB_PN1) ; 736 li s8, 1 | (740 = CNB_FREE)
     CB5  636 lbu a1, 0x140(s8) | 640 bnez a1 -> 736 | 644 sd a0, 8(s1) | 648 jal fuzz_alloc_ran_out | 652 beqz a0 -> 664 |
          656 li a0, -1 | 660 j -> 680 (CNB_READ3) | 664 ld a0, 24(s1) | 668 mv a1, s7 | 672 mv a2, s5 | 676 (CNB_PN2)
     CB6  680 lbu a1, 0x140(s8) | 684 bnez a1 -> 736 | 688 sd a0, 0(s1) | 692 jal fuzz_alloc_ran_out | 696 beqz a0 -> 708 |
          700 li s7, -1 | 704 j -> 728 (CNB_CMP) | 708 ld a0, 16(s1) | 712 mv a1, s7 | 716 mv a2, s4 | 720 (CNB_PN3)
   REFUTED (never walked): the CB4 ran-out arm 612 (r4_ran0_ceq: a0 = g_ran_out = bi_ran D = 0); the CB5 / CB6 byte
   branches 640 / 684 -> 736 (r4_mid_own + r4_own_byte + r4_byte0_ceq: the cut's cnb_mid own = 0). No abort edge and no ASan report
   site lies in these stretches.
   LOCAL STEPS (only CB4-CB6 use them): r4_hs_hi (PHi), r4_hs_ldhi (PLdHi) at SRr (CB4); r4_hs_sd (the rc-slot store,
   with the generic invariant P across it by YC80x.v SRr_step_invR at wle' SEGS RZ_cf) and r4_sd_cut (every cut fact
   across that store: the journal at wle' by r4_base_store, cnb_mid and cnb_fo below the allocation ceiling by
   r4_mid_low / r4_fo_low, the saved words and slots above s1 + 16), both at SRr' SEGS RZ_cf (CB5 / CB6).
   Numerals: offsets as above (DERIVED); 8 / 16 / 24 / 48 / 320 / 56 / 152 / 160 / 192 / 512 (LENGTH: slot, frame, struct
   and hi/lo offsets); 4096 (LENGTH: a margin above the ceiling); register numbers (WORD); 2 ^ 64 / 2 ^ 47 / 2 ^ 28 (word
   and code ranges). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally; the shadow-address bounds here
   (r4_shadow_low / r4_ra_low / r4_hull_low) need it on: without it lia fails at r4_ra_low (build 18:02Z) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section r4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the world relation of a cut after a free: the R forms of cnb_at_read2 / read3 / cmp / free / pn2 / pn3 are taken
   at it *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cnb_img B.
Hypothesis HRO : forall fz : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fz rc cp prh_img_B RL B_prog_listing PA B ARx SK.
#[local] Notation STK := STK_check_no_overread.

(* one hand step that changes memory, at wle' SEGS RZ_cf (CB5 / CB6 run after parse_noting): the srr_inv_laws
   invariant P crosses it (YC80x.v SRr_step_invR) *)
Lemma r4_step_mem : forall P, srr_inv_laws SEGS P -> forall (W : world SEGS) fxk regs mem md m' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off'))) m' (YK11.seg_rom SEGS)) ->
  P mem ->
  (forall X, P (munrestrict (w_H W) mem m') ->
     SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off') regs (munrestrict (w_H W) mem m')
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW W fxk regs mem md m' off off' Q Ho Ho' Hst HPm HK.
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRr_step_invR SEGS pa_wx P PLAW WLE' W);
  [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst | exact HPm |].
intros md' Hs HP'. rewrite (same_but_materialized_wvb md md' Hs).
specialize (HK (m_vm_materialized md') HP'). unfold cnb_cfg, cnb_pc, w64 in HK.
replace (BASE + CNB_OFF + off') with (BASE + (CNB_OFF + off')) in HK by lia. exact HK.
Qed.

(* the bytes of a store: wbytes at the j-th written address (YK0e.v wbytes_nth, which this unit does not build) *)
Lemma r4_wbytes_nth : forall bs m (a : word) j,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a j Hnw Hj; [cbn in Hj; lia|].
cbn [length] in Hnw, Hj. cbn [wbytes].
destruct j as [|j'].
- cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  destruct rest as [|b' rest'].
  + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
  + cbn [length] in Hnw.
    rewrite wbytes_below; [rewrite bv_eqb_refl; reflexivity | | ];
    rewrite (u_add1 a) by lia; cbn [length]; lia.
- cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1) + Z.of_nat j') by lia.
  apply IH; [rewrite Hu1; lia | lia].
Qed.
(* a word read back (YCem.v rdword_of_val_mem, which this unit does not build) *)
Lemma r4_rdword_of_val_mem : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (HB8 : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (HB8 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (HB8 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (HB8 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (HB8 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (HB8 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (HB8 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (HB8 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (HB8 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma r4_nth_le8 : forall V k, 0 <= V < 2 ^ 64 -> (k < 8)%nat ->
  nth k (Z_to_le_bytes 8 V) (Z_to_bv 8 0) = Z_to_bv 8 (YO0f.le_byte V 8 k).
Proof.
intros V k HV Hk. rewrite le_byte_small by (cbn; lia).
do 8 (destruct k as [|k]; [cbn [nth Z_to_le_bytes]; rewrite ?Z.shiftr_shiftr by lia; reflexivity|]). lia.
Qed.
(* the decode check of `sd rs2, i(rs1)` (the kit's cnb_dec) *)
Definition r4_is_sd (off : Z) (rs1 rs2 : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Store SZ8 rs1' rs2' imm, sz) => (sz =? 4) && bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? i)
  | _ => false end.

Lemma r4_hs_sd : forall P, srr_inv_laws SEGS P ->
  forall (W : world SEGS) fxk regs mem md Q off off' rs1 rs2 i a,
  r4_is_sd off rs1 rs2 i = true -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs1) + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> apresent (w_H W) mem (a + j)) -> P mem ->
  (forall X mem',
     (forall x : word, ~ (a <= bv_unsigned x < a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     rdword (aview SEGS (w_H W) mem') a = Some (bv_unsigned (getr regs rs2)) -> P mem' ->
     SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off') regs mem'
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW W fxk regs mem md Q off off' rs1 rs2 i a H. unfold r4_is_sd, cnb_dec in H.
destruct (plookup B_prog_tpi_cno (CNB_OFF + off)) as [e|] eqn:Hpl; [|discriminate H].
destruct e as [w| | | | |]; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[ii sz]|] eqn:Hdec; [|discriminate H].
destruct ii; try discriminate H. destruct sz0; try discriminate H.
apply andb_prop in H as (H & Hi). apply andb_prop in H as (H & H2). apply andb_prop in H as (Hsz & H1).
apply Z.eqb_eq in Hsz, Hi. apply reg_eqb_eq in H1, H2. subst sz rs0 rs3 i.
intros Ho -> Ha Ha0 Ha8 Hpr HPm HK.
assert (Ea : v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
assert (Hua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
assert (Hok : store_ok SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs1) (bv_signed imm)) 8 = true).
{ rewrite Ea. apply store_ok_of_all; [rewrite Hua; lia|]. intros x Hx. rewrite Hua in Hx.
  pose proof (apresent_writable SEGS (w_H W) mem (bv_unsigned x)) as Hw.
  unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. apply Hw.
  replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply Hpr. lia. }
pose proof (@step_sd_val fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs1 rs2 imm
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hok) as Hst.
rewrite Ea, (cnb_pc4 off ltac:(lia)) in Hst.

apply (r4_step_mem P PLAW W fxk regs mem md _ off (off + 4) Q ltac:(lia) ltac:(lia) Hst HPm).
intros X HP'.
set (bs := word_to_le_bytes 8 (getr regs rs2)).
assert (Hlen : length bs = 8%nat) by reflexivity.
set (mem' := munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs)).
assert (Eout : forall x : word, ~ (a <= bv_unsigned x < a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x).
{ intros x Hx. unfold mem', munrestrict, mrestrict. destruct (w_H W x) eqn:Ex; [reflexivity|].
  pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [Hlt|Hge].
  - rewrite wbytes_below by (rewrite ?Hlen, ?Hua; cbn; lia). unfold mrestrict. rewrite Ex. reflexivity.
  - rewrite wbytes_above by (rewrite Hlen, Hua; cbn; lia). unfold mrestrict. rewrite Ex. reflexivity. }
assert (Ein : forall j, (j < 8)%nat ->
  mrestrict (w_H W) mem' (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))).
{ intros j Hj. destruct (Hpr (Z.of_nat j) ltac:(lia)) as (Hh & _).
  unfold mem', munrestrict, mrestrict. rewrite Hh.
  replace (Z_to_bv 64 (a + Z.of_nat j)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + Z.of_nat j)) by (rewrite Hua; reflexivity).
  apply r4_wbytes_nth; [rewrite Hlen, Hua; cbn; lia | rewrite Hlen; exact Hj]. }
refine (HK X mem' Eout _ _ _ HP').
- intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) a) as [Hlt|Hge];
    [rewrite (Eout x ltac:(lia)); exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (a + 8)) as [Hlt2|Hge2]; [|rewrite (Eout x ltac:(lia)); exact Hx].
  assert (Ex : x = Z_to_bv 64 (a + Z.of_nat (Z.to_nat (bv_unsigned x - a)))).
  { rewrite Z2Nat.id by lia. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Ex, (Ein (Z.to_nat (bv_unsigned x - a)) ltac:(lia)). discriminate.
- intros x Hx. unfold mem', munrestrict. rewrite Hx. reflexivity.
- apply r4_rdword_of_val_mem; [|apply bv_unsigned_in_range].
  intros k Hk. unfold mbyte. rewrite (Ein k Hk). f_equal. unfold bs, word_to_le_bytes.
  apply r4_nth_le8; [apply bv_unsigned_in_range | exact Hk].
Qed.

(* `auipc rd, ..` at a PHi slot: rd = the image's hi atom j (the listing's certificate, pi_slot_check's PHi clause) *)
Lemma r4_hs_hi : forall (W : world SEGS) fxk regs mem md Q off off' rd j,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PHi rd j) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (w64 (VAL (A_HI j)))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd j Hpl Hrd Ho -> HK.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert (CNB_OFF + off) (PHi rd j) Hpl)
  as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CNB_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hrd' & Hv). apply reg_eqb_eq in Hrd'. subst rd0. apply Z.eqb_eq in Hv.
apply (cnb_step W fxk regs mem md (regupd regs rd (w64 (VAL (A_HI j)))) off (off + 4) Q ltac:(lia) ltac:(lia));
  [|exact HK].
rewrite (@step_auipc fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd imm (pa_fetch_ok _ _ Hf)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cnb_pc4 off ltac:(lia)). do 3 f_equal.
rewrite <- b_auipc, YP0k.sext64_lit, lit_add, <- lit_canon. unfold auipc_val in Hv. rewrite Hv. reflexivity.
Qed.
(* `lbu rd, lo(rs)` at a PLdHi slot, rs = the hi atom j: the byte at the image object a0 + o *)
Lemma r4_hs_ldhi : forall (W : world SEGS) fxk regs mem md Q off off' rd rs j a0 o b,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PLdHi rd rs j a0 o SZ1 false) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  getr regs rs = w64 (VAL (A_HI j)) ->
  mbyte SEGS (mrestrict (w_H W) mem) (VAL a0 + o) = Some b ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd rs j a0 o b Hpl Hrd Ho -> Hs Hb HK.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert (CNB_OFF + off)
  (PLdHi rd rs j a0 o SZ1 false) Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CNB_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hv). apply andb_prop in Hck as (Hck & Hsg). apply andb_prop in Hck as (Hck & Hszq).
apply andb_prop in Hck as (Hrd' & Hrs'). apply reg_eqb_eq in Hrd'. apply reg_eqb_eq in Hrs'.
apply msize_eqb_eq in Hszq. subst rd0 rs1 sz.
destruct signed; [discriminate Hsg|]. apply Z.eqb_eq in Hv.
apply (cnb_step W fxk regs mem md (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) off (off + 4) Q ltac:(lia) ltac:(lia));
  [|exact HK].
assert (Ea : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 (VAL a0 + o)).
{ rewrite Hs. unfold v_addi, w64. rewrite unsigned_lit_small by (apply pa_val_range). f_equal. lia. }
rewrite (@step_lbu fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm b (pa_fetch_ok _ _ Hf)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
- rewrite Hrd, (cnb_pc4 off ltac:(lia)). reflexivity.
- rewrite Ea. exact (ro_rdn1 SEGS _ _ b Hb).
Qed.

(* ---- THE CUT FACTS ACROSS A REAL-STACK STORE: every fact of cnb_mid reads bytes below the allocation ceiling
   (blocks, the fake frame and its shadow, the program statics, the input), the store writes the real stack above
   it (cnb_entry_facts: alloc_ceiling <= the stack's low end) ---- *)
Lemma r4_pst_low : forall x, Exists (in_zr x) prh_pst -> 0 <= x < kLowMemEnd.
Proof. intros x H. exact (pa_segs_low x (proj1 (cnbi_pst_ok B IMG x H))). Qed.
Lemma r4_vm_pst : forall m m' c n v, In (c, Z.of_nat n) prh_pst -> val_mem SEGS m c n v ->
  (forall x, 0 <= x < kLowMemEnd -> mbyte SEGS m' x = mbyte SEGS m x) -> val_mem SEGS m' c n v.
Proof.
intros m m' c n v Hin Hv K. apply (pj_valR_frame SEGS m m' c n v Hv). intros x Hx. apply K. apply r4_pst_low.
apply Exists_exists. exists (c, Z.of_nat n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma r4_shadow_low : forall x, 0 <= x <= YM05.alloc_ceiling ->
  0 <= shadow_addr x / 8 * 8 /\ shadow_addr x + 8 < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _). pose proof (ro_div8 (shadow_addr x)) as H2.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as H0. pose proof (Z.mul_div_le x 8 ltac:(lia)) as H1.
unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.
Lemma r4_ra_low : forall (rd rd' : reader) x n, 0 <= x -> x + n <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 4096 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n H0 H1 K H. apply (range_addressable_agree rd rd' SHADOW_OFF x n); [|exact H].
intros y Hy. apply K. pose proof (r4_shadow_low y ltac:(lia)) as (S0 & S1). unfold shadow_addr in S0, S1.
unfold shadow_of_addr. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma r4_hull_low : forall (rd rd' : reader) x n, 0 <= x -> 0 < n -> x + n <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 4096 -> rd' a = rd a) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n H0 Hn H1 K H s Hs. rewrite K; [exact (H s Hs)|].
pose proof (r4_shadow_low x ltac:(lia)) as (S0 & _). pose proof (r4_shadow_low (x + n - 1) ltac:(lia)) as (_ & S1).
pose proof (ro_div8 (shadow_addr (x + n - 1))). lia.
Qed.

Lemma r4_mid_low : forall D ly S Hp (W : world SEGS) mem mem' md Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3,
  ARx ly S Hp W mem md ->
  4096 <= bi_data D -> bi_data D + cnb_size D <= YM05.alloc_ceiling ->
  0 <= cnb_F D -> cnb_F D + 512 <= YM05.alloc_ceiling ->
  (forall x, 0 <= x < YM05.alloc_ceiling + 4096 ->
     mrestrict (w_H W) mem' (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)) ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  cnb_mid B D ly S Hp W mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3.
Proof.
intros D ly S Hp W mem mem' md Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HAR Hd0 Hd1 HF0 HF1 KL HM.
pose proof asan_consts as (C1 & _ & _ & _ & C5). pose proof (@cf_head_nonneg cp) as Hh0.
assert (KR : forall x, 0 <= x < YM05.alloc_ceiling + 4096 -> mbyte SEGS (rdW W mem') x = mbyte SEGS (rdW W mem) x)
  by (intros x Hx; unfold mbyte; rewrite (KL x Hx); reflexivity).
assert (KA : forall x, 0 <= x < YM05.alloc_ceiling + 4096 -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x)
  by (intros x Hx; unfold aview; rewrite (KR x Hx); reflexivity).
assert (KW : forall x, 0 <= x < YM05.alloc_ceiling + 4096 ->
  writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W mem') x)
  by (intros x Hx Hw; unfold writable_at, wview in *; rewrite (KL x Hx); exact Hw).
assert (KI : forall x, 0 <= x < kLowMemEnd -> mbyte SEGS (rdW W mem') x = mbyte SEGS (rdW W mem) x)
  by (intros x Hx; apply KR; lia).
destruct HM as (HC1 & HC2 & HC3 & HLED & Hpk & Hcnt & Hroom & Hbb & HO1 & HO2 & HO3 & HD1 & HD2 & HD3 & HPL & HPA
  & HNO & HDAT).
(* the copies *)
assert (KC : forall r, cnb_copy B D ly S Hp W mem r -> cnb_copy B D ly S Hp W mem' r).
{ intros r [Hr0 | (Hin & Hnh & Hsrc)]; [left; exact Hr0|]. right.
  split; [exact Hin|]. split; [exact Hnh|].
  destruct Hsrc as (Hby & H4096 & Hceil' & Hamr & Hra & Hhv).
  split; [|split; [exact H4096|]; split; [exact Hceil'|]; split; [exact Hamr|]; split].
  - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W mem') r (bi_x D) Hby).
    intros x Hx. apply KR. lia.
  - exact (r4_ra_low _ _ r (Z.of_nat (length (bi_x D))) ltac:(lia) ltac:(lia) KA Hra).
  - intros Hl. exact (r4_hull_low _ _ r (Z.of_nat (length (bi_x D))) ltac:(lia) Hl ltac:(lia) KA (Hhv Hl)). }
(* the ledger (its cells through PRH_Base's named projections) *)
assert (KLED : prh_ledger B ly S Hp W mem' Lam peak cnt SIZE_MAXZ ran (bi_most D) own).
{ pose proof (prh_ledger_most B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hmv & Hmb).
  pose proof (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hov & Hob).
  split; [|split; [exact (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED)|];
           split; [|exact (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HLED)]].
  - split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_live pi_gz_live);
      [unfold prh_pst; ro_in | exact (prh_ledger_live B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact KI]|].
    split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_peak pi_gz_peak);
      [unfold prh_pst; ro_in | exact (prh_ledger_peak B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact KI]|].
    split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_count pi_gz_count);
      [unfold prh_pst; ro_in | exact (prh_ledger_count B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact KI]|].
    split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_fail pi_gz_fail);
      [unfold prh_pst; ro_in | exact (prh_ledger_fail B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact KI]|].
    split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_ran_out pi_gz_ran_out);
      [unfold prh_pst; ro_in | exact (prh_ledger_ran B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact KI]|].
    split; [split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_most pi_gz_most);
      [unfold prh_pst; ro_in | exact Hmv | exact KI] | exact Hmb]|].
    split; [split; [apply (r4_vm_pst (rdW W mem) (rdW W mem') pi_g_own_ran_out pi_gz_own_ran_out);
      [unfold prh_pst; ro_in | exact Hov | exact KI] | exact Hob]|].
    exact (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED).
  - eapply Forall_impl; [|exact (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED)].
    intros [a kk] (Hk0 & Hab & Hahp & Hmod & Hv). cbn [fst snd] in *.
    split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hahp|]. split; [exact Hmod|].
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb0 & Hb1 & _).
    pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (Hq1 & Hq2).
    apply (pj_valR_frame SEGS (rdW W mem) (rdW W mem') (a - cf_head) 8 kk Hv). intros x Hx. apply KR. cbn in Hx. lia. }
(* the struct opening and contents *)
assert (KO : forall c, 0 <= c -> c + 56 <= 512 -> cnb_open W mem (cnb_F D + c) -> cnb_open W mem' (cnb_F D + c)).
{ intros c Hc0 Hc (Hra & Hhv). split.
  - exact (r4_ra_low _ _ (cnb_F D + c) 56 ltac:(lia) ltac:(lia) KA Hra).
  - exact (r4_hull_low _ _ (cnb_F D + c) 56 ltac:(lia) ltac:(lia) ltac:(lia) KA Hhv). }
assert (KD : forall st c, 0 <= c -> c + 56 <= 512 -> (forall b, In b (cnb_Dof st) -> In b Lam) ->
  cnb_doc W mem Lam (cnb_F D + c) st -> cnb_doc W mem' Lam (cnb_F D + c) st).
{ intros st c Hc0 Hc HDL Hd. destruct st as [(t & Dd)|]; cbn [cnb_doc cnb_Dof] in Hd, HDL |- *.
  - destruct Hd as (Hn & Hdep). split; [|exact Hdep].
    apply (pj_nodeR_frame SEGS t (rdW W mem) (rdW W mem') (prh_lin Lam) (cnb_F D + c) Dd Hn).
    intros x Hx.
    assert (Hxr : 0 <= x < YM05.alloc_ceiling + 4096).
    { destruct Hx as [Hx | ((a & kk) & Hb & Hhold)]; [lia|].
      unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold.
      pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED)
        (a, kk) (HDL _ Hb)) as (Hkk0 & Hab & _). cbn [fst snd] in Hkk0, Hab.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb0 & Hb1 & _).
      pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (_ & Hq2). lia. }
    split; [exact (KR x Hxr) | exact (KW x Hxr)].
  - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W mem') (cnb_F D + c) Hd). intros x Hx. apply KR. lia. }
assert (HL1 : forall b, In b (cnb_Dof st1) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
assert (HL2 : forall b, In b (cnb_Dof st2) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HL3 : forall b, In b (cnb_Dof st3) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; exact Hb).
split; [exact (KC _ HC1)|]. split; [exact (KC _ HC2)|]. split; [exact (KC _ HC3)|].
split; [exact KLED|]. split; [exact Hpk|]. split; [exact Hcnt|]. split; [exact Hroom|].
split; [exact Hbb|].
split; [exact (KO 32 ltac:(lia) ltac:(lia) HO1)|].
split; [exact (KO 128 ltac:(lia) ltac:(lia) HO2)|].
split; [exact (KO 224 ltac:(lia) ltac:(lia) HO3)|].
split; [exact (KD st1 32 ltac:(lia) ltac:(lia) HL1 HD1)|].
split; [exact (KD st2 128 ltac:(lia) ltac:(lia) HL2 HD2)|].
split; [exact (KD st3 224 ltac:(lia) ltac:(lia) HL3 HD3)|].
split; [exact HPL|]. split; [exact HPA|]. split; [exact HNO|].
unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W mem') (bi_data D) (bi_x D) HDAT).
intros x Hx. apply KR. unfold cnb_size in *. lia.
Qed.
(* cnb_fo (a struct's tree against pj_frees) below the ceiling: the tree's footprint (the struct in F and the Lam
   blocks it holds) lies below the allocation ceiling, so the kit's cnb_fo_keep (the order list's frame lemma) moves it
   across a memory change above it, at the same Lam *)
Lemma r4_fo_low : forall D ly S Hp (W : world SEGS) mem mem' md Lam peak cnt ran own o c st,
  ARx ly S Hp W mem md -> 0 <= cnb_F D -> cnb_F D + 512 <= YM05.alloc_ceiling -> 0 <= c -> c + 56 <= 512 ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) own ->
  (forall b, In b (cnb_Dof st) -> In b Lam) ->
  (forall x, 0 <= x < YM05.alloc_ceiling + 4096 ->
     mrestrict (w_H W) mem' (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)) ->
  cnb_fo D W mem Lam o (cnb_F D + c) st -> cnb_fo D W mem' Lam o (cnb_F D + c) st.
Proof.
intros D ly S Hp W mem mem' md Lam peak cnt ran own o c st HAR HF0 HF1 Hc0 Hc HLED HDL KL Hfo.
pose proof asan_consts as (C1 & _ & _ & _ & C5). pose proof (@cf_head_nonneg cp) as Hh0.
eapply cnb_fo_keep; [exact Hfo | | exact HDL].
intros x Hx.
assert (Hxr : 0 <= x < YM05.alloc_ceiling + 4096).
{ destruct Hx as [Hx | ((a & kk) & Hb & Hhold)]; [lia|].
  unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold.
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED)
    (a, kk) (HDL _ Hb)) as (Hkk0 & Hab & _). cbn [fst snd] in Hkk0, Hab.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb0 & Hb1 & _).
  pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (_ & Hq2). lia. }
split.
- unfold mbyte. rewrite (KL x Hxr). reflexivity.
- intros Hw. unfold writable_at, wview in *. rewrite (KL x Hxr). exact Hw.
Qed.
(* the blocks of a struct of cnb_mid are in Lam (cnb_mid's Lam permutation) *)
Lemma r4_mid_Lin : forall D ly S Hp W mem Lam peak cnt ran own (nr : nat) r1 r2 r3 st1 st2 st3,
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  (forall b, In b (cnb_Dof st1) -> In b Lam) /\ (forall b, In b (cnb_Dof st2) -> In b Lam) /\
  (forall b, In b (cnb_Dof st3) -> In b Lam).
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
split; [|split]; intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)).
- apply in_or_app; left; exact Hb.
- apply in_or_app; right; apply in_or_app; left; exact Hb.
- apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb.
Qed.

(* the entry's numbers the steps use *)
Lemma r4_entry : forall D, cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling + 4096 <= cnb_S1 D /\ cnb_S1 D + 160 <= cnb_sp0 D /\
  cnb_sp0 D < cnb_S1 D + 192 /\ cnb_sp0 D + 64 <= 2 ^ 47 /\ cnb_sp0 D - STK <= cnb_S1 D /\ bi_ran D = 0 /\
  4096 <= bi_data D /\ bi_data D + cnb_size D <= YM05.alloc_ceiling.
Proof.
intros D HPRE.
destruct (cnb_entry_facts B ARx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & _). pose proof cnb_stk_val as HS.
pose proof HPRE as HP. unfold cnb_pre in HP. cbv zeta in HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & (_ & Hd0 & Hd1 & _) & _ & _ & _ & HRAN & _).
unfold cnb_size. repeat split; try assumption; lia.
Qed.

(* a store of 8 bytes at s1 + o (o = 0 / 8, the rc slots): the memory agrees off the 8 bytes *)
Lemma r4_agree : forall (W : world SEGS) mem mem' lo,
  (forall x : word, ~ (lo <= bv_unsigned x < lo + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + 8) ->
  mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a).
Proof. intros W mem mem' lo H a Ha Hn. apply H. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma r4_agree_v : forall (W : world SEGS) mem mem' lo,
  (forall x : word, ~ (lo <= bv_unsigned x < lo + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + 8) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a.
Proof. intros W mem mem' lo H a Ha Hn. unfold aview, mbyte. rewrite (r4_agree W mem mem' lo H a Ha Hn). reflexivity. Qed.

(* cnb_baseR at wle' SEGS RZ_cf across the store (CB5 / CB6 run after parse_noting): the journal (the bytes are the
   function's own stack window) by the kit's FIXED recipe at the same wk and the same relation (cnb_J_rebaseR,
   ajournal_x_execR, cnb_J_fixedR), the frame and the read-only view (below the ceiling), the saved words (above
   s1 + 16) *)
Lemma r4_base_store : forall D fxk ly S Hp W regs mem md k wk mem' X o,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k wk -> 0 <= o <= 8 ->
  (forall x : word, ~ (cnb_S1 D + o <= bv_unsigned x < cnb_S1 D + o + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall x : word, w_H W x = true -> mem' x = mem x) ->
  cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem' (with_vm_backing (m_vm_lazy md) X md) k wk /\
  0 <= cnb_F D /\ cnb_F D + 512 <= YM05.alloc_ceiling /\ ARx ly S Hp W mem md.
Proof.
intros D fxk ly S Hp W regs mem md k wk mem' X o HPRE HB Ho Hfr Hgr Hhid.
destruct (r4_entry D HPRE) as (H16 & HS1c & HS1a & HS1b & H47 & HSTK & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5). pose proof cnb_stk_val as HSv.
pose proof (r4_agree_v W mem mem' (cnb_S1 D + o) Hfr) as KV.
destruct HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof HJ as HJ'. unfold cnb_JR in HJ'. destruct HJ' as (WS & HJW & _).
pose proof (ajxR_ar HJW) as HAR. pose proof (ajxR_ly HJW) as Hly.
assert (EF1 : ly_F ly = ly_F (bi_ly D)) by (destruct Hly as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EFa1 : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF1; reflexivity).
assert (EFB : fs_frame_bytes CNB_CID = 512) by reflexivity.
destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa1 in HF4096, HFceil. rewrite EFB in HFceil.
split; [|split; [lia|]; split; [lia | exact HAR]].
split; [exact Hz|]. split; [exact Hk|].
split.
{ apply (cnb_J_fixedR B ARx WLE' D wk ly S Hp W mem md k _ _ _ _ _ _ _ HJ).
  apply (ajournal_x_execR SEGS B prh_pst ARx LAWS pa_segs_low WLE' _ _ _ _ _ _ _ _ _ _ ly S Hp W mem md k mem'
    (with_vm_backing (m_vm_lazy md) X md) (fun z => cnb_S1 D + o <= z < cnb_S1 D + o + 8)
    (cnb_J_rebaseR B ARx WLE' D wk ly S Hp W mem md k HJ) Hfr Hgr Hhid (same_but_materialized_wvb_any md X)).
  intros a Ha. left. lia. }
split.
{ split; [exact Hfrs|]. split; [exact Hnin|]. split.
  - rewrite <- Hflag. apply (ro_rdword_kept _ _ 0 YM05.alloc_ceiling); [|lia|lia].
    intros a Ha. apply KV; lia.
  - split; intros a Ha; [apply (apresent_grows (w_H W) mem mem' a Hgr); exact (Hfpres a Ha)
                        | apply (apresent_grows (w_H W) mem mem' a Hgr); exact (Hspres a Ha)]. }
split.
{ unfold cnb_saved in *. apply Forall_forall. intros [o' r] Hin.
  pose proof (proj1 (Forall_forall _ _) HSV (o', r) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho' : 56 <= o' <= 152) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply (ro_rdword_kept _ _ (cnb_S1 D + o + 8) (2 ^ 64)); [|lia|lia].
  intros a Ha. apply KV; lia. }
split; [exact R3|]. split; [exact R4|].
intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr).
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)]).
pose proof (pa_segs_low a Himg). apply KV; lia.
Qed.

(* THE rc-SLOT STORE `sd a0, o(s1)` (CB5 0x81c74 o = 8, CB6 0x81ca0 o = 0) with every cut fact carried across it; the
   three structs' cnb_fo too (r4_fo_low), at any grant. Both uses run after parse_noting: the cut's base is at wle'
   SEGS RZ_cf (cnb_baseR) and the stretch concludes SRr' SEGS RZ_cf; the store itself frees nothing *)
Lemma r4_sd_cut : forall P, srr_inv_laws SEGS P ->
  forall D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 Q off o rcv,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k wk ->
  cnb_slots D W mem r2 r3 -> cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  r4_is_sd off 9%bv 10%bv o = true -> 0 <= off < 2 ^ 28 -> (o = 0 \/ o = 8) ->
  getr regs 9%bv = w64 (cnb_S1 D) -> getr regs 10%bv = w64 rcv -> P mem ->
  (forall X mem',
     cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem' (with_vm_backing (m_vm_lazy md) X md) k wk ->
     cnb_slots D W mem' r2 r3 -> cnb_mid B D ly S Hp W mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
     (forall o1, cnb_fo D W mem Lam o1 (cnb_d1 D) st1 -> cnb_fo D W mem' Lam o1 (cnb_d1 D) st1) ->
     (forall o2, cnb_fo D W mem Lam o2 (cnb_d2 D) st2 -> cnb_fo D W mem' Lam o2 (cnb_d2 D) st2) ->
     (forall o3, cnb_fo D W mem Lam o3 (cnb_d3 D) st3 -> cnb_fo D W mem' Lam o3 (cnb_d3 D) st3) ->
     cnb_rcslot D W mem' o rcv ->
     (forall o' v, (o' = 0 \/ o' = 8) -> o' <> o -> cnb_rcslot D W mem o' v -> cnb_rcslot D W mem' o' v) ->
     P mem' ->
     SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc (off + 4)) regs mem'
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 Q off o rcv
  HPRE HB HSL HM Hsd Hoff Ho G9 G10 HPM HK.
destruct (r4_entry D HPRE) as (H16 & HS1c & HS1a & HS1b & H47 & HSTK & _ & Hd0 & Hd1).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hpres : forall a, cnb_sp0 D - STK <= a < cnb_sp0 D -> apresent (w_H W) mem a).
{ pose proof HB as (_ & _ & HJ & _). unfold cnb_JR in HJ. destruct HJ as (WS & HJW & _). exact (ajxR_pres HJW). }
apply (r4_hs_sd P PLAW W fxk regs mem md Q off (off + 4) 9%bv 10%bv o (cnb_S1 D + o) Hsd Hoff eq_refl).
- rewrite G9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros j Hj. apply Hpres. lia.
- exact HPM.
- intros X mem' Hfr Hgr Hhid Hrd HP'.
  destruct (r4_base_store D fxk ly S Hp W regs mem md k wk mem' X o HPRE HB ltac:(lia) Hfr Hgr Hhid)
    as (HB' & HF0 & HF1 & HAR).
  pose proof (r4_agree_v W mem mem' (cnb_S1 D + o) Hfr) as KV.
  assert (KL : forall x, 0 <= x < YM05.alloc_ceiling + 4096 ->
    mrestrict (w_H W) mem' (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x))
    by (intros x Hx; apply (r4_agree W mem mem' (cnb_S1 D + o) Hfr); lia).
  pose proof HM as (_ & _ & _ & HLED & _).
  destruct (r4_mid_Lin D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HM) as (HL1 & HL2 & HL3).
  apply (HK X mem' HB').
  + unfold cnb_slots in *. apply Forall_forall. intros [o' v] Hin.
    pose proof (proj1 (Forall_forall _ _) HSL (o', v) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho' : 16 <= o' <= 48) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
    rewrite <- Hv. apply (ro_rdword_kept _ _ (cnb_S1 D + o + 8) (2 ^ 64)); [|lia|lia].
    intros a Ha. apply KV; lia.
  + exact (r4_mid_low D ly S Hp W mem mem' md Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HAR Hd0 Hd1 HF0 HF1 KL HM).
  + intros o1 Hfo.
    exact (r4_fo_low D ly S Hp W mem mem' md Lam peak cnt ran own o1 32 st1 HAR HF0 HF1 ltac:(lia) ltac:(lia) HLED HL1 KL Hfo).
  + intros o2 Hfo.
    exact (r4_fo_low D ly S Hp W mem mem' md Lam peak cnt ran own o2 128 st2 HAR HF0 HF1 ltac:(lia) ltac:(lia) HLED HL2 KL Hfo).
  + intros o3 Hfo.
    exact (r4_fo_low D ly S Hp W mem mem' md Lam peak cnt ran own o3 224 st3 HAR HF0 HF1 ltac:(lia) ltac:(lia) HLED HL3 KL Hfo).
  + unfold cnb_rcslot. rewrite Hrd, G10. unfold w64. rewrite Z_to_bv_unsigned. reflexivity.
  + intros o' v Ho' Hne Hv. unfold cnb_rcslot in *. rewrite <- Hv.
    apply (ro_rdword_kept _ _ (cnb_S1 D + o') (cnb_S1 D + o' + 8)); [|lia|lia].
    intros a Ha. apply KV; lia.
  + exact HP'.
Qed.

(* ---- the walk's register bookkeeping (Cno102A_R6.v's, B' names) ---- *)
Lemma r4_li : forall regs i, v_addi (getr regs 0%bv) i = w64 i.
Proof. intros regs i. rewrite ro_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. Qed.
Lemma r4_mv : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Ltac r4_get HR := apply (cnb_regsat_get _ _ _ _ HR); unfold cnb_core, cnb_s8; ro_in.
Ltac r4_rs_one HR := cbn [fst snd]; ro_getr;
  first [ reflexivity | rewrite r4_li; reflexivity | rewrite r4_mv; ro_getr; first [reflexivity | r4_get HR] | r4_get HR ].
Ltac r4_rs HR := unfold cnb_regsat, cnb_core, cnb_s8; cbn [app];
  repeat (apply Forall_cons; [r4_rs_one HR |]); apply Forall_nil.
Ltac r4_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.
Ltac r4_acsl := unfold cnb_core, cnb_s8; cbn [app]; repeat (apply Forall_cons; [cbn [fst]; r4_acs |]); apply Forall_nil.
(* THE VM_COMPUTE GUARD: the closed decode / slot checks of the listing, each by its shape *)
Ltac r4_vm := lazymatch goal with
  | |- cnb_is_addi _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_ld _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_lbu _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_beqz _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_bnez _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_j _ _ = true => vm_compute; reflexivity
  | |- r4_is_sd _ _ _ _ = true => vm_compute; reflexivity
  | |- plookup B_prog_tpi_cno (CNB_OFF + _) = Some _ => vm_compute; reflexivity
  end.

(* the cut's base across a register change that keeps gp / tp, the materialised model and a larger spent wild budget,
   at any world relation R (the kit's cnb_base_matR / cnb_base_monoR): CB5 / CB6 use the forms at wle' SEGS RZ_cf,
   CB4 their wle instances r4_base / r4_mat / r4_mono *)
Lemma r4_baseR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs regs' mem md k wk,
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs' mem md k wk.
Proof.
intros R D fxk ly S Hp W regs regs' mem md k wk (Hz & Hk & HJ & HF & HSV & R3 & R4 & HRD) E3 E4.
repeat (split; [eassumption|]). split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HRD.
Qed.
Lemma r4_matR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs mem md k wk X,
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros R D fxk ly S Hp W regs mem md k wk X HB.
exact (cnb_base_matR B ARx LAWS R D fxk ly S Hp W regs regs mem md k wk X HB eq_refl eq_refl).
Qed.
(* the spent wild budget raised where a reading is skipped (the kit's cnb_base_monoR) *)
Lemma r4_monoR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs mem md k wk wk',
  (wk <= wk')%nat ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk'.
Proof. intros R D fxk ly S Hp W regs mem md k wk wk' Hw HB. eapply cnb_base_monoR; eassumption. Qed.
Lemma r4_base : forall D fxk ly S Hp W regs regs' mem md k wk,
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs' mem md k wk.
Proof. exact (r4_baseR (@wle SEGS)). Qed.
Lemma r4_mat : forall D fxk ly S Hp W regs mem md k wk X,
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof. exact (r4_matR (@wle SEGS)). Qed.
Lemma r4_mono : forall D fxk ly S Hp W regs mem md k wk wk', (wk <= wk')%nat ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk'.
Proof. exact (r4_monoR (@wle SEGS)). Qed.
Ltac r4_base HB := eapply r4_base; [repeat (first [exact HB | apply r4_mat]) | ro_getr; reflexivity | ro_getr; reflexivity].
Ltac r4_baseR HB :=
  eapply r4_baseR; [repeat (first [exact HB | apply r4_matR]) | ro_getr; reflexivity | ro_getr; reflexivity].

(* ---- THE HULL STAGE of a skipped reading: it runs no allocator call, so the cut's budget for the rest of the
   all-granted list is one for the rest after that reading (hull_budget_app with nothing used, hull_used_refl), over
   the Base's split equations cnb_hrest_<stage>_split ---- *)
Lemma r4_hull_drop : forall S (A Rl : list PresetReqAt.hev),
  PresetHullBudget.hull_budget S (A ++ Rl) -> PresetHullBudget.hull_budget S Rl.
Proof. intros S A Rl H. exact (PresetHullBudget.hull_budget_app S S A Rl H (PresetHullBudget.hull_used_refl S A)). Qed.
(* reading 1 skipped (CB4's free exit) *)
Lemma r4_hull_rd1 : forall S x,
  PresetHullBudget.hull_budget S (cnb_hrest_copies x) -> PresetHullBudget.hull_budget S (cnb_hrest_rd1 x).
Proof. intros S x H. rewrite (cnb_hrest_rd1_split x) in H. exact (r4_hull_drop S _ _ H). Qed.
(* reading 2 skipped (CB5's skip arm to CNB_READ3, CB4's free exit) *)
Lemma r4_hull_rd2 : forall S x,
  PresetHullBudget.hull_budget S (cnb_hrest_rd1 x) -> PresetHullBudget.hull_budget S (cnb_hrest_rd2 x).
Proof. intros S x H. rewrite (cnb_hrest_rd2_split x) in H. exact (r4_hull_drop S _ _ H). Qed.
(* reading 3 skipped (CB6's skip arm to CNB_CMP, CB4's free exit) *)
Lemma r4_hull_rd0 : forall S x,
  PresetHullBudget.hull_budget S (cnb_hrest_rd2 x) -> PresetHullBudget.hull_budget S (cnb_hrest_rd0 x).
Proof. intros S x H. rewrite (cnb_hrest_rd0_split x) in H. exact (r4_hull_drop S _ _ H). Qed.

(* cnb_mid at a larger count: the count and the budget conjuncts weaken (nr <= nr' <= 3) *)
Lemma r4_live_nonneg : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (@cf_head_nonneg cp) as H0.
assert (H1 : 0 <= hpeakR (PRH_FnPj.prhPj_ptrace x))
  by (destruct (PRH_FnPj.prhPj_ptrace x) as [|e r]; cbn [hpeakR]; lia).
nia.
Qed.
Lemma r4_mid_nr : forall D ly S Hp W mem Lam peak cnt ran own (nr nr' : nat) r1 r2 r3 st1 st2 st3,
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> (nr <= nr' <= 3)%nat ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr' r1 r2 r3 st1 st2 st3.
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr nr' r1 r2 r3 st1 st2 st3
  (C1 & C2 & C3 & HL & Hpk & Hcnt & Hroom & Hbb & HRest) Hn.
pose proof (r4_live_nonneg (bi_x D)) as HLV.
assert (Hnc : 0 <= ck_ncalls (bi_x D)) by (unfold ck_ncalls; lia).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact HL|]. split; [exact Hpk|].
split; [nia|]. split; [exact Hroom|].
split; [rewrite !Nat2Z.inj_sub in * by lia; nia | exact HRest].
Qed.
(* the ledger of cnb_mid, and the g_own_ran_out byte it holds (PRH_Base's named projection prh_ledger_own) *)
Lemma r4_mid_led : forall D ly S Hp W mem Lam peak cnt ran own (nr : nat) r1 r2 r3 st1 st2 st3,
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) own.
Proof. intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 (_ & _ & _ & HL & _). exact HL. Qed.
Lemma r4_mid_own : forall D ly S Hp W mem Lam peak cnt ran own (nr : nat) r1 r2 r3 st1 st2 st3,
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> prh_own W mem own.
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HM.
exact (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ (r4_mid_led D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HM)).
Qed.

(* ---- THE g_own_ran_out BYTE: prh_own (r4_mid_own) gives the byte the lbu reads (cnbi_own: VAL (A_OBJ 13) = the cell) ---- *)
Lemma r4_own_byte : forall (W : world SEGS) mem own, prh_own W mem own ->
  mbyte SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 13) + 0) = Some (Z_to_bv 8 own).
Proof.
intros W mem own (Hv & Ho). rewrite Z.add_0_r, (cnbi_own B IMG).
assert (Hz : pi_gz_own_ran_out = 1%nat) by reflexivity. rewrite Hz in Hv.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv.
destruct Ho as [-> | ->]; reflexivity.
Qed.
(* the byte as the register value the branch tests *)
Lemma r4_byte01 : forall own, own = 0 \/ own = 1 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 8 own)) = w64 own.
Proof. intros own [-> | ->]; reflexivity. Qed.
(* the address of `lbu a1, 0x140(s8)`: s8 = the hi atom 9, VAL (A_HI 9) + 320 = VAL (A_OBJ 13) (cnbi_hi) *)
Lemma r4_own_addr : forall regs, getr regs 24%bv = w64 (VAL (A_HI 9)) ->
  bv_unsigned (getr regs 24%bv) + 320 = VAL (A_OBJ 13) + 0.
Proof.
intros regs H. rewrite H. unfold w64. rewrite unsigned_lit_small by (apply pa_val_range).
rewrite <- (cnbi_hi B IMG). lia.
Qed.
(* REFUTATION of the byte branches 640 / 684 -> 736 (and the CB4 own0 = 0 arm of 600): a byte 0 tests zero *)
Lemma r4_byte0_ceq : forall regs, c_eq (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0))) (getr regs 0%bv) = true.
Proof. intros regs. rewrite ro_getr0. reflexivity. Qed.
(* REFUTATION of the CB4 ran-out arm 608 -> 612: fuzz_alloc_ran_out returns g_ran_out (cnb_ro_call's a0 = ran), which
   cnb_pre pins to 0 at entry (bi_ran D = 0) and the reading-free stretch keeps *)
Lemma r4_ran0_ceq : forall D regs, cnb_pre (fx := fx) B ARx CTX0 D -> getr regs 10%bv = w64 (bi_ran D) ->
  c_eq (getr regs 10%bv) (getr regs 0%bv) = true.
Proof.
intros D regs HPRE H. destruct (r4_entry D HPRE) as (_ & _ & _ & _ & _ & _ & HRAN & _).
rewrite H, HRAN, ro_getr0. reflexivity.
Qed.

(* ---- THE READINGS' EVENTS, g_ran_out AND THE STRUCTS (the contract's exact-position form, Cno102B_Base.v
   20c89a1d4da2): the model's ranout of a skipped reading (grant None) is false, so g_ran_out after the readings is 1
   exactly when a reading made ran out; a reading skipped after a ran-out reading adds no event (cnb_revs2 /
   cnb_revs3's skip) and leaves its struct zero (cnb_rds2 / cnb_rds3) ---- *)
Lemma r4_ranz1 : forall D o1, cnb_ranz D o1 None None = if cnb_ro D o1 then 1 else 0.
Proof. intros D o1. unfold cnb_ranz, ck_cno_ranout, cnb_ro. destruct (PresetRun.ranout _ (bi_x D) o1); reflexivity. Qed.
Lemma r4_ranz2 : forall D o1 o2, cnb_ranz D o1 o2 None = if cnb_ro D o1 || cnb_ro D o2 then 1 else 0.
Proof.
intros D o1 o2. unfold cnb_ranz, ck_cno_ranout, cnb_ro.
destruct (PresetRun.ranout _ (bi_x D) o1), (PresetRun.ranout _ (bi_x D) o2); reflexivity.
Qed.
(* CB5: g_ran_out = 1 after reading 1 says reading 1 ran out, 0 says it did not *)
Lemma r4_ro1_true : forall D o1, 1 = cnb_ranz D o1 None None -> cnb_ro D o1 = true.
Proof. intros D o1. rewrite r4_ranz1. destruct (cnb_ro D o1); [reflexivity | discriminate]. Qed.
Lemma r4_ro1_false : forall D o1, 0 = cnb_ranz D o1 None None -> cnb_ro D o1 = false.
Proof. intros D o1. rewrite r4_ranz1. destruct (cnb_ro D o1); [discriminate | reflexivity]. Qed.
(* CB6: the same after readings 1 and 2 *)
Lemma r4_ro2_false : forall D o1 o2, 0 = cnb_ranz D o1 o2 None -> cnb_ro D o1 = false /\ cnb_ro D o2 = false.
Proof.
intros D o1 o2. rewrite r4_ranz2. destruct (cnb_ro D o1), (cnb_ro D o2); intros H; cbv iota beta in H;
  first [discriminate H | split; reflexivity].
Qed.
(* the skip: reading 2 (CB5, grant None) or reading 3 (CB6, grant None) after a ran-out reading adds no event *)
Lemma r4_revs2_skip : forall D o1, cnb_ro D o1 = true -> cnb_revs2 D o1 None = cnb_pe D o1.
Proof. intros D o1 H. unfold cnb_revs2. rewrite H. apply app_nil_r. Qed.
Lemma r4_revs3_skip : forall D o1 o2, 1 = cnb_ranz D o1 o2 None -> cnb_revs3 D o1 o2 None = cnb_revs2 D o1 o2.
Proof.
intros D o1 o2. rewrite r4_ranz2. unfold cnb_revs3, cnb_revs2.
destruct (cnb_ro D o1), (cnb_ro D o2); intros H; cbv iota beta in H |- *;
  first [discriminate H | rewrite ?app_nil_r; reflexivity].
Qed.
(* the structs at the skip: reading 2 (CB5) / reading 3 (CB6) skipped, its struct stays zero (None) *)
Lemma r4_rds2_skip : forall D o1 st1, cnb_ro D o1 = true -> cnb_rd D o1 st1 -> cnb_rds2 D o1 None st1 None.
Proof. intros D o1 st1 Hro H. unfold cnb_rds2. rewrite Hro. split; [exact H | exact eq_refl]. Qed.
Lemma r4_rds3_skip : forall D o1 o2 st1 st2, 1 = cnb_ranz D o1 o2 None -> cnb_rds2 D o1 o2 st1 st2 ->
  cnb_rds3 D o1 o2 None st1 st2 None.
Proof.
intros D o1 o2 st1 st2. rewrite r4_ranz2. unfold cnb_rds3, cnb_rds2.
destruct (cnb_ro D o1), (cnb_ro D o2); intros H (H1 & H2); cbv iota beta in H, H2 |- *;
  first [discriminate H | split; [exact H1 | split; [exact H2 | exact eq_refl]]].
Qed.
(* the reading-2 struct of a pn3 call state: reading 1 did not run out *)
Lemma r4_rds2_rd : forall D o1 o2 st1 st2, cnb_ro D o1 = false -> cnb_rds2 D o1 o2 st1 st2 ->
  cnb_rd D o1 st1 /\ cnb_rd D o2 st2.
Proof. intros D o1 o2 st1 st2 Hro (H1 & H2). rewrite Hro in H2. exact (conj H1 H2). Qed.

(* ---- CB4, CNB_READ1 -> CNB_FREE (own0 <> 0: 600 bnez a0 taken, 736 li s8, 1; the budget 0 -> 6 by r4_monoR, read1's
   own0 <> 0 -> cnb_cdead D into free's ownl <> 0 arm) or the parse_noting call state CNB_PN1 (own0 = 0, budget 0).
   The stretch runs before any reading, so it stays at SRr and its cuts at wle; CNB_FREE's cut is taken at wle' SEGS
   RZ_cf (cnb_ex_freeR), so the free exit lifts the base by the Base's cnb_baseR_mono (wle_wle') ---- *)
Theorem cnb_read1_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_read1 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ1) regs mem md)
    (fun W' c' => (cnb_ex_freeR (fx := fx) B ARx WLE' D W' c' \/ cnb_ex_pn1 (fx := fx) B ARx D W' c') /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Hoc & Hcd & EHp & HRP & HM & HHB).
pose proof (r4_mid_own D ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) (bi_ran D) own0 0 r1 r2 r3 None None None HM) as HOWN.
destruct (r4_entry D HPRE) as (H16 & HS1c & HS1a & HS1b & H47 & HSTK & HRAN & _).
pose proof HOWN as (_ & Ho01).
unfold CNB_READ1.
(* 592 auipc s8, hi(g_own_ran_out) *)
apply (r4_hs_hi W fxk regs mem md _ 592 596 24%bv 9); [r4_vm | reflexivity | lia | reflexivity |].
intros X1.
(* 596 lbu a0, lo(g_own_ran_out)(s8): the byte own0 *)
apply (r4_hs_ldhi W fxk _ mem _ _ 596 600 10%bv 24%bv 9 (A_OBJ 13) 0 (Z_to_bv 8 own0));
  [r4_vm | reflexivity | lia | reflexivity | ro_getr; reflexivity | exact (r4_own_byte W mem own0 HOWN) |].
intros X2. rewrite (r4_byte01 own0 Ho01).
destruct Ho01 as [E0 | E1].
- (* own0 = 0: every copy non-NULL; 600 bnez a0 falls through, the guard calls fuzz_alloc_ran_out *)
  subst own0. destruct (Hoc eq_refl) as (Nr1 & Nr2 & Nr3).
  apply (cnb_hs_bnez W fxk _ mem _ _ 600 10%bv 136 736 604 true);
    [r4_vm | lia | lia | reflexivity | reflexivity | ro_getr; exact (r4_byte0_ceq _) |].
  intros X3. cbv iota.
  (* 604 jal fuzz_alloc_ran_out *)
  apply (cnb_hs_call W fxk _ mem _ _ 604 608 AS_fuzz_alloc_ran_out); [r4_vm | lia | reflexivity |].
  intros X4.
  eapply SRr_bind.
  { apply (cnb_ro_call B ARx LAWS IMG HRO P PCALL CTX0 D fxk ly S Hp W _ mem _ k 0%nat
      (bi_Lam D) (bi_peak D) (bi_cnt D) (bi_ran D) 0 0 r1 r2 r3 None None None 608 HPRE).
    - unfold cnb_ro_rets. ro_in.
    - r4_base HB.
    - r4_rs HR.
    - ro_getr. reflexivity.
    - exact HSL.
    - exact HM.
    - exact HPM. }
  cbv beta. intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & _ & _ & _ & HKT2
    & HPM2).
  assert (HR2 : cnb_regsat regs2 (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)])).
  { apply (cnb_regsat_pres (regupd (regupd (regupd regs 24%bv (w64 (VAL (A_HI 9)))) 10%bv (w64 0)) 1%bv
      (w64 (cnb_pc 608))) regs2); [r4_rs HR | exact HP2 | r4_acsl]. }
  (* 608 beqz a0: g_ran_out = 0, taken (the ran-out arm 612 refuted by r4_ran0_ceq) *)
  apply (cnb_hs_beqz W2 fxk regs2 mem2 md2 _ 608 10%bv 12 620 612 true);
    [r4_vm | lia | lia | reflexivity | reflexivity | exact (r4_ran0_ceq D regs2 HPRE R10) |].
  intros X5. cbv iota.
  (* 620 mv a0, s9; 624 mv a1, s7; 628 mv a2, s6 *)
  apply (cnb_hs_addi W2 fxk _ mem2 _ _ 620 624 10%bv 25%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X6.
  apply (cnb_hs_addi W2 fxk _ mem2 _ _ 624 628 11%bv 23%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X7.
  apply (cnb_hs_addi W2 fxk _ mem2 _ _ 628 632 12%bv 22%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X8.
  apply SRr_ret. split; [right | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, r1, r2, r3. split; [reflexivity|].
  split; [r4_base HB2|].
  split; [r4_rs HR2|].
  split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|]. split; [exact EHp|].
  split; [exact HRP|].
  (* the hull stage is still the copies' (S kept across the ran-out call, no reading made yet) *)
  split; [rewrite HRAN in HM2; exact HM2 | exact HHB].
- (* own0 = 1: 600 bnez a0 taken to 736 li s8, 1, then CNB_FREE with r = 1, nr = 0 *)
  subst own0. rewrite (cnb_base_R_wle B ARx) in HB.
  apply (cnb_hs_bnez W fxk _ mem _ _ 600 10%bv 136 736 604 false);
    [r4_vm | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0; reflexivity |].
  intros X3. cbv iota.
  apply (cnb_hs_addi W fxk _ mem _ _ 736 740 24%bv 0%bv 1); [r4_vm | reflexivity | lia | reflexivity |].
  intros X4.
  apply SRr_ret. split; [left | exact HPM].
  exists fxk, ly, S, Hp. do 4 eexists.
  exists (bi_Lam D), (bi_peak D), (bi_cnt D), (bi_ran D), 0%nat, r1, r2, r3, 1, 1, None, None, None, None, None, None.
  split; [reflexivity|].
  (* CNB_FREE's cut is taken after a free: the base at wle lifted into wle' SEGS RZ_cf *)
  split; [apply (cnb_baseR_mono B ARx (@wle SEGS) WLE' (wle_wle' SEGS YGcfRehidePost.RZ_cf));
          apply (r4_monoR (@wle SEGS) _ _ _ _ _ _ _ _ _ _ 0%nat); [lia | r4_baseR HB]|].
  split; [r4_rs HR|].
  split; [exact HSL|]. split; [exact HM|]. split; [lia|].
  (* r = 1 by ownl = own0 = 1; the ownl = 0 clause does not apply *)
  split; [left; split; [reflexivity | left; lia]|]. split; [intros E; discriminate E|].
  (* the refused-copy arm (ownl <> 0): no event since read1 (S unchanged), so read1's cnb_prog, read1's zero structs
     (cnb_mid .. None None None), and read1's refused copy dead at a consumer run (own0 = 1 <> 0) *)
  split.
  { intros _. split; [exact HRP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact (Hcd ltac:(lia)). }
  (* readings 1, 2 and 3 skipped: they pay nothing (copies -> rd1 -> rd2 -> rd0) *)
  exact (r4_hull_rd0 S (bi_x D) (r4_hull_rd2 S (bi_x D) (r4_hull_rd1 S (bi_x D) HHB))).
Qed.

(* ---- CB5, CNB_READ2 -> CNB_READ3 (the ran-out flag set: rc2 = -1; the budget 2 -> 4 by r4_monoR) or the
   parse_noting call state CNB_PN2 (budget 2); the byte branch 640 -> 736 is refuted (the cut's own 0: r4_mid_own,
   r4_own_byte, r4_byte0_ceq); reading 1's cnb_fo crosses the store (r4_sd_cut) and the ran-out call (cnb_ro_callR).
   CNB_READ2 holds after the first parse_noting: the cut is taken at wle' SEGS RZ_cf (cnb_at_read2R, exits
   cnb_ex_read3R / cnb_ex_pn2R), the hand steps are the kit's R forms there, and the segment concludes SRr' SEGS
   RZ_cf ---- *)
Theorem cnb_read2_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_read2R (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ2) regs mem md)
    (fun W' c' => (cnb_ex_read3R (fx := fx) B ARx WLE' D W' c' \/ cnb_ex_pn2R (fx := fx) B ARx WLE' D W' c') /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Nr1 & Nr2 & Nr3 & HPG & HRZ & HM & HRES & HRD & HFO & HHB).
pose proof (r4_mid_own D ly S Hp W mem Lam peak cnt ran 0 1 r1 r2 r3 st1 None None HM) as HOWN.
destruct (r4_entry D HPRE) as (H16 & HS1c & HS1a & HS1b & H47 & HSTK & HRAN & _).
pose proof asan_consts as (C1 & _).
unfold CNB_READ2.
(* 636 lbu a1, 0x140(s8): the g_own_ran_out byte, 0 *)
apply (cnb_hs_lbuR WLE' W fxk regs mem md _ 636 640 11%bv 24%bv 320 (VAL (A_OBJ 13) + 0) (Z_to_bv 8 0));
  [r4_vm | reflexivity | lia | reflexivity | apply r4_own_addr; r4_get HR | exact (r4_own_byte W mem 0 HOWN) |].
intros X1.
(* 640 bnez a1: falls through (the byte branch to 736 refuted) *)
apply (cnb_hs_bnezR WLE' W fxk _ mem _ _ 640 11%bv 96 736 644 true);
  [r4_vm | lia | lia | reflexivity | reflexivity | ro_getr; exact (r4_byte0_ceq _) |].
intros X2. cbv iota.
(* 644 sd a0, 8(s1): rc1 to its slot *)
apply (r4_sd_cut P PLAW D fxk ly S Hp W _ mem _ k 2%nat Lam peak cnt ran 0 1 r1 r2 r3 st1 None None _ 644 8 rc1 HPRE);
  [r4_baseR HB | exact HSL | exact HM | r4_vm | lia | right; reflexivity
  | ro_getr; r4_get HR | ro_getr; r4_get HR | exact HPM |].
intros X3 mem1 HB1 HSL1 HM1 HFs1 _ _ HRC1 _ HPM1.
pose proof (HFs1 o1 HFO) as HFO1.
(* 648 jal fuzz_alloc_ran_out *)
apply (cnb_hs_callR WLE' W fxk _ mem1 _ _ 648 652 AS_fuzz_alloc_ran_out); [r4_vm | lia | reflexivity |].
intros X4.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (cnb_ro_callR B ARx LAWS IMG HRO WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (wle'_trans SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)
    P PCALL CTX0 D fxk ly S Hp W _ mem1 _ k 2%nat Lam peak cnt ran 0 1 r1 r2 r3 st1 None None 652 HPRE).
  - unfold cnb_ro_rets. ro_in.
  - r4_baseR HB1.
  - r4_rs HR.
  - ro_getr. reflexivity.
  - exact HSL1.
  - exact HM1.
  - exact HPM1. }
cbv beta. intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & HFc1 & _ & _ & HKT2
  & HPM2).
pose proof (HFc1 o1 HFO1) as HFO2.
assert (HR2 : cnb_regsat regs2 (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)])).
{ apply (cnb_regsat_pres (regupd (regupd regs 11%bv (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) 1%bv
    (w64 (cnb_pc 652))) regs2); [r4_rs HR | exact HP2 | r4_acsl]. }
assert (G9 : getr regs2 9%bv = w64 (cnb_S1 D)) by r4_get HR2.
pose proof (cnb_rcslot_agree D W mem1 W2 mem2 8 rc1 H16 ltac:(lia) HKT2 HRC1) as HRC2.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ (r4_mid_led _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2))
  as (_ & _ & _ & _ & Hran).
revert HRZ. destruct Hran as [Er | Er]; subst ran; intros HRZ.
- (* g_ran_out = 0: 652 beqz a0 taken, the reading *)
  apply (cnb_hs_beqzR WLE' W2 fxk regs2 mem2 md2 _ 652 10%bv 12 664 656 true);
    [r4_vm | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 664 ld a0, 24(s1): r2 *)
  apply (cnb_hs_ldR WLE' W2 fxk regs2 mem2 _ _ 664 668 10%bv 9%bv 24 (cnb_S1 D + 24) r2);
    [r4_vm | reflexivity | lia | reflexivity
    | rewrite G9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSL2 (24, r2) ltac:(ro_in)) |].
  intros X6.
  (* 668 mv a1, s7; 672 mv a2, s5 *)
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 668 672 11%bv 23%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X7.
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 672 676 12%bv 21%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X8.
  apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [right | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, r1, r2, r3, rc1, st1, o1.
  split; [reflexivity|].
  split; [r4_baseR HB2|].
  split; [r4_rs HR2|].
  split; [exact HSL2|]. split; [exact HRC2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* the events: S is kept across the ran-out call; reading 1 did not run out (g_ran_out = 0) *)
  split; [exact HPG|]. split; [exact (r4_ro1_false D o1 HRZ)|].
  split; [exact HM2|]. split; [exact HRES|]. split; [exact HRD|].
  (* the hull stage is still rd1 (S kept across the ran-out call, reading 2 not made yet) *)
  split; [exact HFO2 | exact HHB].
- (* g_ran_out = 1: 652 beqz a0 falls through, the reading is skipped (rc2 = -1, st2 = None) *)
  apply (cnb_hs_beqzR WLE' W2 fxk regs2 mem2 md2 _ 652 10%bv 12 664 656 false);
    [r4_vm | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 656 li a0, -1; 660 j +20 *)
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 656 660 10%bv 0%bv (-1)); [r4_vm | reflexivity | lia | reflexivity |].
  intros X6.
  apply (cnb_hs_jR WLE' W2 fxk _ mem2 _ _ 660 680 20); [r4_vm | lia | reflexivity | lia |].
  intros X7.
  apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [left | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, 1, r1, r2, r3, rc1, (-1), st1, None, o1, None.
  split; [reflexivity|].
  split; [apply (r4_monoR WLE' _ _ _ _ _ _ _ _ _ _ 2%nat); [lia | r4_baseR HB2]|].
  split; [r4_rs HR2|].
  split; [exact HSL2|]. split; [exact HRC2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* reading 1 ran out (g_ran_out = 1): reading 2 skipped, no event (r4_revs2_skip), its struct zero (cnb_fo trivial) *)
  split; [exact (cnb_prog_eq D _ _ S (f_equal (app (cnb_cevs D r1 r2 r3))
    (eq_sym (r4_revs2_skip D o1 (r4_ro1_true D o1 HRZ)))) HPG)|]. split; [exact HRZ|].
  split; [exact (r4_mid_nr D ly2 S Hp W2 mem2 Lam peak cnt 1 0 1 2 r1 r2 r3 st1 None None HM2 ltac:(lia))|].
  split; [exact HRES|]. split; [unfold cnb_res; intros E; discriminate E|].
  split; [exact (r4_rds2_skip D o1 st1 (r4_ro1_true D o1 HRZ) HRD)|].
  split; [exact HFO2|].
  (* reading 2 skipped: it pays nothing (rd1 -> rd2) *)
  split; [exact I | exact (r4_hull_rd2 S (bi_x D) HHB)].
Qed.

(* ---- CB6, CNB_READ3 -> CNB_CMP (the ran-out flag set: rc3 = -1 in s7; the budget 4 -> 6 by r4_monoR) or the
   parse_noting call state CNB_PN3 (budget 4); the byte branch 684 -> 736 is refuted (the cut's own 0: r4_mid_own,
   r4_own_byte, r4_byte0_ceq); readings 1 and 2's cnb_fo cross the store and the ran-out call. CNB_READ3 holds after
   a parse_noting: the cut is taken at wle' SEGS RZ_cf (cnb_at_read3R, exits cnb_ex_cmpR / cnb_ex_pn3R), the hand
   steps are the kit's R forms there, and the segment concludes SRr' SEGS RZ_cf ---- *)
Theorem cnb_read3_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_read3R (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2
    o1 o2 ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_READ3) regs mem md)
    (fun W' c' => (cnb_ex_cmpR (fx := fx) B ARx WLE' D W' c' \/ cnb_ex_pn3R (fx := fx) B ARx WLE' D W' c') /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HRC & Nr1 & Nr2 & Nr3 & HPG & HRZ & HM & HRES1 & HRES2 & HRDS & HFO1 & HFO2 & HHB).
pose proof (r4_mid_own D ly S Hp W mem Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None HM) as HOWN.
destruct (r4_entry D HPRE) as (H16 & HS1c & HS1a & HS1b & H47 & HSTK & HRAN & _).
pose proof asan_consts as (C1 & _).
unfold CNB_READ3.
(* 680 lbu a1, 0x140(s8): the g_own_ran_out byte, 0 *)
apply (cnb_hs_lbuR WLE' W fxk regs mem md _ 680 684 11%bv 24%bv 320 (VAL (A_OBJ 13) + 0) (Z_to_bv 8 0));
  [r4_vm | reflexivity | lia | reflexivity | apply r4_own_addr; r4_get HR | exact (r4_own_byte W mem 0 HOWN) |].
intros X1.
(* 684 bnez a1: falls through (the byte branch to 736 refuted) *)
apply (cnb_hs_bnezR WLE' W fxk _ mem _ _ 684 11%bv 52 736 688 true);
  [r4_vm | lia | lia | reflexivity | reflexivity | ro_getr; exact (r4_byte0_ceq _) |].
intros X2. cbv iota.
(* 688 sd a0, 0(s1): rc2 to its slot; rc1's slot (s1 + 8) is kept *)
apply (r4_sd_cut P PLAW D fxk ly S Hp W _ mem _ k 4%nat Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None _ 688 0 rc2 HPRE);
  [r4_baseR HB | exact HSL | exact HM | r4_vm | lia | left; reflexivity
  | ro_getr; r4_get HR | ro_getr; r4_get HR | exact HPM |].
intros X3 mem1 HB1 HSL1 HM1 HFs1 HFs2 _ HRC0 HKO HPM1.
pose proof (HFs1 o1 HFO1) as HFO1m. pose proof (HFs2 o2 HFO2) as HFO2m.
pose proof (HKO 8 rc1 ltac:(right; reflexivity) ltac:(lia) HRC) as HRC8.
(* 692 jal fuzz_alloc_ran_out *)
apply (cnb_hs_callR WLE' W fxk _ mem1 _ _ 692 696 AS_fuzz_alloc_ran_out); [r4_vm | lia | reflexivity |].
intros X4.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (cnb_ro_callR B ARx LAWS IMG HRO WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (wle'_trans SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)
    P PCALL CTX0 D fxk ly S Hp W _ mem1 _ k 4%nat Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None 696 HPRE).
  - unfold cnb_ro_rets. ro_in.
  - r4_baseR HB1.
  - r4_rs HR.
  - ro_getr. reflexivity.
  - exact HSL1.
  - exact HM1.
  - exact HPM1. }
cbv beta. intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & HFc1 & HFc2 & _
  & HKT2 & HPM2).
pose proof (HFc1 o1 HFO1m) as HFO1'. pose proof (HFc2 o2 HFO2m) as HFO2'.
assert (HR2 : cnb_regsat regs2 (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)])).
{ apply (cnb_regsat_pres (regupd (regupd regs 11%bv (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) 1%bv
    (w64 (cnb_pc 696))) regs2); [r4_rs HR | exact HP2 | r4_acsl]. }
assert (G9 : getr regs2 9%bv = w64 (cnb_S1 D)) by r4_get HR2.
pose proof (cnb_rcslot_agree D W mem1 W2 mem2 8 rc1 H16 ltac:(lia) HKT2 HRC8) as HRC8'.
pose proof (cnb_rcslot_agree D W mem1 W2 mem2 0 rc2 H16 ltac:(lia) HKT2 HRC0) as HRC0'.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ (r4_mid_led _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2))
  as (_ & _ & _ & _ & Hran).
revert HRZ. destruct Hran as [Er | Er]; subst ran; intros HRZ.
- (* g_ran_out = 0: 696 beqz a0 taken, the reading *)
  apply (cnb_hs_beqzR WLE' W2 fxk regs2 mem2 md2 _ 696 10%bv 12 708 700 true);
    [r4_vm | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 708 ld a0, 16(s1): r3 *)
  apply (cnb_hs_ldR WLE' W2 fxk regs2 mem2 _ _ 708 712 10%bv 9%bv 16 (cnb_S1 D + 16) r3);
    [r4_vm | reflexivity | lia | reflexivity
    | rewrite G9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSL2 (16, r3) ltac:(ro_in)) |].
  intros X6.
  (* 712 mv a1, s7; 716 mv a2, s4 *)
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 712 716 11%bv 23%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X7.
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 716 720 12%bv 20%bv 0); [r4_vm | reflexivity | lia | reflexivity |].
  intros X8.
  apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [right | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, r1, r2, r3, rc1, rc2, st1, st2, o1, o2.
  split; [reflexivity|].
  split; [r4_baseR HB2|].
  split; [r4_rs HR2|].
  split; [exact HSL2|]. split; [exact HRC8'|]. split; [exact HRC0'|].
  split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* the events: S is kept across the ran-out call; neither reading ran out (g_ran_out = 0) *)
  destruct (r4_ro2_false D o1 o2 HRZ) as (Hro1 & Hro2).
  split; [exact HPG|]. split; [exact Hro1|]. split; [exact Hro2|].
  split; [exact HM2|]. split; [exact HRES1|]. split; [exact HRES2|].
  destruct (r4_rds2_rd D o1 o2 st1 st2 Hro1 HRDS) as (HRD1 & HRD2).
  split; [exact HRD1|]. split; [exact HRD2|]. split; [exact HFO1'|].
  (* the hull stage is still rd2 (S kept across the ran-out call, reading 3 not made yet) *)
  split; [exact HFO2' | exact HHB].
- (* g_ran_out = 1: 696 beqz a0 falls through, the reading is skipped (rc3 = -1 in s7, st3 = None) *)
  apply (cnb_hs_beqzR WLE' W2 fxk regs2 mem2 md2 _ 696 10%bv 12 708 700 false);
    [r4_vm | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 700 li s7, -1; 704 j +24 *)
  apply (cnb_hs_addiR WLE' W2 fxk _ mem2 _ _ 700 704 23%bv 0%bv (-1)); [r4_vm | reflexivity | lia | reflexivity |].
  intros X6.
  apply (cnb_hs_jR WLE' W2 fxk _ mem2 _ _ 704 728 24); [r4_vm | lia | reflexivity | lia |].
  intros X7.
  apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [left | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists.
  exists k2, Lam, peak, cnt, 1, r1, r2, r3, rc1, rc2, (-1), st1, st2, None, o1, o2, None.
  split; [reflexivity|].
  split; [apply (r4_monoR WLE' _ _ _ _ _ _ _ _ _ _ 4%nat); [lia | r4_baseR HB2]|].
  split; [r4_rs HR2|].
  split; [exact HSL2|]. split; [exact HRC8'|]. split; [exact HRC0'|].
  split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* a reading ran out (g_ran_out = 1): reading 3 skipped, no event (r4_revs3_skip), its struct zero (cnb_fo trivial) *)
  split; [exact (cnb_prog_eq D _ _ S (f_equal (app (cnb_cevs D r1 r2 r3)) (eq_sym (r4_revs3_skip D o1 o2 HRZ))) HPG)|].
  split; [exact HRZ|].
  split; [exact (r4_mid_nr D ly2 S Hp W2 mem2 Lam peak cnt 1 0 2 3 r1 r2 r3 st1 st2 None HM2 ltac:(lia))|].
  split; [exact HRES1|]. split; [exact HRES2|]. split; [unfold cnb_res; intros E; discriminate E|].
  split; [exact (r4_rds3_skip D o1 o2 st1 st2 HRZ HRDS)|].
  split; [exact HFO1'|]. split; [exact HFO2'|].
  (* reading 3 skipped: it pays nothing (rd2 -> rd0) *)
  split; [exact I | exact (r4_hull_rd0 S (bi_x D) HHB)].
Qed.

End r4.
