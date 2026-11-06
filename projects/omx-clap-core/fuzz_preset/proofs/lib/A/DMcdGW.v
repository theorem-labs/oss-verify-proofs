(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdGW.v (commit 67deba317dfb, blob c018ca677975) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 6 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgo AFh2 AFfo DMcdGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMcdK DMcdGI FGsN FGtN FGcN AFgz DMcdGWb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Local Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize, kUserMapSize, kFreeArrayMapSize in *.

Lemma val_mem_rebase : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  (forall k, (k < n)%nat -> H' (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
  (forall k, (k < n)%nat -> off_img (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v Hv He Hh Ho k Hk. pose proof (Hv k Hk) as E. unfold mbyte, mrestrict in E |- *.
  rewrite (Hh k Hk), (He k Hk). destruct (H (Z_to_bv 64 (a + Z.of_nat k))).
  - rewrite (seg_rom_none_off _ (Ho k Hk)) in E. discriminate.
  - exact E.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WT.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z).
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Hypothesis FH : free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst.
Local Notation Pv := (DMcdGk.Pv ly off).
Local Notation PCv := (DMcdGk.PCv ly c).
Local Notation MAXv := (DMcdGk.MAXv c).
Local Notation SZv := (DMcdGk.SZv c).
Local Notation Nv := (DMcdGk.Nv c).
Local Notation CNTPv := (DMcdGk.CNTPv c cnt).
Local Notation SLOTv := (DMcdGk.SLOTv ly c cnt).
Local Notation RIv := (DMcdGk.RIv ly).
Local Notation RGv := (DMcdGk.RGv ly c).
Local Notation RBv := (DMcdGk.RBv ly c).
Local Notation FAv := (DMcdGk.FAv ly c).
Local Notation DSTv := (DMcdGk.DSTv ly c old).
Local Notation SRCv := (DMcdGk.SRCv ly c cnt).
Local Notation RELv := (DMcdGk.RELv c off).
Local Notation E0 := (DMcdGk.E0 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation Er := (DMcdGk.Er ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E2 := (DMcdGk.E2 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqT := (DMcdGk.EqT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSB := (DMcdGk.EqSB ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqP := (DMcdGk.EqP ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqC := (DMcdGk.EqC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqPC := (DMcdGk.EqPC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqCNT := (DMcdGk.EqCNT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMAX := (DMcdGk.EqMAX ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSZ := (DMcdGk.EqSZ ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSLOT := (DMcdGk.EqSLOT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRG := (DMcdGk.EqRG ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqOLD := (DMcdGk.EqOLD ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMF := (DMcdGk.EqMF ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ80 := (DMcdGk.EqJ80 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ88 := (DMcdGk.EqJ88 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJST := (DMcdGk.EqJST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRI := (DMcdGk.EqRI ly regs0 c off cnt old mf j80 j88 jst).
Local Notation LYB := (DMcdGk.LYB W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation class_facts := (DMcdGk.class_facts W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation derived_ranges := (DMcdGk.derived_ranges W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINX := (DMcdGk.WINX ly regs0 c cnt).
Local Notation WINY := (DMcdGk.WINY ly regs0 c cnt).
Local Notation DST_notWINX := (DMcdGk.DST_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation SRC_notWINX := (DMcdGk.SRC_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation DST_notWINY := (DMcdGk.DST_notWINY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation off_T := (DMcdGk.off_T W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
Local Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].

Local Ltac meq_acc SKOK :=
match goal with
| M : DMcdGk.MEQX _ _ ?b _ _ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (DMcdGk.MEQX_frame ly regs0 b c cnt E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
| M : DMcdGk.MEQY _ _ _ _ ?m3 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (DMcdGk.MEQY_frame ly regs0 c cnt E _ rs m3 ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Local Ltac reg_zevK HS r tac :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot _ _ _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; tac ].
Local Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Local Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Local Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Local Ltac zevR tac :=
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := eval vm_compute in (2 ^ k) in change (2 ^ k) with cc end; tac ].

Lemma w2_tail : cnt = MAXv -> forall (W3 : world tfibsegs) regs3 mem3 mdx,
  DMcdGWb.w2_pre ly regs0 mem0 c off cnt old mf j80 j88 jst W3 regs3 mem3 ->
  SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 DMcdGWb.A_RTA_RET) mem3 (seg_rom tfibsegs)) mdx)
    (DMcdGI.at_RETKG W ly regs0 mem0 c off cnt old W3 mdx mem3 (mf + kFreeArrayMapSize)).
Proof.
intros HFULL W3 regs3 mem3 mdx PRE.
destruct PRE as (E3 & HEn0 & HS & PdstL0 & PsrcL0 & SRCeq).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (HCP : CNTPv = cnt - Nv) by (unfold DMcdGk.CNTPv; destruct (Z.eqb_spec cnt MAXv); [reflexivity | zlia]).
destruct (Hfull HFULL) as (F1 & F2 & F3 & F4 & Frg & Vmx & Vold & Vmf & V80 & V88 & Psrc & Pold).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R33 : rho_of E0 33%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R34 : rho_of E0 34%nat = Pv) by (unfold rho_of; rewrite EqP; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R35 : rho_of E0 35%nat = c) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - Hc; zlia).
assert (R36 : rho_of E0 36%nat = PCv) by (unfold rho_of; rewrite EqPC; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R37 : rho_of E0 37%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - Hcnt K3; zlia).
assert (R38 : rho_of E0 38%nat = MAXv) by (unfold rho_of; rewrite EqMAX; unfold w64; apply unsigned_lit_small; clear - K3; zlia).
assert (R39 : rho_of E0 39%nat = SZv) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - K1; numconst; zlia).
assert (R40 : rho_of E0 40%nat = SLOTv) by (unfold rho_of; rewrite EqSLOT; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R48 : rho_of E0 48%nat = jst) by (unfold rho_of; rewrite EqJST; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = PCv) by exact R36.
assert (BV40 : bv_unsigned (ew E0 40) = SLOTv) by exact R40.
assert (R41 : rho_of E0 41%nat = RGv) by (unfold rho_of; rewrite EqRG; unfold w64; apply unsigned_lit_small; clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia).
assert (R42 : rho_of E0 42%nat = old) by (unfold rho_of; rewrite EqOLD; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R43 : rho_of E0 43%nat = mf) by (unfold rho_of; rewrite EqMF; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R46 : rho_of E0 46%nat = j80) by (unfold rho_of; rewrite EqJ80; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R47 : rho_of E0 47%nat = j88) by (unfold rho_of; rewrite EqJ88; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R49 : rho_of E0 49%nat = RIv) by (unfold rho_of; rewrite EqRI; unfold w64; apply unsigned_lit_small; clear - dI1 dI3; numconst; zlia).
assert (BV41 : bv_unsigned (ew E0 41) = RGv) by exact R41.

repeat match goal with R : rho_of E0 ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E3 k = v) by (unfold rho_of; rewrite (HEn0 k ltac:(cbv; zlia)); exact R); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E0 ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E0 k) = v -> bv_unsigned (ew E3 k) = v) by (intros HB; rewrite (HEn0 k ltac:(cbv; zlia)); exact HB);
specialize (B' B); clear B; rename B' into B end.

assert (MQ : DMcdGk.MEQX ly regs0 mem3 c cnt mem3) by (intros x _; reflexivity).
pose proof (DMcdGk.WSKX_okX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH E3 HEn0 HFULL) as SKR.

srr_run_to_sh tfibtbl_rtK_ok HS 0x352c8. meq_acc SKR. dbg HS.
assert (USRC : PCv + 16 <= SRCv /\ SRCv + 4 * Nv <= PCv + 80) by (unfold DMcdGk.SRCv, DMcdGk.Nv, DMcdGk.MAXv in *; clear - dC1 dC2 dT1 HFULL K3 K4 K5 K6 Hcnt; numconst; zlia).
assert (UDST : kHighMemBeg <= DSTv /\ DSTv + 4 * Nv <= ASAN_CEIL) by (unfold DMcdGk.DSTv in *; clear - dB0 dB1 dB2 dS1 dS2 dF0 F1 F2 F3 F4 K5; numconst; zlia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msL end.
assert (VSRC : getr (ms_regs msL) 22 = Z_to_bv 64 SRCv).
{ reg_zevK HS (22%bv : bv 5) ltac:(unfold DMcdGk.SRCv, DMcdGk.Nv, DMcdGk.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
assert (VDST : getr (ms_regs msL) 25 = Z_to_bv 64 DSTv).
{ reg_zevK HS (25%bv : bv 5) ltac:(unfold DMcdGk.DSTv, DMcdGk.FAv, DMcdGk.RBv in *; rewrite ?K8 in *; clear - dB0 dB1 dB2 dS1 dS2 F1 F2 F3 F4 K5 K7 K9 Hc; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
assert (VEND : getr (ms_regs msL) 10 = Z_to_bv 64 (SRCv + 4 * Nv)).
{ reg_zevK HS (10%bv : bv 5) ltac:(unfold DMcdGk.SRCv, DMcdGk.Nv, DMcdGk.MAXv in *; clear - dC1 dC2 dT1 dT2 HFULL K3 K4 K5 K6 Hcnt; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
idtac "CURSORS-OK".
assert (PdstL : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W3) (ms_mem msL) a).
{ intros a Ha. destruct (PdstL0 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
rewrite unsigned_lit_small by (clear - Ha UDST; numconst; zlia). exact (DST_notWINX HFULL a Ha). }
assert (PsrcL : forall a, SRCv <= a < SRCv + 4 * Nv -> apresent (w_H W3) (ms_mem msL) a).
{ intros a Ha. destruct (PsrcL0 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
rewrite unsigned_lit_small by (clear - Ha USRC dC1 dT1 dC2 dT2; numconst; zlia). exact (SRC_notWINX HFULL a Ha). }
assert (DISJ : DSTv + 4 * Nv <= SRCv \/ SRCv + 4 * Nv <= DSTv).
{ unfold DMcdGk.DSTv in *. clear - USRC dC1 dC2 dT2 dB0 dB1 dB2 dF0 dS1 dS2 F1 F2 F3 F4 LB K5. numconst. zlia. }
eapply (cpyk_stretch W3 70%nat E3 _ msL _ DSTv SRCv (4 * Nv));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| exact VSRC | exact VDST | exact VEND
| clear - K5; zlia | clear - K5; rewrite Z.mul_comm; apply Z_mod_mult
| clear - UDST; numconst; zlia | clear - UDST K5; numconst; zlia
| clear - USRC dC1 dT1; numconst; zlia | clear - USRC dC2 dT2 K5; numconst; zlia
| exact DISJ
| exact PdstL | exact PsrcL
| intros r Hr | intros r a Hr | ].
1-2: cbn [ss_mem In] in Hr;
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2, ?BV32, ?BV36, ?BV41;
unfold DMcdGk.DSTv in *; clear - UDST USRC DR LB K5 F1 F2 F3 F4 Hlo Hhi Usp; numconst; zlia.
all: idtac "SIDE-LEFT".
intros regs3' mem3' mat3 HS3 Hfr3 Hpr3 Hcp3. rewrite wvb_collapse.
lazymatch type of HS3 with st_ok _ ?e ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS3; set (E' := e) in HS3 end.
clear HS. rename HS3 into HS.
assert (HEn : forall k, (k < aHAVf)%nat -> ew E' k = ew E0 k) by (intros k Hk; subst E'; rewrite ew_havoc_old by (unfold aHAVf in Hk; zlia); apply HEn0; exact Hk).
pose proof (DMcdGk.MEQY_0 ly regs0 c cnt mem3') as MQ3. rename MQ into MQX. rename MQ3 into MQ.
pose proof (DMcdGk.WSKR_okY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH E' HEn HFULL) as SKR'.
repeat match goal with R : rho_of E3 ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E' k = v) by (unfold rho_of; rewrite (HEn k ltac:(cbv; zlia)); rewrite <- (HEn0 k ltac:(cbv; zlia)); exact R); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E3 ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E' k) = v) by (rewrite (HEn k ltac:(cbv; zlia)); rewrite <- (HEn0 k ltac:(cbv; zlia)); exact B); clear B; rename B' into B end.
apply (st_ok_add_region _ _ _ DMcdGk.R_SLOT) in HS;
[ | reflexivity
| unfold DMcdGk.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite BV40;
split; [clear - DR; numconst; zlia|]; split; [clear - DR; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - DR Ho; numconst; zlia) | apply Hpr3; apply PsrcL; unfold DMcdGk.SLOTv, DMcdGk.SRCv in *; rewrite HCP in *; clear - Ho K5; zlia] | apply Forall_nil]
| unfold DMcdGk.R_SLOT; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x355f4. meq_acc SKR'. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
assert (QSP : getr (ms_regs msC) 2 = Z_to_bv 64 (sp0 - 240)).
{ let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 2%nat ltac:(cbv; zlia)), E2. first [reflexivity | f_equal; zlia]. }
assert (USP : bv_unsigned (getr (ms_regs msC) 2) = sp0 - 240) by (rewrite QSP; apply unsigned_lit_small; clear - Usp dK1; numconst; zlia).

assert (PRESC : forall a, sp0 - 320 <= a < sp0 - 240 -> apresent (w_H W3) (ms_mem msC) a).
{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W3) E' _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Usp dK1; numconst; zlia) ]. }
assert (J80 : 0 <= (j80 + Nv) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; zlia).
assert (FHO : AFgo.free_hyps W3 (ms_regs msC) (ms_mem msC) RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88).
{ apply FHO_ok.
- let Q := fresh "Q" in rreg HS (1%bv : bv 5) Q; rewrite Q. unfold YK0s.ret_ok. reflexivity.
- rewrite USP. clear - Hlo Hhi LB; numconst; zlia.
- rewrite USP. clear - Hsp_al. replace (sp0 - 240) with (sp0 + (-15) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite USP. intros a Ha. apply PRESC. clear - Ha. zlia.
- exact Hc.
- clear - dI1 dI2 dI3 dSal. split; [exact dI1|]. split; [exact dI3|]. rewrite dI2. numconst.
apply Z.mod_divide in dSal as [q Hq]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * 16 + 2 ^ 25). zlia.
- clear - F1 F2 F3 F4 K5 dJ3 dJ4 J80. numconst. zlia.
- rewrite USP. change (RIv + 128 * c) with RGv. clear - LB Hlo Hhi dG0 dG1 dG2 dI1 dI2 dI3 dS1 dS2. numconst. zlia.
- let Q := fresh "Q" in rreg HS (10%bv : bv 5) Q; rewrite Q. reflexivity.
- let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q. cbn [sv_denot]. rewrite (HEn 35%nat ltac:(cbv; zlia)), EqC. first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]].
- let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q. reflexivity.
- change (RIv + 128 * c) with RGv. memvo HS 2%nat 16; [ rewrite BV41; zlia
| apply denot_by_zev; [ reflexivity | clear - F1 F2 F3 F4 K5; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold DMcdGk.Nv, DMcdGk.MAXv in *;
clear - F1 F2 F3 F4 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| clear - F1 F2 F3 F4 K5; numconst; zlia ].
- change (RIv + 128 * c) with RGv. memvo HS 3%nat 80; [ rewrite BV41; zlia
| apply denot_by_zev; [ reflexivity | exact J80
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; unfold DMcdGk.Nv, DMcdGk.MAXv in *;
clear - K3 K4 K5 K6 dJ1 dJ2; numconst; zcanon_simp; unfold zcanon, M64; zlia ]
| exact J80 ].
- change (RIv + 128 * c) with RGv. memvo HS 3%nat 88; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite (HEn 47%nat ltac:(cbv; zlia)), EqJ88; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | exact (conj dJ3 dJ4) ].
- memvo HS 9%nat (A_ALLOCATOR + 48); [ reflexivity | cbn [sv_denot]; rewrite (HEn 49%nat ltac:(cbv; zlia)), EqRI; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - dI1 dI3; numconst; zlia ].
- memvo HS 10%nat (A_ALLOCATOR + 40); [ reflexivity | reflexivity | zlia ].
- memvo HS 11%nat 0xa1ff0; [ reflexivity | reflexivity | zlia ].
- memvo HS 12%nat 0x13a960; [ reflexivity | reflexivity | zlia ]. }
idtac "FHO-OK".
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mat _)) _ => pose proof (segO W3 ly (ms_regs msC) (ms_mem msC) mdx RIv c (old + Nv) ((j80 + Nv) mod 2 ^ 64) j88 mat FHO) as SEGO end.
rewrite Hshape. rewrite Hshape in HS.
lazymatch type of HS with st_ok _ _ ?ss _ =>
let rs := eval vm_compute in (match ss_mem ss with r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest => r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: rest | l => l end) in
eapply (call_stretch W3 73%nat E' ss _ _ mdx rs 0x35300 (AFgo.WIN (ms_regs msC)) _ HS);
[ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| do 6 (apply submem_keep; [apply subregion_refl|]); apply submem_drop; apply submem_refl
| reflexivity | zlia
| intros r a Hr Ha | intros r Hr | exact SEGO | ] end.
{ unfold AFgo.WIN. rewrite USP. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?BV2, ?BV32, ?BV36, ?BV40, ?BV41 in Ha;
clear - Ha DR LB K5 F1 F2 F3 Hlo Hhi Usp; numconst; zlia. }
{ cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn; zlia. }
idtac "CALL-OK".
clear SEGO. intros regs4 mem4 mat4 HS4 HP4 Hfr4 Hpr4.
lazymatch type of HS4 with st_ok _ ?e ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS4; set (E'' := e) in HS4 end.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew E'' k = ew E0 k) by (intros k Hk; subst E''; rewrite ew_havoc_old by (unfold aHAVf in Hk; zlia); apply HEn; exact Hk).
clear HS Hshape. rename HS4 into HS.
repeat match goal with R : rho_of E' ?k = ?v |- _ =>
let R' := fresh R in assert (R' : rho_of E'' k = v) by (unfold rho_of; rewrite (HEn4 k ltac:(cbv; zlia)); rewrite <- (HEn k ltac:(cbv; zlia)); exact R); clear R; rename R' into R end.
repeat match goal with B : bv_unsigned (ew E' ?k) = ?v |- _ =>
let B' := fresh B in assert (B' : bv_unsigned (ew E'' k) = v) by (rewrite (HEn4 k ltac:(cbv; zlia)); rewrite <- (HEn k ltac:(cbv; zlia)); exact B); clear B; rename B' into B end.
unfold AFgo.WIN in Hfr4, Hpr4. rewrite USP in Hfr4, Hpr4. cbn [ms_mem ms_regs mkst] in Hfr4, Hpr4, HP4.
assert (MQ4 : DMcdGk.MEQY ly regs0 c cnt mem3' mem4).
{ intros x Hx. rewrite (Hfr4 x) by (intros HD; apply Hx; left; clear - HD; zlia). exact (MQ x Hx). }
clear MQ. rename MQ4 into MQ.
pose proof (DMcdGk.WSKR_okY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH E'' HEn4 HFULL) as SKR4.
apply (st_ok_add_region _ _ _ DMcdGk.R_STK_LO) in HS;
[ | reflexivity
| unfold DMcdGk.R_STK_LO, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite BV2;
split; [clear - Usp dK1; numconst; zlia|]; split; [clear - Usp dK1 dK2; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp dK1 Ho; numconst; zlia) | apply Hpr4; clear - Ho; zlia] | apply Forall_nil]
| unfold DMcdGk.R_STK_LO; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV40, ?BV41, ?BV2;
clear - LB DR Hlo Hhi Usp; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
idtac "READD-OK".
srr_run_to_sh tfibtbl_rtK_ok HS 0x34c88. meq_acc SKR4. dbg HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 40%nat (-16))) in HS;
[ | intros Hx; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := eval vm_compute in (2 ^ k) in change (2 ^ k) with cc end;
unfold DMcdGk.SLOTv, DMcdGk.Nv, DMcdGk.MAXv in *; rewrite HCP; clear - dC1 dC2 dT1 dT2 Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
idtac "PIN2-OK".
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtK tfibtbl_rtK_ok Hwx W3 E''); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. unfold DMcdGI.at_RETKG. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (Er4 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E'' k = getr regs0 r).
{ intros k r Hk. rewrite (HEn4 k) by (pose proof (u5_range r); unfold aHAVf; zlia). exact (Er k r Hk). }
let Q1 := fresh "Q1" in rreg HS (1%bv : bv 5) Q1; rewrite (Er4 1%nat 1%bv eq_refl) in Q1;
split; [ rewrite Q1; unfold YK0s.ret_ok in Hra; rewrite Hra; rewrite ?wvb_collapse; reflexivity |].
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q. apply Er4. reflexivity. }
split. { intros r Hr. cbn [DMcdGk.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let RR := fresh "RR" in rreg HS r RR; rewrite RR end;
first [ apply Er4; reflexivity | rewrite Htp; reflexivity ]). }
assert (DPRES : forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W3) mem3' a) by (intros a Ha; apply Hpr3; apply PdstL; exact Ha).
split.
{
  intros x Hx. unfold DMcdGI.WING in Hx.
  rewrite (MQ x) by (intros HY; apply Hx; unfold DMcdGk.WINY, DMcdGk.WINF, DMcdGk.WRG in HY; unfold DMcdGk.Nv, DMcdGk.MAXv in *; tauto).
  rewrite (Hfr3 x) by (intros HD; apply Hx; unfold DMcdGk.Nv, DMcdGk.MAXv in *; tauto).
  apply MQX. intros HX. apply Hx. unfold DMcdGk.WINX, DMcdGk.WRG in HX. unfold DMcdGk.Nv, DMcdGk.MAXv in *; tauto. }
split.
{
  intros a Ha. unfold DMcdGI.WING in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
  - destruct (Z_lt_le_dec a (sp0 - 240)).
    + eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
    + eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 7 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV36; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV40; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - eapply (st_ok_window_apresent_off (w_H W3) E'' _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
  - change (max_cached c / 2) with Nv in Ha.
    destruct (DPRES a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MQ.
    rewrite unsigned_lit_small by (clear - Ha UDST; numconst; zlia). exact (DST_notWINY HFULL a Ha). }
cbv zeta.
split. { idtac "F1". memvo HS 5%nat 0; [ rewrite BV36; zlia
| zevR ltac:(unfold DMcdGk.CNTPv, DMcdGk.Nv, DMcdGk.MAXv in *; rewrite ?HCP; clear - Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; try zlia)
| rewrite HCP; clear - Hcnt HFULL K3 K5 K6; zlia ]. }
split. { idtac "F2". memvo HS 1%nat 0; [ rewrite BV40; zlia
| zevR ltac:(unfold DMcdGk.Pv, DMcdGk.RELv in *; rewrite ?K8 in *; clear - O1 O2 K1 K7 K9 dS1 dS2 Hc;
first [ split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia]
| numconst; zcanon_simp; unfold zcanon, M64; replace (-1 mod 2 ^ 64) with 18446744073709551615 by reflexivity; zlia ])
| unfold DMcdGk.RELv in *; clear - O1 O2 K1; split; [apply Z.div_pos; zlia | apply Z.div_lt_upper_bound; [zlia|]; numconst; zlia] ]. }
split. { idtac "F3". memvo HS 2%nat 0; [ rewrite BV41; zlia | reflexivity | zlia ]. }
split. { idtac "F4". memvo HS 3%nat 16; [ rewrite BV41; zlia
| zevR ltac:(unfold DMcdGk.Nv, DMcdGk.MAXv in *; clear - F1 F2 F3 F4 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia)
| clear - F1 F2 F3 F4 K5; unfold DMcdGk.Nv, DMcdGk.MAXv in *; numconst; zlia ]. }
split. { idtac "F5". memvo HS 3%nat 24; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite (HEn4 43%nat ltac:(cbv; zlia)), EqMF; unfold w64; rewrite Zbv_add_unsigned; reflexivity | clear - F1 F2 F3 K5; numconst; zlia ]. }
idtac "F6".
intros i v Hi Hv. change (max_cached c / 2) with Nv in Hi.
assert (HvS : val_mem tfibsegs (mrestrict (w_H W3) mem3) (SRCv + 4 * i) 4 v).
{ apply (val_mem_rebase (w_H W) (w_H W3) mem0 mem3 _ 4 v Hv).
  - intros k Hk. apply SRCeq. rewrite unsigned_lit_small by (clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5; numconst; zlia). clear - Hi Hk; zlia.
  - intros k Hk. exact (proj1 (PsrcL0 (SRCv + 4 * i + Z.of_nat k) ltac:(clear - Hi Hk; zlia))).
  - intros k Hk. apply off_T. clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5. numconst. zlia. }
apply (AFgz.val_mem_move (w_H W3) mem3 (ms_mem msR) (SRCv + 4 * i) (DSTv + 4 * i) 4 v); try exact HvS.
- intros k Hk. rewrite (MQ _) by (rewrite unsigned_lit_small by (clear - Hi Hk UDST K5; numconst; zlia); apply (DST_notWINY HFULL); clear - Hi Hk; zlia).
replace (DSTv + 4 * i + Z.of_nat k) with (DSTv + (4 * i + Z.of_nat k)) by zlia. unfold YG0n.w64, w64 in Hcp3. rewrite (Hcp3 (4 * i + Z.of_nat k)) by (clear - Hi Hk; zlia).
replace (SRCv + (4 * i + Z.of_nat k)) with (SRCv + 4 * i + Z.of_nat k) by zlia.
apply MQX. rewrite unsigned_lit_small by (clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5; numconst; zlia). apply (SRC_notWINX HFULL). clear - Hi Hk; zlia.
- intros k Hk. exact (proj1 (DPRES (DSTv + 4 * i + Z.of_nat k) ltac:(clear - Hi Hk; zlia))).
- intros k Hk. exact (proj1 (PsrcL0 (SRCv + 4 * i + Z.of_nat k) ltac:(clear - Hi Hk; zlia))).
- intros k Hk. apply off_T. clear - Hi Hk USRC dC1 dC2 dT1 dT2 K5. numconst. zlia.
- clear - Hi USRC dC2 dT2 K5. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. numconst. zlia.
Qed.
End WT.

Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z) (X : astate).

Theorem w2 : DMcdGI.w2_t W ly regs0 mem0 md0 c off cnt old mf j80 j88 jst X.
Proof.
unfold DMcdGI.w2_t. intros FH HFULL HX HGROW HLEN c9 HEFA regs9 mem9 md9 Hc9 r W' c' HLEAF.
destruct (DMcdGWb.w2_bridge W ly regs0 mem0 md0 c off cnt old mf j80 j88 jst X FH HFULL HX HGROW c9 HEFA regs9 mem9 md9 Hc9 r W' c' HLEAF)
  as (Hsnd & regs3 & mem3 & mdx & Hc' & PRE).
subst c'. cbn [cfg_model cfg_ms ms_mem mkst].
assert (MF2 : rg_mapped_fa (reg (snd r) c) = mf + kFreeArrayMapSize).
{ rewrite Hsnd.
  rewrite reg_upd_reg; [ unfold FGcN.rgG; cbn [rg_mapped_fa]; rewrite HX; reflexivity
  | pose proof (DMcdGk.fh_Hc _ _ _ _ _ _ _ _ _ _ _ _ FH); lia | exact HLEN ]. }
rewrite MF2.
exact (w2_tail W ly regs0 mem0 c off cnt old mf j80 j88 jst FH HFULL W' regs3 mem3 mdx PRE).
Qed.
End g.
End d.
