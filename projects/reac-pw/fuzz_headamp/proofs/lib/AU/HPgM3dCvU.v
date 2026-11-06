(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dFlt.v at 0312b0cd6c6c; hvl_core_step,
   hvl_hc_core, hvl_mid with its run / float-step / call transports, hvl_at_kept, hvl_base_at, the cut builders,
   hvl_soff, hvl_ge3 / hvl_le3 and hvl_half_words restated for image B over lib/AU/HPgSeg.v / HPgSegM.v and
   lib/AU/HPgM3dBaseU.v's cut CV (the write zone is [R - T_SEG_STK, R) and [R+0x88, R+0x90), s2 and s8 are not
   kept, no float register is written); the six block lemmas of image B's step from cut CV and its chain are new. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the step from cut CV of the
   piece value of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgM3dBaseU.v hvu_piece_cv_stmt
   (CV 0x83608 -> TAIL 0x83694 / RF 0x836a0). Proves no function (kind: segment lemma).

   THE CODE (pod_nearest pod.h:152-171 inlined: the rounding of t = trunc(f) and the range test against 255)
     0x83608  fcvt.l.s s2,fs0,rtz        t := trunc(b)                       (HPgM3dFpU.v hvfu_fcvt)
     0x8360c  mv a0,s2; jal __floatditf  ra 0x83614                          (block hvc_c1)
     0x83614  a2:a3 := a0:a1; a0 := s8; a1 := R+0x88; jal __subtf3, ra 0x83628   (block hvc_c2)
     0x83628  s8 := a0; sd a1,0x88(s1); a2 := 0; a3 := R+0xa8 (0.5L); jal __getf2, ra 0x8363c (block hvc_c3)
     0x8363c  bgez a0 -> 0x83674 (t + 1, `blt` 0x83678 to `unimp` not taken), else a0:a1 := s8:R+0x88,
              a2:a3 := 0:R+0xa0 (-0.5L), jal __lttf2, ra 0x83654               (block hvc_c4)
     0x83654  bgez a0 -> 0x83680 (r = t), else t - 1 (`bge` 0x8365c to `unimp` not taken)   (block hvc_c5)
     0x83680  t5 := R+0x110, t6 := R+0x108, a0 := 255, a5 := 5, bltu a0,s2 -> RF 0x836a0, else TAIL 0x83694
                                                                               (block hvc_c6)
   The registers this lane reads or writes: s1 = R, s2 (t, then r), s8 (the low word of d, then of frac), s5 / s7
   (kept), a0 .. a3, a5, ra, t5, t6; the real-frame cells R+0x88 (the high word of d, then of frac), R+0x90 (the
   param), R+0xa0 / R+0xa8 (-0.5L / 0.5L high words), R+0x108 / R+0x110 (t6 / t5).

   HOW. Each block is a lemma over the machine state at its first pc (the registers as atoms, the read cells as a
   region over s1), run by the kit's engine with the token base HPgSteps.RTBx and no shadow entry (no instrumented
   check in this lane). The cut CV is carried to every state of the lane by hvc_mid (the journal-and-frame part,
   every byte outside [R - T_SEG_STK, R) and R+0x88 .. R+0x90 as at CV, the callee-saved registers but s2 / s8, every
   float register and a zero rounding mode), across each block (hvc_mid_run), the float step (hvc_mid_fp) and each
   soft-float call (hvc_mid_call; lib/AU/HPgCallsSFIU.v hsfu_fd_stmt / hsfu_sub_stmt / hsfu_ge_stmt /
   hsfu_lt_stmt). The two UBSan traps are not taken: t lies in [-2^31 - 1, 2^31] (hvc_t_rng, the third clause of
   lib/U/Prog/HeadCheck/Near.v hn_traps, proved here from lib/Prog/HeadCheck/NearVal.v's lemmas), so neither
   overflow test is taken (hvc_lt_inc / hvc_ge_dec, Near.v's lts_inc / lts_dec in the engine's branch form; Near.v
   is not Required: it loads lib/U's own Reusable modules, whose names shadow lib/Reusable's). The exit is RF
   exactly when 255 < r mod 2^64, i.e. NearVal.hn_bin b =
   None (lib/A/HPgM3dVal.v hvm_hn_body), and then cell_value v = -1; else TAIL with val = r mod 2^64.

   SECTION HYPOTHESES of hvu_cv_B: MTL : ameter_laws MT (the meter's order across a call, as HPgCallsSFIU's) and
   ERR : api_env rsegs B (lib/Reusable/YCbq.v: the errno cell lies in the image, below kLowMemEnd, so __subtf3's
   frame below R misses it). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0c YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require NearVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgM3dVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgM3dBaseU HPgM3dSFU HPgM3dFpU HPgM3dDispU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgCallsSFIU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== registers and float registers ===================================== *)
(* the registers every state of the lane keeps from the cut CV: the callee-saved ones but s2 (x18) and s8 (x24) *)
Definition HVC_KR : list Z := [8; 9; 19; 20; 21; 22; 23; 25; 26; 27].
(* the same with sp, gp and tp, as the engine's register list *)
Definition HVC_KRB : list (bv 5) := map (Z_to_bv 5) (2 :: 3 :: 4 :: HVC_KR).

Lemma hvc_krb : forall q, In q (2 :: 3 :: 4 :: HVC_KR) -> In (Z_to_bv 5 q) HVC_KRB.
Proof. intros q Hq. unfold HVC_KRB. apply in_map. exact Hq. Qed.

Lemma hvc_incl : forall (l1 l2 : list (bv 5)),
forallb (fun rr => existsb (fun c => bv_eqb c rr) l2) l1 = true -> forall rr, In rr l1 -> In rr l2.
Proof.
intros l1 l2 H rr Hr. pose proof (proj1 (forallb_forall _ _) H rr Hr) as H1.
apply existsb_exists in H1 as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact Hc.
Qed.

(* a block's kept registers include HVC_KRB *)
Lemma hvc_kept_of : forall (kept : list (bv 5)) (regs regs' : bvmap 5 word),
(forall rr, In rr kept -> getr regs' rr = getr regs rr) ->
forallb (fun rr => existsb (fun c => bv_eqb c rr) kept) HVC_KRB = true ->
forall rr, In rr HVC_KRB -> getr regs' rr = getr regs rr.
Proof. intros kept regs regs' Hk Hb rr Hr. apply Hk. exact (hvc_incl _ _ Hb rr Hr). Qed.

(* the kept registers of the six blocks *)
Definition hvc_k1 : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvc_k2 : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Definition hvc_k3 : list (bv 5) :=
map (Z_to_bv 5) [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30;
  31].
Definition hvc_k4a : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvc_k6 : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29].

Lemma hvc_fxk_trans : forall f1 f2 f3 : YK11.FPState, hd_fxk [] f1 f2 -> hd_fxk [] f2 f3 -> hd_fxk [] f1 f3.
Proof. intros f1 f2 f3 (H1 & _) (H2 & Hz). split; [|exact Hz]. intros k Hk. rewrite (H2 k Hk). exact (H1 k Hk). Qed.

(* ===================================== the value language ===================================== *)
Lemma hvc_soff : forall E n z c, ew E n = Z_to_bv 64 z -> sv_denot E (SOff n c) = Z_to_bv 64 (z + c).
Proof.
intros E n z c H. cbn [sv_denot]. rewrite H.
rewrite <- (HPgSteps.Z_to_bv_mod64 (bv_unsigned (Z_to_bv 64 z) + c)), <- (HPgSteps.Z_to_bv_mod64 (z + c)).
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.

(* the two UBSan overflow tests on t + 1 (`blt a0,s2`, 0x83678) and t - 1 (`bge a0,s2`, 0x8365c) are not taken
   when -2^31 - 1 <= t <= 2^31 (lib/U/Prog/HeadCheck/Near.v lts_inc / lts_dec, in the branch form) *)
Lemma hvc_lt_inc : forall t, - 2 ^ 31 - 1 <= bv_swrap 64 t <= 2 ^ 31 ->
branch_taken BC_LT (Z_to_bv 64 (t + 1)) (Z_to_bv 64 t) = false.
Proof.
intros t Ht. rewrite YO0c.branch_lt, !YO0c.lit64_unsigned. unfold YO0b.s64.
unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2 ^ 63) in Ht.
change (bv_modulus 64) with (2 ^ 64) in Ht.
apply Z.ltb_ge.
destruct (Z.ltb_spec ((t + 1) mod 2 ^ 64) (2 ^ 63)); destruct (Z.ltb_spec (t mod 2 ^ 64) (2 ^ 63)); cbv iota;
  revert Ht; Z.div_mod_to_equations; lia.
Qed.
Lemma hvc_ge_dec : forall t, - 2 ^ 31 - 1 <= bv_swrap 64 t <= 2 ^ 31 ->
branch_taken BC_GE (Z_to_bv 64 (t + -1)) (Z_to_bv 64 t) = false.
Proof.
intros t Ht. rewrite YO0c.branch_ge, !YO0c.lit64_unsigned. unfold YO0b.s64.
unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2 ^ 63) in Ht.
change (bv_modulus 64) with (2 ^ 64) in Ht.
apply negb_false_iff, Z.ltb_lt.
destruct (Z.ltb_spec ((t + -1) mod 2 ^ 64) (2 ^ 63)); destruct (Z.ltb_spec (t mod 2 ^ 64) (2 ^ 63)); cbv iota;
  revert Ht; Z.div_mod_to_equations; lia.
Qed.

(* t = trunc(b) lies in [-2^31 - 1, 2^31] once the NaN test and the range test -1.0f <= b <= 256.0f have passed
   (the third clause of lib/U/Prog/HeadCheck/Near.v hn_traps, from lib/Prog/HeadCheck/NearVal.v's lemmas) *)
Lemma hvc_t_rng : forall b, 0 <= b < 2 ^ 32 ->
fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 b) = false ->
- 2 ^ 31 - 1 <= bv_swrap 64 (NearVal.pn_t b) <= 2 ^ 31.
Proof.
intros b Hb Heq Hl1 Hl2.
destruct (Nearest.f32_ratio b) as [[N D]|] eqn:HR.
- rewrite (NearVal.flt_m1 b N D HR) in Hl1. rewrite (NearVal.flt_256 b N D HR) in Hl2.
  apply Z.ltb_ge in Hl1. apply Z.ltb_ge in Hl2.
  pose proof (proj2 (Nearest.near_f32_ratio b) N D HR) as HD.
  assert (HB : (Nearest.INT32_MIN - 1) * D <= N <= (Nearest.INT32_MAX + 1) * D)
    by (unfold Nearest.INT32_MIN, Nearest.INT32_MAX; lia).
  rewrite (NearVal.toint_ratio b N D HR HB). pose proof (NearVal.quot_rng N D HD HB) as Hq.
  rewrite NearVal.swrap_iw0 by lia. exact Hq.
- exfalso. destruct (NearVal.ratio_none b HR) as [Hd|[Hd|Hd]].
  + rewrite (NearVal.feq_nan b Hd) in Heq. discriminate Heq.
  + rewrite (NearVal.flt_minf_m1 b Hd) in Hl1. discriminate Hl1.
  + rewrite (NearVal.flt_pinf_256 b Hd) in Hl2. discriminate Hl2.
Qed.

(* `bgez a0` on a comparison result *)
Lemma hvc_bge0 : forall g, -1 <= g <= 1 -> branch_taken BC_GE (Z_to_bv 64 g) (Z_to_bv 64 0) = (0 <=? g).
Proof. intros g Hg. assert (E : g = -1 \/ g = 0 \/ g = 1) by lia. destruct E as [-> | [-> | ->]]; vm_compute; reflexivity. Qed.

Lemma hvc_ge3 : forall a c, SF.f128_ge a c = -1 \/ SF.f128_ge a c = 0 \/ SF.f128_ge a c = 1.
Proof.
intros a c. unfold SF.f128_ge, SoftFloat.nez64, SoftFloat.b2z. cbv zeta.
repeat match goal with |- context [if ?x then _ else _] => destruct x end; auto.
Qed.
Lemma hvc_le3 : forall a c, SF.f128_le a c = -1 \/ SF.f128_le a c = 0 \/ SF.f128_le a c = 1.
Proof.
intros a c. unfold SF.f128_le, SoftFloat.nez64, SoftFloat.b2z. cbv zeta.
repeat match goal with |- context [if ?x then _ else _] => destruct x end; auto.
Qed.

Lemma hvc_half_words : 0 + 2 ^ 64 * HQU_HALF_HI = NearSF.HALF_128 /\ 0 + 2 ^ 64 * HQU_MHALF_HI = NearSF.MHALF_128.
Proof.
destruct hvm_half_rng as (Hr1 & Hr2 & L1 & L2 & H1 & H2).
split.
- rewrite <- (hvm_w128 _ Hr1), L1, H1. reflexivity.
- rewrite <- (hvm_w128 _ Hr2), L2, H2. reflexivity.
Qed.

(* ===================================== the six blocks ===================================== *)
Section bl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* ---------------- c1 0x8360c -> __floatditf: `mv a0,s2; jal` ---------------- *)
Definition hvc_ss1 : sstate := mkSS 0x8360c sr_atoms [] None (mkFacts [] [] []).

Lemma hvc_c1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (t : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 18) = Z_to_bv 64 t ->
SRr rsegs W (cfg_at rsegs 0x8360c regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_FD hvc_k1
  (fun regs2 => getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 t /\ getr regs2 (Z_to_bv 5 1) = Z_to_bv 64 HVU_RA_FD)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t HJ H18.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 t)
  by (rewrite (ew_Ereg_nat regs ex 18 (Z_to_bv 5 18) eq_refl); exact H18).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8360c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss1. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 0x8360c) with (Z_to_bv 64 0x8360c).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvc_k1. cbv beta.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split.
- hvu_sv. rewrite hvu_denot0. exact E18.
- hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ---------------- c2 0x83614 -> __subtf3: `mv a2,a0; mv a3,a1; mv a0,s8; ld a1,0x88(s1); jal` ---------------- *)
Definition hvc_R2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0x90 0 0 [YP09.mkChunk 0x88 (CVal 8 (SOff 33 0))].
Definition hvc_ss2 : sstate := mkSS HVU_RA_FD sr_atoms [hvc_R2] None (mkFacts [] [] []).
Definition hvc_x1 (w : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 w].
Definition hvc_x2 (w w' : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 w; Z_to_bv 64 w'].

Lemma hvc_c2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R dlo dhi flo fhi : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = Z_to_bv 64 R -> getr regs (Z_to_bv 5 10) = Z_to_bv 64 flo ->
getr regs (Z_to_bv 5 11) = Z_to_bv 64 fhi -> getr regs (Z_to_bv 5 24) = Z_to_bv 64 dlo ->
0 <= R -> R + 0x90 <= 2 ^ 64 -> 0 <= dhi < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x88) 8 dhi ->
SRr rsegs W (cfg_at rsegs HVU_RA_FD regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_SUB hvc_k2
  (fun regs2 => getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 dlo /\ getr regs2 (Z_to_bv 5 11) = Z_to_bv 64 dhi /\
     getr regs2 (Z_to_bv 5 12) = Z_to_bv 64 flo /\ getr regs2 (Z_to_bv 5 13) = Z_to_bv 64 fhi /\
     getr regs2 (Z_to_bv 5 1) = Z_to_bv 64 HVU_RA_SUB)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R dlo dhi flo fhi HJ H9 H10 H11 H24
  HR0 HR1 Hd V88.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvc_x1 dhi) as ex eqn:Hex.
assert (EA : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs ex) n = getr regs rr)
  by (intros n rr Hn; exact (ew_Ereg_nat regs _ n rr Hn)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 flo) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 fhi) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 dlo) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 dhi) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_RA_FD) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss2. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0x88 dhi 33 E33 ltac:(rewrite Z.mod_small by lia; exact V88)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_RA_FD) with (Z_to_bv 64 HVU_RA_FD).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvc_k2. cbv beta.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [hvu_sv; rewrite hvu_denot0; exact E24|].
split; [hvu_sv; rewrite hvu_denot0; exact E33|].
split; [hvu_sv; rewrite hvu_denot0; exact E10|].
split; [hvu_sv; rewrite hvu_denot0; exact E11|].
hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ---------------- c3 0x83628 -> __getf2: `mv s8,a0; sd a1,0x88(s1); li a2,0; ld a3,0xa8(s1); jal` ----------------
   the one store of the lane: R+0x88 := a1, inside the journal's stack window *)
Definition hvc_R3 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0xb0 0x88 0x90 [YP09.mkChunk 0xa8 (CVal 8 (SOff 33 0))].
Definition hvc_f9 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition hvc_ss3 : sstate := mkSS HVU_RA_SUB sr_atoms [hvc_R3] None hvc_f9.

Lemma hvc_c3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R slo shi : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = Z_to_bv 64 R -> getr regs (Z_to_bv 5 10) = Z_to_bv 64 slo ->
getr regs (Z_to_bv 5 11) = Z_to_bv 64 shi ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> sp0 - STK <= R + 0x88 -> R + 0x90 <= sp0 ->
0 <= slo < 2 ^ 64 -> 0 <= shi < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 HQU_HALF_HI ->
SRr rsegs W (cfg_at rsegs HVU_RA_SUB regs memc mdc)
(hvu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_GE hvc_k3
  (fun a => R + 0x88 <= a < R + 0x90)
  (fun regs2 mem2 => getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 slo /\ getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 slo /\
     getr regs2 (Z_to_bv 5 11) = Z_to_bv 64 shi /\ getr regs2 (Z_to_bv 5 12) = Z_to_bv 64 0 /\
     getr regs2 (Z_to_bv 5 13) = Z_to_bv 64 HQU_HALF_HI /\ getr regs2 (Z_to_bv 5 1) = Z_to_bv 64 HVU_RA_GE /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x88) 8 shi)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R slo shi HJ H9 H10 H11 HR Hal Hw0 Hw1
  Hslo Hshi Va8.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
remember (hvc_x1 HQU_HALF_HI) as ex eqn:Hex.
assert (EA : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs ex) n = getr regs rr)
  by (intros n rr Hn; exact (ew_Ereg_nat regs _ n rr Hn)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 slo) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 shi) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 HQU_HALF_HI) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E9u : bv_unsigned (ew (Ereg regs ex) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss3
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_RA_SUB) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss3. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ (w_H W) memc 9 R 0x88 0xb0 0x88 0x90 _ E9u ltac:(lia) ltac:(lia)).
    + intros o Ho. apply Hpres. lia.
    + constructor; [|constructor].
      exact (hvu_slot_chunk _ _ _ R 0xa8 HQU_HALF_HI 33 E33
        ltac:(rewrite Z.mod_small by (unfold HQU_HALF_HI; lia); exact Va8)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [hvc_f9 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite E9u. change (2 ^ 4) with 16. repeat split; lia. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x88 <= a < R + 0x90) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_RA_SUB) with (Z_to_bv 64 HVU_RA_SUB).
hvu_run HPgSteps.RTBspan hvu_awr.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (@hvu_kept_run fx (fun a => R + 0x88 <= a < R + 0x90) _ _ _ _ _ _ KE HFr) as KS end.
lazymatch type of KS with ?P -> _ => assert (KW : P) end.
{ intros a (rg & Hr & Hb). cbv beta.
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite E9u in Hb; lia | ]).
  destruct Hr. }
specialize (KS KW). clear KW KE.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict ?H ?ms) |- _ =>
  let rs := eval vm_compute in (ss_mem ss') in
  lazymatch rs with [?rg] =>
    assert (C88 : val_mem rsegs (mrestrict H (ms_mem ms)) (R + 0x88) 8 shi)
    by (pose proof (YN0d.st_ok_chunk rsegs E' ss' (restrict H ms) 0 rg (YP09.mkChunk 0x88 (CVal 8 (SOff 11 0))) HS
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as HC0;
        cbn [YP09.r_base base_val] in HC0; rewrite E9u in HC0;
        exact (hvu_chunk8_val E' _ R 0x88 (SOff 11 0) shi ltac:(rewrite hvu_denot0; exact E11) Hshi HC0))
  end end.
apply SRr_ret.
eapply (hvu_post_intro B); [exact HS | reflexivity | reflexivity | exact HJ | hvu_io | hvu_kept hvc_k3 | exact KS | ].
cbv beta.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split; [hvu_sv; rewrite hvu_denot0; exact E10|].
split; [hvu_sv; rewrite hvu_denot0; exact E10|].
split; [hvu_sv; rewrite hvu_denot0; exact E11|].
split; [hvu_sv; cbn [sv_denot]; reflexivity|].
split; [hvu_sv; rewrite hvu_denot0; exact E33|].
split; [hvu_sv; cbn [sv_denot]; reflexivity|].
exact C88.
Qed.

(* ---------------- c4 0x8363c: `bgez a0` after __getf2 ----------------
   taken (frac >= 0.5L): `addi a0,s2,1; blt a0,s2 -> unimp; mv s2,a0` to 0x83680; not taken: the call of
   __lttf2 with a0:a1 = s8:R+0x88 and a2:a3 = 0:R+0xa0 *)
Definition hvc_R4 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0xa8 0 0
    [YP09.mkChunk 0x88 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xa0 (CVal 8 (SOff 34 0))].
Definition hvc_ss4 : sstate := mkSS HVU_RA_GE sr_atoms [hvc_R4] None (mkFacts [] [] []).

Lemma hvc_c4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R t g slo shi : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = Z_to_bv 64 R -> getr regs (Z_to_bv 5 10) = Z_to_bv 64 g ->
getr regs (Z_to_bv 5 18) = Z_to_bv 64 t -> getr regs (Z_to_bv 5 24) = Z_to_bv 64 slo ->
0 <= R -> R + 0xa8 <= 2 ^ 64 -> -1 <= g <= 1 -> 0 <= shi < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x88) 8 shi ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 HQU_MHALF_HI ->
branch_taken BC_LT (Z_to_bv 64 (t + 1)) (Z_to_bv 64 t) = false ->
SRr rsegs W (cfg_at rsegs HVU_RA_GE regs memc mdc)
(fun W2 c2 =>
 (0 <= g /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83680 hvc_k4a
    (fun regs2 => getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (t + 1)) W2 c2) \/
 (g < 0 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_SF_LT hvc_k2
    (fun regs2 => getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 slo /\ getr regs2 (Z_to_bv 5 11) = Z_to_bv 64 shi /\
       getr regs2 (Z_to_bv 5 12) = Z_to_bv 64 0 /\ getr regs2 (Z_to_bv 5 13) = Z_to_bv 64 HQU_MHALF_HI /\
       getr regs2 (Z_to_bv 5 1) = Z_to_bv 64 HVU_RA_LT) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R t g slo shi HJ H9 H10 H18 H24
  HR0 HR1 Hg Hshi V88 Va0 Hlt.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvc_x2 shi HQU_MHALF_HI) as ex eqn:Hex.
assert (EA : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs ex) n = getr regs rr)
  by (intros n rr Hn; exact (ew_Ereg_nat regs _ n rr Hn)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 g) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 t) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 slo) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 shi) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 HQU_MHALF_HI) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss4
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_RA_GE) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss4. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hvu_slot_chunk _ _ _ R 0x88 shi 33 E33 ltac:(rewrite Z.mod_small by lia; exact V88)).
    + exact (hvu_slot_chunk _ _ _ R 0xa0 HQU_MHALF_HI 34 E34
        ltac:(rewrite Z.mod_small by (unfold HQU_MHALF_HI; lia); exact Va0)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_RA_GE) with (Z_to_bv 64 HVU_RA_GE).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite hvu_denot0, E10 in Hc; cbn [sv_denot] in Hc; rewrite (hvc_bge0 g Hg) in Hc.
- (* taken: frac >= 0.5L, r = t + 1 *)
  hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
  hvu_branch HPgSteps.RTBspan Hc2.
  all: rewrite hvu_denot0, E18, (hvc_soff E 18 t _ E18), Hlt in Hc2.
  + discriminate Hc2.
  + hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x83680. hvu_mem.
    apply SRr_ret; left. split; [apply Z.leb_le in Hc; exact Hc|].
    hvu_post0_tac B hvc_k4a. cbv beta.
    lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
      rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
    hvu_sv. exact (hvc_soff E 18 t 1 E18).
- (* not taken: frac < 0.5L, the call of __lttf2 *)
  hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
  apply SRr_ret; right. split; [apply Z.leb_gt in Hc; exact Hc|].
  hvu_post0_tac B hvc_k2. cbv beta.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hvu_sv; rewrite hvu_denot0; exact E24|].
  split; [hvu_sv; rewrite hvu_denot0; exact E33|].
  split; [hvu_sv; cbn [sv_denot]; reflexivity|].
  split; [hvu_sv; rewrite hvu_denot0; exact E34|].
  hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ---------------- c5 0x83654: `bgez a0` after __lttf2 ----------------
   taken (not frac < -0.5L): r = t, to 0x83680; not taken: `addi a0,s2,-1; bge a0,s2 -> unimp; j; mv s2,a0` *)
Definition hvc_ss5 : sstate := mkSS HVU_RA_LT sr_atoms [] None (mkFacts [] [] []).

Lemma hvc_c5 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (t l : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = Z_to_bv 64 l -> getr regs (Z_to_bv 5 18) = Z_to_bv 64 t -> -1 <= l <= 1 ->
branch_taken BC_GE (Z_to_bv 64 (t + -1)) (Z_to_bv 64 t) = false ->
SRr rsegs W (cfg_at rsegs HVU_RA_LT regs memc mdc)
(fun W2 c2 =>
 (0 <= l /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83680 hvc_k4a
    (fun regs2 => getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 t) W2 c2) \/
 (l < 0 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83680 hvc_k4a
    (fun regs2 => getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 (t - 1)) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t l HJ H10 H18 Hl Hlt.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember HPgSteps.rt_extra as ex eqn:Hex.
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 l)
  by (rewrite (ew_Ereg_nat regs ex 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 t)
  by (rewrite (ew_Ereg_nat regs ex 18 (Z_to_bv 5 18) eq_refl); exact H18).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss5
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_RA_LT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss5. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE Hex.
unfold cfg_at. change (w64 HVU_RA_LT) with (Z_to_bv 64 HVU_RA_LT).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite hvu_denot0, E10 in Hc; cbn [sv_denot] in Hc; rewrite (hvc_bge0 l Hl) in Hc.
- (* taken: r = t *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x83680. hvu_mem.
  apply SRr_ret; left. split; [apply Z.leb_le in Hc; exact Hc|].
  hvu_post0_tac B hvc_k4a. cbv beta.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  hvu_sv. rewrite hvu_denot0. exact E18.
- (* not taken: r = t - 1 *)
  hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
  hvu_branch HPgSteps.RTBspan Hc2.
  all: rewrite hvu_denot0, E18, (hvc_soff E 18 t _ E18), Hlt in Hc2.
  + discriminate Hc2.
  + hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x83680. hvu_mem.
    apply SRr_ret; right. split; [apply Z.leb_gt in Hc; exact Hc|].
    hvu_post0_tac B hvc_k4a. cbv beta.
    lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
      rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
    hvu_sv. rewrite (hvc_soff E 18 t _ E18). f_equal; lia.
Qed.

(* ---------------- c6 0x83680: `ld t5,0x110(s1); ld t6,0x108(s1); li a0,255; li a5,5; bltu a0,s2` ---------------- *)
Definition hvc_R6 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x108 0x118 0 0
    [YP09.mkChunk 0x108 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 34 0))].
Definition hvc_ss6 : sstate := mkSS 0x83680 sr_atoms [hvc_R6] None (mkFacts [] [] []).
Definition hvc_R6p (v108 v110 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 30) = Z_to_bv 64 v110 /\ getr regs2 (Z_to_bv 5 31) = Z_to_bv 64 v108 /\
getr regs2 (Z_to_bv 5 15) = Z_to_bv 64 5.

Lemma hvc_c6 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R rv v108 v110 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = Z_to_bv 64 R -> getr regs (Z_to_bv 5 18) = Z_to_bv 64 rv ->
0 <= R -> R + 0x118 <= 2 ^ 64 -> 0 <= v108 < 2 ^ 64 -> 0 <= v110 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 v108 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 v110 ->
SRr rsegs W (cfg_at rsegs 0x83680 regs memc mdc)
(fun W2 c2 =>
 (255 < rv mod 2 ^ 64 /\
  hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvc_k6 (hvc_R6p v108 v110) W2 c2) \/
 (rv mod 2 ^ 64 <= 255 /\
  hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_TAIL hvc_k6 (hvc_R6p v108 v110) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R rv v108 v110 HJ H9 H18 HR0 HR1 H108 H110
  V108 V110.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvc_x2 v108 v110) as ex eqn:Hex.
assert (EA : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs ex) n = getr regs rr)
  by (intros n rr Hn; exact (ew_Ereg_nat regs _ n rr Hn)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 rv) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 v108) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 v110) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hvc_ss6
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83680) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvc_ss6. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hvu_slot_chunk _ _ _ R 0x108 v108 33 E33 ltac:(rewrite Z.mod_small by lia; exact V108)).
    + exact (hvu_slot_chunk _ _ _ R 0x110 v110 34 E34 ltac:(rewrite Z.mod_small by lia; exact V110)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x83680) with (Z_to_bv 64 0x83680).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite hvu_denot0, E18 in Hc; cbn [sv_denot] in Hc; rewrite YO0c.branch_ltu, !YO0c.lit64_unsigned in Hc.
all: change (255 mod 2 ^ 64) with 255 in Hc.
- (* taken: 255 < r, the refusal fold *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_RF. hvu_mem.
  apply SRr_ret; left. split; [apply Z.ltb_lt in Hc; exact Hc|].
  hvu_post0_tac B hvc_k6. unfold hvc_R6p.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hvu_sv; rewrite hvu_denot0; exact E34|].
  split; [hvu_sv; rewrite hvu_denot0; exact E33|].
  hvu_sv. cbn [sv_denot]. reflexivity.
- (* not taken: r <= 255, TAIL *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_TAIL. hvu_mem.
  apply SRr_ret; right. split; [apply Z.ltb_ge in Hc; exact Hc|].
  hvu_post0_tac B hvc_k6. unfold hvc_R6p.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split; [hvu_sv; rewrite hvu_denot0; exact E34|].
  split; [hvu_sv; rewrite hvu_denot0; exact E33|].
  hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

End bl.

(* ===================================== the cut CV carried along the lane ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis ERR : api_env rsegs B.

(* [HPgM3dFlt.v hvl_core_step] *)
Lemma hvc_core_step : forall (cx : hsu_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hsu_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hr & Hfr & Hperm & Hio & Hmo & HK)
  HJ3 Hr3 Hfr3 Hperm3 Hio3 Hmo3 HK3.
split; [exact HJ3|].
split; [intros q Hq; rewrite (Hr3 q Hq); exact (Hr q Hq)|].
split; [rewrite Hfr3; exact Hfr|].
split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|].
intros a Ha Hs He. rewrite (HK3 a Ha Hs He). exact (HK a Ha Hs He).
Qed.

(* the call adapters' frame of facts (HPgCalls.hc_core) at R, from a cut's journal-and-frame part *)
Lemma hvc_hc_core : forall (cx : hsu_scx rsegs) sh E ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh -> hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx sh E ly2 S2 W2 regs2 mem2 md2 HP Hcore.
pose proof HP as (_ & Hev & H2 & H3 & H4 & HSe & Hal & Hrsz & Hwin & _).
destruct Hcore as (HJ & Hr234 & _).
cbn [hi_rsz headamp_himg_B] in Hrsz.
split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hr234 2 (or_introl eq_refl))|].
split; [rewrite <- H3; exact (Hr234 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- H4; exact (Hr234 4 (or_intror (or_intror eq_refl)))|].
split; [apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 32);
  [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]]|].
split; [exact Hwin | lia].
Qed.

(* the errno cell lies in the image, far below the allocator's ceiling *)
Lemma hvc_errno_low : forall i, 0 <= i < 4 -> 0 <= as_errno B + i < alloc_ceiling.
Proof using ERR.
intros i Hi. destruct ERR as ((H0 & H1) & _ & _).
pose proof asan_consts as (C1 & _).
unfold kLowMemEnd in H1. lia.
Qed.

(* ===================================== one cut CV ===================================== *)
Section cv.
Variables (cx : hsu_scx rsegs) (POST : world rsegs -> config -> Prop) (r : Model.pod_rec) (ev : Z) (at0 m : nat).
Variables (fx2 : YK11.FPState) (ly2 : alayout) (S2 : astate) (W2 : world rsegs) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model).
Variables (kk : list byte) (v : Model.ent) (ch p b : Z) (cs : list cell) (keys rf : Z).
Hypothesis HS : @hqu_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HCV : @hvu_cut_CV fx rc SK B MT cx fx2 r at0 m kk v ch p b cs keys rf ly2 S2 W2 regs2 mem2 md2.

Definition hvc_R : Z := e_R (x_e rsegs cx).
(* the values of the inlined pod_nearest: t, d, (long double)t, frac and the two comparisons *)
Definition hvc_t : Z := NearVal.pn_t b.
Definition hvc_fd : Z := C_floatditf.f128_of_i64 hvc_t.
Definition hvc_s : Z := SF.f128_sub (hvu_d b) hvc_fd.
Definition hvc_g : Z := SF.f128_ge hvc_s NearSF.HALF_128.
Definition hvc_l : Z := SF.f128_le hvc_s NearSF.MHALF_128.
(* what a state of the lane may have written: the soft-float callees' stack below R and the cell R+0x88 *)
Definition hvc_wz (a : Z) : Prop :=
(hvc_R - T_SEG_STK <= a < hvc_R) \/ (hvc_R + 0x88 <= a < hvc_R + 0x90).

Lemma hvc_pre : hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B).
Proof. exact (hvu_start_pre B cx r ev HS). Qed.

(* the stack: R, its window and the allocator's ceiling *)
Lemma hvc_geo :
2 ^ 46 <= hvc_R <= 2 ^ 47 /\ hvc_R mod 32 = 0 /\ hvc_R + 0x220 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= hvc_R - T_SEG_STK /\ alloc_ceiling <= hvc_R - T_SEG_STK /\
x_sp0 rsegs cx <= 2 ^ 47 /\ spZ (x_regs rsegs cx) = hvc_R /\ T_SEG_STK = 16384 /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
destruct (hvu_stack B cx _ hvc_pre) as (HR & Hal & Hrs & Hwin & Hceil & H46 & H47 & _).
pose proof asan_consts as (C1 & _).
unfold hvc_R. repeat split; try assumption; try lia; reflexivity.
Qed.

Lemma hvc_R16 : hvc_R mod 16 = 0.
Proof.
pose proof hvc_geo as (_ & Hal & _).
apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]].
Qed.

Lemma hvc_CV_base : @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2.
Proof. exact (proj1 HCV). Qed.

(* the float b, its range and the three tests passed *)
Lemma hvc_b : 0 <= b < 2 ^ 32 /\ fst (fp_eq fmt_single b b) = true /\ fst (fp_lt fmt_single b 0xbf800000) = false /\
fst (fp_lt fmt_single 0x43800000 b) = false.
Proof.
pose proof HCV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbd & Heq & Hlo & Hhi & _).
split; [rewrite Hbd; apply Cursor.rd32_range|]. split; [exact Heq|]. split; [exact Hlo | exact Hhi].
Qed.

(* t's range (hn_traps) and the two overflow tests *)
Lemma hvc_traps : - 2 ^ 31 - 1 <= bv_swrap 64 hvc_t <= 2 ^ 31.
Proof.
pose proof hvc_b as (Hb & Heq & Hlo & Hhi).
exact (hvc_t_rng b Hb Heq Hlo Hhi).
Qed.
Lemma hvc_inc : branch_taken BC_LT (Z_to_bv 64 (hvc_t + 1)) (Z_to_bv 64 hvc_t) = false.
Proof. exact (hvc_lt_inc hvc_t hvc_traps). Qed.
Lemma hvc_dec : branch_taken BC_GE (Z_to_bv 64 (hvc_t + -1)) (Z_to_bv 64 hvc_t) = false.
Proof. exact (hvc_ge_dec hvc_t hvc_traps). Qed.

(* r: exactly the code's three arms, in its order *)
Lemma hvc_pnr : NearVal.pn_r b = (if 0 <=? hvc_g then hvc_t + 1 else if hvc_l <? 0 then hvc_t - 1 else hvc_t).
Proof. exact (hvm_pnr_eq b (proj1 hvc_b)). Qed.

(* the value entry *)
Lemma hvc_facts : Model.pod_rec_wf r /\ Model.ent_wf v /\ Model.e_type v = Model.POD_FLOAT /\
4 <= Model.e_size v /\ b = Cursor.rd32 (Model.e_body v) /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) kk) = Headamp.KCell ch p.
Proof.
pose proof HS as (_ & _ & Hwf & _).
pose proof HCV as (_ & _ & _ & _ & _ & _ & _ & _ & Hkey & Hty & Hsz & Hbd & _ & _ & _ & Hpair & _).
pose proof Hpair as (Hv & _ & Hlen & _).
destruct (Model.ents_wf r Hwf) as (Hle & Hall).
split; [exact Hwf|].
split; [rewrite Hv; rewrite Forall_forall in Hall; apply Hall; apply nth_In; exact Hlen|].
split; [exact Hty|]. split; [exact Hsz|]. split; [exact Hbd | exact Hkey].
Qed.

(* no nearest byte: a refusal; a nearest byte: the cell's value *)
Lemma hvc_cell_none : 255 < NearVal.pn_r b mod 2 ^ 64 ->
Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof.
intros Hgt. pose proof hvc_facts as (_ & Hvwf & Hty & Hsz & Hbd & Hkey).
pose proof hvc_b as (Hb & Heq & Hlo & Hhi).
apply (hvm_cell_inl kk v ch p Hkey). left.
rewrite (hvm_cv_float v Hvwf Hty Hsz), <- Hbd, <- (hvm_hn_nearest b Hb), (hvm_hn_body b Heq Hlo Hhi).
rewrite (proj2 (Z.ltb_lt _ _) Hgt). lia.
Qed.

Lemma hvc_cell_some : NearVal.pn_r b mod 2 ^ 64 <= 255 -> Headamp.cell_value v = NearVal.pn_r b mod 2 ^ 64.
Proof.
intros Hle. pose proof hvc_facts as (_ & Hvwf & Hty & Hsz & Hbd & _).
pose proof hvc_b as (Hb & Heq & Hlo & Hhi).
rewrite (hvm_cv_float v Hvwf Hty Hsz), <- Hbd, <- (hvm_hn_nearest b Hb), (hvm_hn_body b Heq Hlo Hhi).
rewrite (proj2 (Z.ltb_ge _ _) Hle). reflexivity.
Qed.

(* ===================================== what every state of the lane keeps ===================================== *)
Definition hvc_mid (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 : Prop :=
hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ hvc_wz a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) /\
(forall q, In q HVC_KR -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) /\
hd_fxk [] fx2 fx3.

Lemma hvc_mid_CV : hvc_mid fx2 ly2 S2 W2 regs2 mem2 md2.
Proof.
pose proof hvc_CV_base as (Hcore & (_ & Hz) & _).
split; [exact Hcore|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros kq _; reflexivity | exact Hz].
Qed.

(* the cell R+0x88 is M03's own (hi_w3's real-frame cells [R, R+0x160)) *)
Lemma hvc_band_E3 : forall a, hvc_R + 0x88 <= a < hvc_R + 0x90 -> hqu_E3 rsegs B cx a.
Proof.
intros a Ha. left. unfold hd_inw. cbn [hi_w3 headamp_himg_B].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. unfold hvc_R in Ha. lia.
Qed.

(* across a block: the journal at the block's end, the I/O-equal model, the kept registers and every byte outside
   R+0x88 .. R+0x90 *)
Lemma hvc_mid_run : forall fx3 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 ->
(forall rr, In rr HVC_KRB -> getr regs4 rr = getr regs3 rr) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hvc_R + 0x88 <= a < hvc_R + 0x90) ->
 aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W3) mem3 a) ->
hvc_mid fx3 ly3 S3 W3 regs4 mem4 md4.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (Hcore & HK & HR & Hfx) HJ4 Hio HR4 HK4.
split.
{ apply (hvc_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regs4 mem4 md4 Hcore HJ4);
  [ intros q Hq; apply HR4; apply hvc_krb; destruct Hq as [-> | [-> | ->]];
    [left | right; left | right; right; left]; reflexivity
  | reflexivity | apply Permutation_refl | exact Hio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ HE. apply HK4; [exact Ha|]. intros Hb. exact (HE (hvc_band_E3 a Hb)). }
split.
{ intros a Ha Hw. rewrite (HK4 a Ha); [exact (HK a Ha Hw)|].
  intros Hb. apply Hw. right. exact Hb. }
split; [|exact Hfx].
intros q Hq. rewrite (HR4 (Z_to_bv 5 q) (hvc_krb q ltac:(right; right; right; exact Hq))). exact (HR q Hq).
Qed.

(* across the float step fcvt.l.s: the registers but s2, the memory and the journal are kept; the model is its
   materialized copy *)
Lemma hvc_mid_fp : forall fx3 ly3 S3 W3 regs3 mem3 md3 fx4 regs4 X,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hd_fxk [] fx3 fx4 ->
(forall rr, In rr HVC_KRB -> getr regs4 rr = getr regs3 rr) ->
hvc_mid fx4 ly3 S3 W3 regs4 mem3 (with_vm_backing (m_vm_lazy md3) X md3).
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 fx4 regs4 X (Hcore & HK & HR & Hfx) Hfx4 HR4.
split.
{ apply (hvc_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regs4 mem3 _ Hcore);
  [ exact (ajournal_materialize rsegs B (AR_laws_ok rsegs B) HPgSteps.img_segs_low
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X (proj1 Hcore))
  | intros q Hq; apply HR4; apply hvc_krb; destruct Hq as [-> | [-> | ->]];
    [left | right; left | right; right; left]; reflexivity
  | reflexivity | apply Permutation_refl | apply HPgSteps.same_io_wvb | apply (mo_le_refl MT MTL) |].
  intros a _ _ _. reflexivity. }
split; [exact HK|]. split; [|exact (hvc_fxk_trans _ _ _ Hfx Hfx4)].
intros q Hq. rewrite (HR4 (Z_to_bv 5 q) (hvc_krb q ltac:(right; right; right; exact Hq))). exact (HR q Hq).
Qed.

(* across a soft-float call (HPgM3dSFU's continuation), whose callee writes at most [R - T, R) *)
Lemma hvc_mid_call : forall fx3 ly3 S3 W3 regs3 mem3 md3 fx4 ly4 S4 W4 regs4 mem4 md4 T,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> 0 <= T <= T_SEG_STK -> hd_fxk [] fx3 fx4 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly4 S4 W4 mem4 md4 regs4 hvc_R ->
aregs_preserved regs3 regs4 -> frames S4 = frames S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
same_io md3 md4 -> mo_le MT S3 S4 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hvc_R - T <= a < hvc_R) -> aview rsegs (w_H W4) mem4 a = aview rsegs (w_H W3) mem3 a) ->
hvc_mid fx4 ly4 S4 W4 regs4 mem4 md4.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 fx4 ly4 S4 W4 regs4 mem4 md4 T (Hcore & HK & HR & Hfx) HT Hfx4 HC4 Hpres
  Hfr Hperm Hio Hmo HK4.
pose proof hvc_geo as (_ & _ & _ & _ & _ & _ & Hsp & HTS & _).
split.
{ apply (hvc_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hcore (proj1 HC4));
  [ intros q Hq; apply Hpres; unfold acallee_saved; lia
  | exact Hfr | exact Hperm | exact Hio | exact Hmo |].
  intros a Ha Hs _. apply HK4; [exact Ha|]. rewrite Hsp in Hs. lia. }
split.
{ intros a Ha Hw. rewrite (HK4 a Ha); [exact (HK a Ha Hw)|].
  intros Hb. apply Hw. left. lia. }
split; [|exact (hvc_fxk_trans _ _ _ Hfx Hfx4)].
intros q Hq. rewrite (Hpres q); [exact (HR q Hq)|].
unfold HVC_KR in Hq. cbn [In] in Hq. unfold acallee_saved. lia.
Qed.

(* the call adapters' premises at a state of the lane *)
Lemma hvc_mid_hc : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly3 S3 W3 mem3 md3 regs3 hvc_R.
Proof. intros fx3 ly3 S3 W3 regs3 mem3 md3 (Hcore & _). exact (hvc_hc_core cx _ _ _ _ _ _ _ _ hvc_pre Hcore). Qed.

Lemma hvc_wz_low : forall a, 0 <= a < alloc_ceiling -> ~ hvc_wz a.
Proof.
intros a Ha. pose proof hvc_geo as (_ & _ & _ & _ & Hceil & _ & _ & HTS & _).
unfold hvc_wz. lia.
Qed.

(* a byte below the allocator's ceiling is as at CV *)
Lemma hvc_mid_low : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 (_ & HK & _) a Ha.
pose proof hvc_geo as (_ & _ & _ & _ & _ & _ & _ & _ & Hc).
apply HK; [lia|]. exact (hvc_wz_low a Ha).
Qed.

Lemma hvc_mid_rom : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> rom_view rsegs W3 mem3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
pose proof hvc_CV_base as (_ & _ & _ & Hrom & _).
pose proof hvc_geo as (_ & _ & _ & _ & _ & _ & _ & _ & Hc).
apply (hm_rom_kept rsegs W2 W3 mem2 mem3 Hrom). intros a (sg & Hin & _ & Hsb).
assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
apply (hvc_mid_low _ _ _ _ _ _ _ HM). lia.
Qed.

(* the float registers of a state of the lane: every one as at CV, a zero rounding mode *)
Lemma hvc_mid_fs : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hqu_fs fx3 8 b /\ hqu_fs fx3 9 HQU_F32_M1 /\ hqu_fs fx3 18 HQU_F32_256 /\ hqu_fs fx3 19 HQU_F32_2P63 /\
YK0o.frm_zero (@fp_csr fx3) /\ @hqu_fxk fx fx3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 (_ & _ & _ & (Hf & Hz)).
pose proof HCV as (Hb & _ & H8 & H9 & H18 & H19 & _).
pose proof Hb as (_ & (Hk & _) & _).
unfold hqu_fs in *.
split; [rewrite (Hf (Z_to_bv 5 8) (fun x => x)); exact H8|].
split; [rewrite (Hf (Z_to_bv 5 9) (fun x => x)); exact H9|].
split; [rewrite (Hf (Z_to_bv 5 18) (fun x => x)); exact H18|].
split; [rewrite (Hf (Z_to_bv 5 19) (fun x => x)); exact H19|].
split; [exact Hz|].
split; [|exact Hz].
intros kq Hk'. rewrite (Hf kq (fun x => x)). exact (Hk kq Hk').
Qed.

(* ===================================== the cut's facts at a state of the lane ===================================== *)
Definition hvc_locb (f : hd_loc * Z) : bool :=
match fst f with
| LReg q => existsb (Z.eqb q) HVC_KR
| LCell XR o => ((0 <=? o) && (o + 8 <=? 0x88)) || ((0x90 <=? o) && (o + 8 <=? 0x220))
| LCell _ _ => false
end.

Lemma hvc_at_kept : forall fx3 ly3 S3 W3 regs3 mem3 md3 L,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hsu_at_cx rsegs cx W2 mem2 regs2 L -> forallb hvc_locb L = true ->
hsu_at_cx rsegs cx W3 mem3 regs3 L.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 L (_ & HK & HR & _) HL Hb.
pose proof hvc_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
unfold hsu_at_cx, hsu_at in *.
apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) L HL).
intros f Hf. pose proof (proj1 (forallb_forall _ _) Hb f Hf) as Hl.
apply (hm_keeps_of rsegs (fun x => ~ (0 <= x < 2 ^ 64) \/ hvc_wz x)).
- intros x Hx. apply HK; [|intros Hw; apply Hx; right; exact Hw].
  destruct (Z_lt_le_dec x 0) as [Hn|Hn]; [exfalso; apply Hx; left; lia|].
  destruct (Z_lt_le_dec x (2 ^ 64)) as [Hm|Hm]; [lia | exfalso; apply Hx; left; lia].
- destruct f as [[q|bb o] w]; cbn [fst hvc_locb] in Hl |- *.
  + apply existsb_exists in Hl as (z & Hz & Hzq). apply Z.eqb_eq in Hzq. subst z. exact (HR q Hz).
  + destruct bb; try (cbn in Hl; discriminate Hl).
    change (((0 <=? o) && (o + 8 <=? 0x88)) || ((0x90 <=? o) && (o + 8 <=? 0x220)) = true) in Hl.
    intros i Hi. cbn [hd_xv]. unfold hvc_wz. unfold hvc_R in *.
    apply orb_true_iff in Hl as [Hl|Hl]; apply andb_true_iff in Hl as (Hl1 & Hl2);
    apply Z.leb_le in Hl1; apply Z.leb_le in Hl2; lia.
Qed.

(* the facts of CV every later state keeps *)
Definition hvc_LK : list (hd_loc * Z) :=
hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
[(LCell XR 0x90, p); (LReg 23, hvm_top p); (LReg 21, ch)].

Lemma hvc_CV_at : hsu_at_cx rsegs cx W2 mem2 regs2 hvc_LK.
Proof. pose proof HCV as (_ & Hat & _). unfold hsu_at_cx in *. unfold hvc_LK. hvu_sub Hat. Qed.

Lemma hvc_at_K : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hsu_at_cx rsegs cx W3 mem3 regs3 hvc_LK.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
apply (hvc_at_kept _ _ _ _ _ _ _ _ HM hvc_CV_at). vm_compute. reflexivity.
Qed.

(* a block of the segment's own state lies below the allocator's ceiling (YG0d AR_blocks_law) *)
Lemma hvc_blk_low : forall (q n : Z), In (q, n) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
q mod 16 = 0 /\ 4096 <= q /\ q + req_size n <= alloc_ceiling.
Proof.
intros q n Hin.
pose proof hvc_pre as Hpre. unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (Hnz & H0 & Hc & _).
split; [exact Hnz|]. split; [exact H0 | exact Hc].
Qed.

(* hqu_base3 and x at a state of the lane *)
Lemma hvc_base_at : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
@hqu_base3 fx rc SK rsegs B MT cx fx3 r hqu_shX ly3 S3 W3 regs3 mem3 md3 /\
hqu_x_at rsegs cx W3 mem3 cs (keys + 1) rf.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
pose proof (hvc_mid_low _ _ _ _ _ _ _ HM) as Kl.
pose proof HM as (Hcore3 & _).
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM) as (_ & _ & _ & _ & _ & Hfxk3).
pose proof hvc_CV_base as (_ & _ & Hfsh & _ & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
pose proof HCV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxat).
pose proof HS as (HP & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (hvu_apart B cx _ hvc_pre) as (Hppin & _ & Hp0 & Hpc & _ & HF0 & HFc & _).
destruct (hvc_blk_low _ _ Hpodin) as (_ & Hpod0 & Hpodc).
destruct (hvc_blk_low _ _ Houtin) as (_ & Hout0 & Houtc).
pose proof asan_consts as (C1 & _).
assert (Hreq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (Hgarr : forall a l, garr8 rsegs (mrestrict (w_H W2) mem2) a (hd_zbytes l) ->
  0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  garr8 rsegs (mrestrict (w_H W3) mem3) a (hd_zbytes l)).
{ intros a l Hg Ha0 Ha1. apply (proj1 (hm_bytes_zbytes rsegs (w_H W3) mem3 a l)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 a l) Hg)|].
  intros y Hy. apply Kl. lia. }
split.
- split; [exact Hcore3|]. split; [exact Hfxk3|].
  split.
  { unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh).
    intros i Hi. rewrite hqu_shX_len in Hi. apply Kl.
    assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
    assert (8 * (e_F (x_e rsegs cx) / 8) <= e_F (x_e rsegs cx)) by (apply Z.mul_div_le; lia).
    unfold shadow_addr, SHADOW_OFF. lia. }
  split; [exact (hvc_mid_rom _ _ _ _ _ _ _ HM)|].
  split.
  { unfold hsu_pp_at in *. apply Hgarr; [exact Hpp | lia|].
    rewrite (Layout.length_pp_bytes r Hwf). exact Hpc. }
  split.
  { apply Hgarr; [exact Hpod | lia|]. rewrite <- Hlen. pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)). lia. }
  split.
  { apply Hgarr; [exact Hout | lia|]. rewrite length_ha_cells_bytes.
    pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)).
    assert (Hcells : Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e rsegs cx)).
    { pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
        ltac:(lia)) as HO. fold (hqu_ans rsegs cx r) in HO.
      apply answer_ok_parts in HO as [[(_ & E2 & _) | (E1 & E2 & _)] _]; [rewrite E2; cbn [length]|]; lia. }
    lia. }
  split.
  { apply Hgarr; [exact Hres | unfold HQU_RES; lia|]. unfold ans_res_bytes. rewrite length_ha_res_bytes.
    unfold HQU_RES. lia. }
  exists ev2. intros j Hj.
  assert (Hj' : 0 <= Z.of_nat j < 4) by lia.
  rewrite (Kl _ (hvc_errno_low (Z.of_nat j) Hj')). exact (Herr j Hj).
- destruct Hxat as (Hx & Hrest). split; [|exact Hrest].
  destruct Hrest as (HlX & _).
  apply Hgarr; [exact Hx | unfold HQU_XO; lia|].
  rewrite (hqu_x_open_len cs (keys + 1) rf HlX). unfold HQU_XO. lia.
Qed.

(* RF 0x836a0 at a state of the lane, when the pair is refused as out of range *)
Lemma hvc_cut_RF : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 30) = w64 (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) ->
getr regs3 (Z_to_bv 5 31) = w64 (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)) ->
getr regs3 (Z_to_bv 5 15) = w64 Headamp.REFUSE_OUT_OF_RANGE ->
Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE ->
@hqu_cut_RF fx rc SK rsegs B MT cx fx3 r at0 m kk v Headamp.REFUSE_OUT_OF_RANGE cs keys rf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H30 H31 H15 Hcell.
destruct (hvc_base_at _ _ _ _ _ _ _ HM) as (Hb3 & Hx3).
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM) as (_ & H9 & H18 & H19 & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK.
pose proof HCV as (_ & _ & _ & _ & _ & _ & Hlive & Hat0 & _ & _ & _ & _ & _ & _ & _ & Hpair & _).
split; [exact Hb3|].
split.
{ unfold hsu_at_cx, hsu_at in HK |- *. unfold hvc_LK in HK.
  rewrite !Forall_app in HK. rewrite !Forall_app. destruct HK as (K1 & K2 & K3 & K4).
  split; [exact K1|]. split; [exact K2|].
  split.
  { unfold hqu_L_t56. cbv zeta. apply Forall_cons; [exact H30|]. apply Forall_cons; [exact H31 | apply Forall_nil]. }
  split; [exact K3|].
  apply Forall_cons; [exact H15 | apply Forall_nil]. }
split; [exact H9|]. split; [exact H18|]. split; [exact H19|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hcell|]. split; [right; reflexivity|].
split; [exact Hpair | exact Hx3].
Qed.

(* TAIL 0x83694 at a state of the lane: s2 = val *)
Lemma hvc_cut_TAIL : forall fx3 ly3 S3 W3 regs3 mem3 md3 val,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 18) = w64 val ->
getr regs3 (Z_to_bv 5 30) = w64 (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) ->
getr regs3 (Z_to_bv 5 31) = w64 (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)) ->
getr regs3 (Z_to_bv 5 15) = w64 Headamp.REFUSE_OUT_OF_RANGE ->
Headamp.cell_value v = val -> 0 <= val <= 255 ->
@hvu_cut_TAIL fx rc SK B MT cx fx3 r at0 m kk v ch p val cs keys rf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 val HM H18 H30 H31 H15 Hval Hrng.
destruct (hvc_base_at _ _ _ _ _ _ _ HM) as (Hb3 & Hx3).
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM) as (_ & H9 & H18f & H19 & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK.
pose proof HCV as (_ & _ & _ & _ & _ & _ & Hlive & Hat0 & Hkey & _ & _ & _ & _ & _ & _ & Hpair & Hkcs & _).
split; [exact Hb3|].
split.
{ unfold hsu_at_cx, hsu_at in HK |- *. unfold hvc_LK in HK.
  rewrite !Forall_app in HK. rewrite !Forall_app. destruct HK as (K1 & K2 & K3 & K4).
  split; [exact K1|]. split; [exact K2|].
  split.
  { unfold hqu_L_t56. cbv zeta. apply Forall_cons; [exact H30|]. apply Forall_cons; [exact H31 | apply Forall_nil]. }
  split; [exact K3|].
  rewrite !Forall_cons_iff in K4. destruct K4 as (X90 & X23 & X21 & _).
  apply Forall_cons; [exact H18|]. apply Forall_cons; [exact X90|]. apply Forall_cons; [exact X23|].
  apply Forall_cons; [exact X21|]. apply Forall_cons; [exact H15 | apply Forall_nil]. }
split; [exact H9|]. split; [exact H18f|]. split; [exact H19|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hkey|]. split; [exact Hval|]. split; [exact Hrng|].
split; [exact Hpair|]. split; [exact Hkcs | exact Hx3].
Qed.

(* ===================================== the chain, from the last block back to CV ===================================== *)
Hypothesis HRF : @hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m.
Hypothesis HTAIL : @hvu_from_TAIL fx rc SK B MT cx r POST at0 m.

(* the cells t5 / t6 are reloaded from *)
Definition hvc_ps : Z := e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT.

(* 0x83680 -> RF / TAIL, with s2 = r *)
Lemma hvc_p6 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 (NearVal.pn_r b) ->
SRr rsegs W3 (@cfg_at fx3 rsegs 0x83680 regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H18.
pose proof hvc_geo as (H46 & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK. unfold hsu_at_cx in HK.
pose proof (hvu_at_get _ _ _ _ _ 9 hvc_R HK ltac:(unfold hvc_LK, hvc_R; hvu_in)) as R9.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x108 (shadow_addr hvc_ps) HK ltac:(unfold hvc_LK, hvc_ps; hvu_in)) as C108.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x110 hvc_ps HK ltac:(unfold hvc_LK, hvc_ps; hvu_in)) as C110.
cbn [hd_xv] in C108, C110. fold hvc_R in C108, C110.
pose proof (proj1 HM) as (HJ & _).
eapply SRr_bind.
{ apply (hvc_c6 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_R (NearVal.pn_r b)
    (shadow_addr hvc_ps mod 2 ^ 64) (hvc_ps mod 2 ^ 64) HJ R9 H18);
  [lia | lia | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia | exact C108 | exact C110]. }
intros W4 c4 _ [(Hgt & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q30 & Q31 & Q15))
              | (Hle & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q30 & Q31 & Q15))].
- (* RF *)
  assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem3 md4).
  { apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k6 _ _ Hk4). vm_compute. reflexivity. }
  apply (HRF fx3 ly3 S3 W3 regs4 mem3 md4 kk v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
  apply (hvc_cut_RF fx3 ly3 S3 W3 regs4 mem3 md4 HM4).
  + rewrite Q30. unfold w64. apply HPgSteps.Z_to_bv_mod64.
  + rewrite Q31. unfold w64. apply HPgSteps.Z_to_bv_mod64.
  + rewrite Q15. reflexivity.
  + exact (hvc_cell_none Hgt).
- (* TAIL *)
  assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem3 md4).
  { apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k6 _ _ Hk4). vm_compute. reflexivity. }
  apply (HTAIL fx3 ly3 S3 W3 regs4 mem3 md4 kk v ch p (NearVal.pn_r b mod 2 ^ 64) cs keys rf).
  apply (hvc_cut_TAIL fx3 ly3 S3 W3 regs4 mem3 md4 _ HM4).
  + rewrite (Hk4 (Z_to_bv 5 18) ltac:(unfold hvc_k6; hvu_kin)), H18. unfold w64.
    symmetry. apply HPgSteps.Z_to_bv_mod64.
  + rewrite Q30. unfold w64. apply HPgSteps.Z_to_bv_mod64.
  + rewrite Q31. unfold w64. apply HPgSteps.Z_to_bv_mod64.
  + rewrite Q15. reflexivity.
  + exact (hvc_cell_some Hle).
  + split; [apply Z.mod_pos_bound; lia | exact Hle].
Qed.

(* 0x83654, after __lttf2 (frac < 0.5L): r = t or t - 1 *)
Lemma hvc_p5 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvc_g < 0 ->
getr regs3 (Z_to_bv 5 10) = Z_to_bv 64 hvc_l -> getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 hvc_t ->
SRr rsegs W3 (@cfg_at fx3 rsegs HVU_RA_LT regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM Hg H10 H18.
pose proof (proj1 HM) as (HJ & _).
pose proof (hvc_le3 hvc_s NearSF.MHALF_128) as Hl3. fold hvc_l in Hl3.
eapply SRr_bind.
{ apply (hvc_c5 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_t hvc_l HJ H10 H18);
  [lia | exact hvc_dec]. }
intros W4 c4 _ [(Hl & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & Q18)
              | (Hl & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & Q18)].
- apply (hvc_p6 fx3 ly3 S3 W3 regs4 mem3 md4).
  + apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k4a _ _ Hk4). vm_compute. reflexivity.
  + rewrite Q18, hvc_pnr, (proj2 (Z.leb_gt 0 hvc_g) Hg), (proj2 (Z.ltb_ge hvc_l 0) Hl). reflexivity.
- apply (hvc_p6 fx3 ly3 S3 W3 regs4 mem3 md4).
  + apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k4a _ _ Hk4). vm_compute. reflexivity.
  + rewrite Q18, hvc_pnr, (proj2 (Z.leb_gt 0 hvc_g) Hg), (proj2 (Z.ltb_lt hvc_l 0) Hl). reflexivity.
Qed.

(* 0x8363c, after __getf2: s8 = the low word of frac, R+0x88 its high word *)
Lemma hvc_p4 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 10) = Z_to_bv 64 hvc_g -> getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 hvc_t ->
getr regs3 (Z_to_bv 5 24) = Z_to_bv 64 (SF.lo64 hvc_s) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvc_R + 0x88) 8 (SF.hi64 hvc_s) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HVU_RA_GE regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H10 H18 H24 C88.
pose proof hvc_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
pose proof (proj1 HM) as (HJ & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK. unfold hsu_at_cx in HK.
pose proof (hvu_at_get _ _ _ _ _ 9 hvc_R HK ltac:(unfold hvc_LK, hvc_R; hvu_in)) as R9.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xa0 HQU_MHALF_HI HK ltac:(unfold hvc_LK; hvu_in)) as Ca0.
cbn [hd_xv] in Ca0. fold hvc_R in Ca0.
rewrite (Z.mod_small HQU_MHALF_HI) in Ca0 by (unfold HQU_MHALF_HI; lia).
pose proof (hvc_ge3 hvc_s NearSF.HALF_128) as Hg3. fold hvc_g in Hg3.
eapply SRr_bind.
{ apply (hvc_c4 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_R hvc_t hvc_g (SF.lo64 hvc_s) (SF.hi64 hvc_s)
    HJ R9 H10 H18 H24);
  [lia | lia | lia | apply hvm_hi64_rng | exact C88 | exact Ca0 | exact hvc_inc]. }
intros W4 c4 _ [(Hg & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & Q18)
              | (Hg & -> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q10 & Q11 & Q12 & Q13 & Q1))].
- (* frac >= 0.5L: r = t + 1 *)
  apply (hvc_p6 fx3 ly3 S3 W3 regs4 mem3 md4).
  + apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k4a _ _ Hk4). vm_compute. reflexivity.
  + rewrite Q18, hvc_pnr, (proj2 (Z.leb_le 0 hvc_g) Hg). reflexivity.
- (* the call of __lttf2 *)
  assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem3 md4).
  { apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
    apply (hvc_kept_of hvc_k2 _ _ Hk4). vm_compute. reflexivity. }
  pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM4) as (_ & _ & _ & _ & Hz & _).
  apply ((@hsfu_lt_stmt fx3 rc SK B MT MTL) HVU_RA_LT POST
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mem3 md4 regs4 hvc_R
    (SF.lo64 hvc_s) (SF.hi64 hvc_s) 0 HQU_MHALF_HI
    (hvc_mid_hc _ _ _ _ _ _ _ HM4) Q1 ltac:(unfold HVU_RA_LT; lia) ltac:(reflexivity)
    Q10 Q11 Q12 Q13 (hvm_lo64_rng _) (hvm_hi64_rng _) ltac:(lia) ltac:(unfold HQU_MHALF_HI; lia)
    (hvc_mid_rom _ _ _ _ _ _ _ HM4) Hz).
  intros W5 fx5 ly5 S5 regs5 mem5 md5 Hle5 Hfx5 HC5 Hpres Hfr Hperm Hio Hmo Hkeep Hrom5 R10.
  assert (HM5 := hvc_mid_call _ _ _ _ _ _ _ fx5 ly5 S5 W5 regs5 mem5 md5 0 HM4 ltac:(lia)
    Hfx5 HC5 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha)).
  rewrite (hvm_w128 hvc_s (hvm_sub_range _ _)), (proj2 hvc_half_words) in R10.
  apply (hvc_p5 fx5 ly5 S5 W5 regs5 mem5 md5 HM5); [exact Hg | exact R10 |].
  rewrite (Hpres 18 ltac:(unfold acallee_saved; lia)).
  rewrite (Hk4 (Z_to_bv 5 18) ltac:(unfold hvc_k2; hvu_kin)). exact H18.
Qed.

(* 0x83628, after __subtf3: a0:a1 = frac *)
Lemma hvc_p3 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 10) = Z_to_bv 64 (SF.lo64 hvc_s) -> getr regs3 (Z_to_bv 5 11) = Z_to_bv 64 (SF.hi64 hvc_s) ->
getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 hvc_t ->
SRr rsegs W3 (@cfg_at fx3 rsegs HVU_RA_SUB regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H10 H11 H18.
pose proof hvc_geo as (H46 & Hal & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof hvc_R16 as H16.
pose proof (proj1 HM) as (HJ & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK. unfold hsu_at_cx in HK.
pose proof (hvu_at_get _ _ _ _ _ 9 hvc_R HK ltac:(unfold hvc_LK, hvc_R; hvu_in)) as R9.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xa8 HQU_HALF_HI HK ltac:(unfold hvc_LK; hvu_in)) as Ca8.
cbn [hd_xv] in Ca8. fold hvc_R in Ca8.
rewrite (Z.mod_small HQU_HALF_HI) in Ca8 by (unfold HQU_HALF_HI; lia).
eapply SRr_bind.
{ apply (hvc_c3 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_R (SF.lo64 hvc_s) (SF.hi64 hvc_s)
    HJ R9 H10 H11); [lia | exact H16 | lia | lia | apply hvm_lo64_rng | apply hvm_hi64_rng | exact Ca8]. }
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & HK4 & (Q24 & Q10 & Q11 & Q12 & Q13 & Q1 & C88)).
assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem4 md4).
{ apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem4 md4 HM HJ4 Hio4); [|exact HK4].
  apply (hvc_kept_of hvc_k3 _ _ Hk4). vm_compute. reflexivity. }
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM4) as (_ & _ & _ & _ & Hz & _).
apply ((@hsfu_ge_stmt fx3 rc SK B MT MTL) HVU_RA_GE POST
  (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mem4 md4 regs4 hvc_R
  (SF.lo64 hvc_s) (SF.hi64 hvc_s) 0 HQU_HALF_HI
  (hvc_mid_hc _ _ _ _ _ _ _ HM4) Q1 ltac:(unfold HVU_RA_GE; lia) ltac:(reflexivity)
  Q10 Q11 Q12 Q13 (hvm_lo64_rng _) (hvm_hi64_rng _) ltac:(lia) ltac:(unfold HQU_HALF_HI; lia)
  (hvc_mid_rom _ _ _ _ _ _ _ HM4) Hz).
intros W5 fx5 ly5 S5 regs5 mem5 md5 Hle5 Hfx5 HC5 Hpres Hfr Hperm Hio Hmo Hkeep Hrom5 R10.
assert (HM5 := hvc_mid_call _ _ _ _ _ _ _ fx5 ly5 S5 W5 regs5 mem5 md5 0 HM4 ltac:(lia)
  Hfx5 HC5 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha)).
rewrite (hvm_w128 hvc_s (hvm_sub_range _ _)), (proj1 hvc_half_words) in R10.
apply (hvc_p4 fx5 ly5 S5 W5 regs5 mem5 md5 HM5).
- exact R10.
- rewrite (Hpres 18 ltac:(unfold acallee_saved; lia)).
  rewrite (Hk4 (Z_to_bv 5 18) ltac:(unfold hvc_k3; hvu_kin)). exact H18.
- rewrite (Hpres 24 ltac:(unfold acallee_saved; lia)). exact Q24.
- apply (val_mem_kept rsegs (w_H W3) (w_H W5) mem4 mem5 _ 8 _); [|exact C88].
  intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0. apply Hkeep. lia.
Qed.

(* 0x83614, after __floatditf: a0:a1 = (long double)t; s8 = the low word of d, R+0x88 its high word *)
Lemma hvc_p2 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 10) = Z_to_bv 64 (SF.lo64 hvc_fd) -> getr regs3 (Z_to_bv 5 11) = Z_to_bv 64 (SF.hi64 hvc_fd) ->
getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 hvc_t -> getr regs3 (Z_to_bv 5 24) = Z_to_bv 64 (SF.lo64 (hvu_d b)) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvc_R + 0x88) 8 (SF.hi64 (hvu_d b)) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HVU_RA_FD regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H10 H11 H18 H24 C88.
pose proof hvc_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
pose proof (proj1 HM) as (HJ & _).
pose proof (hvc_at_K _ _ _ _ _ _ _ HM) as HK. unfold hsu_at_cx in HK.
pose proof (hvu_at_get _ _ _ _ _ 9 hvc_R HK ltac:(unfold hvc_LK, hvc_R; hvu_in)) as R9.
eapply SRr_bind.
{ apply (hvc_c2 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_R (SF.lo64 (hvu_d b)) (SF.hi64 (hvu_d b))
    (SF.lo64 hvc_fd) (SF.hi64 hvc_fd) HJ R9 H10 H11 H24); [lia | lia | apply hvm_hi64_rng | exact C88]. }
intros W4 c4 _ (-> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q10 & Q11 & Q12 & Q13 & Q1)).
assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem3 md4).
{ apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
  apply (hvc_kept_of hvc_k2 _ _ Hk4). vm_compute. reflexivity. }
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM4) as (_ & _ & _ & _ & Hz & _).
apply ((@hsfu_sub_stmt fx3 rc SK B MT MTL) HVU_RA_SUB POST
  (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mem3 md4 regs4 hvc_R
  (SF.lo64 (hvu_d b)) (SF.hi64 (hvu_d b)) (SF.lo64 hvc_fd) (SF.hi64 hvc_fd)
  (hvc_mid_hc _ _ _ _ _ _ _ HM4) Q1 ltac:(unfold HVU_RA_SUB; lia) ltac:(reflexivity)
  Q10 Q11 Q12 Q13 (hvm_lo64_rng _) (hvm_hi64_rng _) (hvm_lo64_rng _) (hvm_hi64_rng _)
  (hvc_mid_rom _ _ _ _ _ _ _ HM4) Hz).
intros W5 fx5 ly5 S5 regs5 mem5 md5 Hle5 Hfx5 HC5 Hpres Hfr Hperm Hio Hmo Hkeep Hrom5 R10 R11.
assert (HM5 := hvc_mid_call _ _ _ _ _ _ _ fx5 ly5 S5 W5 regs5 mem5 md5 HVU_SUB_STK HM4
  ltac:(unfold HVU_SUB_STK; lia) Hfx5 HC5 Hpres Hfr Hperm Hio Hmo Hkeep).
rewrite (hvm_w128 (hvu_d b) (hvm_ext_range _)), (hvm_w128 hvc_fd (hvm_fd_range _)) in R10, R11.
apply (hvc_p3 fx5 ly5 S5 W5 regs5 mem5 md5 HM5).
- exact R10.
- exact R11.
- rewrite (Hpres 18 ltac:(unfold acallee_saved; lia)).
  rewrite (Hk4 (Z_to_bv 5 18) ltac:(unfold hvc_k2; hvu_kin)). exact H18.
Qed.

(* 0x8360c, after fcvt.l.s: s2 = t *)
Lemma hvc_p1 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvc_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 hvc_t -> getr regs3 (Z_to_bv 5 24) = Z_to_bv 64 (SF.lo64 (hvu_d b)) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvc_R + 0x88) 8 (SF.hi64 (hvu_d b)) ->
SRr rsegs W3 (@cfg_at fx3 rsegs 0x8360c regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM H18 H24 C88.
pose proof hvc_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
pose proof (proj1 HM) as (HJ & _).
eapply SRr_bind.
{ apply (hvc_c1 (fx := fx3) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 hvc_t HJ H18). }
intros W4 c4 _ (-> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q10 & Q1)).
assert (HM4 : hvc_mid fx3 ly3 S3 W3 regs4 mem3 md4).
{ apply (hvc_mid_run _ _ _ _ _ _ _ regs4 mem3 md4 HM HJ4 Hio4); [|intros; reflexivity].
  apply (hvc_kept_of hvc_k1 _ _ Hk4). vm_compute. reflexivity. }
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM4) as (_ & _ & _ & _ & Hz & _).
apply ((@hsfu_fd_stmt fx3 rc SK B MT MTL) HVU_RA_FD POST
  (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mem3 md4 regs4 hvc_R hvc_t
  (hvc_mid_hc _ _ _ _ _ _ _ HM4) Q1 ltac:(unfold HVU_RA_FD; lia) ltac:(reflexivity) Q10
  (hvc_mid_rom _ _ _ _ _ _ _ HM4) Hz).
intros W5 fx5 ly5 S5 regs5 mem5 md5 Hle5 Hfx5 HC5 Hpres Hfr Hperm Hio Hmo Hkeep Hrom5 R10 R11.
assert (HM5 := hvc_mid_call _ _ _ _ _ _ _ fx5 ly5 S5 W5 regs5 mem5 md5 0 HM4 ltac:(lia)
  Hfx5 HC5 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha)).
apply (hvc_p2 fx5 ly5 S5 W5 regs5 mem5 md5 HM5).
- exact R10.
- exact R11.
- rewrite (Hpres 18 ltac:(unfold acallee_saved; lia)).
  rewrite (Hk4 (Z_to_bv 5 18) ltac:(unfold hvc_k1; hvu_kin)). exact H18.
- rewrite (Hpres 24 ltac:(unfold acallee_saved; lia)).
  rewrite (Hk4 (Z_to_bv 5 24) ltac:(unfold hvc_k1; hvu_kin)). exact H24.
- apply (val_mem_kept rsegs (w_H W3) (w_H W5) mem3 mem5 _ 8 _); [|exact C88].
  intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0. apply Hkeep. lia.
Qed.

(* CV 0x83608: fcvt.l.s s2,fs0,rtz, then the chain *)
Lemma hvc_p0 : SRr rsegs W2 (@cfg_at fx2 rsegs HVU_CV regs2 mem2 md2) POST.
Proof.
pose proof hvc_mid_CV as HM.
pose proof (hvc_mid_fs _ _ _ _ _ _ _ HM) as (Hf8 & _ & _ & _ & Hz & _).
pose proof hvc_b as (Hb & _).
pose proof HCV as (_ & Hat & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 24 (SF.lo64 (hvu_d b)) Hat ltac:(hvu_in)) as R24.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x88 (SF.hi64 (hvu_d b)) Hat ltac:(hvu_in)) as C88.
cbn [hd_xv] in C88. fold hvc_R in C88.
rewrite (Z.mod_small (SF.hi64 (hvu_d b))) in C88 by apply hvm_hi64_rng.
unfold cfg_at. change (w64 HVU_CV) with (Z_to_bv 64 0x83608).
unfold hqu_fs in Hf8.
apply (hvfu_fcvt (fx := fx2) W2 regs2 mem2 md2 POST b Hf8 Hb Hz).
intros fx4 regs4 X Hfx4 Hr4 G18.
assert (HM4 : hvc_mid fx4 ly2 S2 W2 regs4 mem2 (with_vm_backing (m_vm_lazy md2) X md2)).
{ apply (hvc_mid_fp _ _ _ _ _ _ _ _ _ X HM Hfx4).
  intros rr Hr. rewrite Hr4. apply getr_other.
  intros ->. revert Hr. unfold HVC_KRB, HVC_KR. cbn [map In].
  intros Hr. repeat (destruct Hr as [Hr | Hr]; [apply (f_equal (@bv_unsigned 5)) in Hr; vm_compute in Hr; discriminate Hr|]).
  destruct Hr. }
apply (hvc_p1 fx4 ly2 S2 W2 regs4 mem2 _ HM4).
- exact G18.
- rewrite Hr4, getr_other; [exact R24|].
  intros Hq. apply (f_equal (@bv_unsigned 5)) in Hq. vm_compute in Hq. discriminate Hq.
- exact C88.
Qed.

End cv.

Theorem hvu_cv_B : @hvu_piece_cv_stmt fx rc SK B MT.
Proof.
unfold hvu_piece_cv_stmt. intros cx POST r ev at0 m HS HRF HTAIL.
unfold hvu_from_CV. intros fx2 ly2 S2 W2 regs2 mem2 md2 kk v ch p b cs keys rf Hcut.
exact (hvc_p0 cx POST r ev at0 m fx2 ly2 S2 W2 regs2 mem2 md2 kk v ch p b cs keys rf HS Hcut HRF HTAIL).
Qed.

End k.

Print Assumptions hvc_c1.
Print Assumptions hvc_c2.
Print Assumptions hvc_c3.
Print Assumptions hvc_c4.
Print Assumptions hvc_c5.
Print Assumptions hvc_c6.
About hvu_cv_B.
Print Assumptions hvu_cv_B.
