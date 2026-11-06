(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheck.v (ck_entry, the code table ck_tbl / ck_wx / ck_segs_low) and
   lib/A/RPgCheckStr.v (rl_cstr_kept) at 77f59d02b01 for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02:
   the half's code table, the entry state of a run that starts at one of its cuts (the registers, the real frame at
   s1 and the role cell as regions), the stack facts of lib/A/RPgSeg.v's rs_pre, the seam between RPgSeg's rs_core and
   lib/A/RPgCSpec.v's callee contracts (rl_pre before a call, rl_post after it), and the strings and cells the callees
   read, carried from the segment's start to a cut (rl_cstr_kept with two worlds and the half's write set). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 7e8cf15c304 (m2_core_step and
   the shape of m2_core_call: a cut's journal-and-frame part across a run of the engine and across a call) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304 (m2f_cut / m2f_exit_mal: a cut's facts carried to a
   state of the arm, every byte outside the arm's write zone and every callee-saved register kept) for
   reac-pw/fuzz_headamp image A: the cut texts are lib/A/HPgSegM.v's hq_cut_RFA and lib/A/HPgM3dBase.v's hv_cut_FA /
   hv_cut_TAIL, the write zone is HPgM3dBase's hv_wz, s4 is not kept (the arm computes the value in it) and the
   float state is related to the cut's by every register but f8 and f10. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): THE FLOAT ARM of M03's
   piece value_nearest in the walk of LLVMFuzzerTestOneInput (0x80bc0), from lib/A/HPgM3dBase.v's cut FA 0x83430 to
   lib/A/HPgSegM.v's cut RFA 0x83454 or HPgM3dBase's cut TAIL 0x83534: hvl_flt_A : hv_piece_flt_stmt.
   proves function LLVMFuzzerTestOneInput (reuse search: at ossv/recipes 2d2ff01bb6f2, read by the released-proof
   index v5 built 2026-10-30T13:16:21Z, no released proof of these pieces; the lookup record is in the PR body).

   THE CODE: the inlined pod_float + pod_nearest(f, 0, 255) of cell_value (pod.h:118-120, 152-171,
   fuzz_headamp.c:105):
     0x83430 sd a3,0x98(s1); the size's check; lw a1 = ent[v].size; bgeu a1,4 -> 0x83490, else RFA 0x83454
     0x83490 the body's check; 0x834a4 flw fs0 = the body word f; 0x834a8 feq.s / 0x834ac beqz -> RFA (NaN)
     0x834b0 flt.s f < -1.0f (fs1) / bnez -> RFA; 0x834b8 flt.s 256.0f (fs2) < f / bnez -> RFA
     0x834c0 fmv.s fa0,fs0; 0x834c4 jal __extendsftf2 (d); 0x834c8 d to R+0x90 / R+0x88; 0x834d0 fcvt.l.s s4 = t
     0x834d4 jal __floatditf (t); 0x834ec jal __subtf3 (s = d - t); 0x834f0 s to R+0x90 / R+0x88;
     0x83500 jal __getf2 (s, 0.5L), 0x83504 bgez -> s4 + 1; 0x83518 jal __lttf2 (s, -0.5L), 0x8351c bgez,
     0x83520 s4 - 1; 0x8352c li a0,0xff; bltu a0,s4 -> RFA, else TAIL 0x83534.

   THE WALK: P1 .. P11, one lemma per stretch, each in continuation form (the next stretch's statement is a
   premise), chained by hvl_from_FA_inst. The engine (HPgM3dBase's hv_run / hv_branch over hv_tbl) runs every
   stretch of integer code; the six float instructions are HPgM3dFp's exact steps (hvf_flw, hvf_feq, hvf_lt1,
   hvf_lt2, hvf_fmv, hvf_fcvt), after each of which the engine starts again with a0 pinned to the literal the
   compare left (hvl_enter_a0); the five soft-float calls are HPgCallsSFI's closed adapters (hsf_*_call). The values
   are HPgM3dVal's: the three tests and the range test are NearVal.hn_bin (hvm_hn_nan / _lo / _hi / _body), the
   three-way rounding is hvm_pnr_eq, and Headamp.cell_value is hvm_cv_float / hvm_cv_small with hvm_hn_nearest.

   THE KIT (Section fa: the cut FA and the segment's start facts):
   - hvl_mid: what every state of the arm keeps from the cut: the journal-and-frame part HPgSeg.hs_core with M03's
     write set, every byte outside HPgM3dBase.hv_wz (the soft-float callees' stack [R - T_SEG_STK, R) and the cells
     R+0x88 .. R+0xa0), the registers s0, s1, s2, s3, s5 .. s11 (every callee-saved register but s4), and every float
     register but f8 and f10 with a zero rounding mode (hvl_fxr);
   - hvl_mid_run / hvl_mid_fp / hvl_mid_call: hvl_mid across a run of the engine that writes only R+0x88 .. R+0xa0,
     across one float step of lib/A/HPgM3dFp.v, and across a soft-float call of lib/A/HPgCallsSFI.v;
   - hvl_cut_RFA / hvl_cut_TAIL: HPgSegM's cut RFA and HPgM3dBase's cut TAIL at such a state, from the cut FA (the
     cells R+0x98 = p, R+0x90 / R+0x88 = the binary128 pair are carried as explicit facts from the engine's region).
   SECTION HYPOTHESES of hvl_flt_A: MTL : ameter_laws MT (the meter's order across a call) and
   ERR : api_env rsegs B (lib/Reusable/YCbq.v: the errno cell lies in the image, below kLowMemEnd, so the arm's
   writes miss it). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require NearVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgCalls HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3dVal HPgM3dFp HPgCallsSF HPgCallsSFI HPgM3dBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== registers and float registers ===================================== *)
(* the registers every state of the arm keeps from the cut FA: the callee-saved ones but s4 (x20) *)
Definition HVL_KR : list Z := [8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].
(* the same with sp, gp and tp, as the engine's register list *)
Definition HVL_KRB : list (bv 5) := map (Z_to_bv 5) (2 :: 3 :: 4 :: HVL_KR).

Lemma hvl_krb : forall q, In q (2 :: 3 :: 4 :: HVL_KR) -> In (Z_to_bv 5 q) HVL_KRB.
Proof. intros q Hq. unfold HVL_KRB. apply in_map. exact Hq. Qed.

(* the float state of a state of the arm against the cut's: every register but f8 and f10 kept, frm = 0 *)
Definition hvl_fxr (fxA fx3 : YK11.FPState) : Prop :=
(forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 ->
 Sem.reg_get (@fp_regs fx3) k = Sem.reg_get (@fp_regs fxA) k) /\ YK0o.frm_zero (@fp_csr fx3).

Lemma hvl_fxr_refl : forall f, YK0o.frm_zero (@fp_csr f) -> hvl_fxr f f.
Proof. intros f Hz. split; [intros k _ _; reflexivity | exact Hz]. Qed.

Lemma hvl_fxr_keep : forall fA f1 f2, hvl_fxr fA f1 -> hd_fxk [] f1 f2 -> hvl_fxr fA f2.
Proof.
intros fA f1 f2 (H1 & _) (H2 & Hz). split; [|exact Hz].
intros k Hk8 Hk10. rewrite (H2 k (fun H => H)). exact (H1 k Hk8 Hk10).
Qed.

Lemma hvl_fxr_set : forall fA f1 (k : Z) (w : word), hvl_fxr fA f1 -> (k = 8 \/ k = 10) ->
hvl_fxr fA (YK11.mkFP (bvmap_set (Z_to_bv 5 k) w (@fp_regs f1)) (@fp_csr f1)).
Proof.
intros fA f1 k w (H1 & Hz) Hk. split; [|exact Hz].
intros k' Hk8 Hk10. cbn [fp_regs].
change (bvmap_set (Z_to_bv 5 k) w (@fp_regs f1)) with (regupd (@fp_regs f1) (Z_to_bv 5 k) w).
rewrite regupd_other; [exact (H1 k' Hk8 Hk10)|].
intros ->. destruct Hk as [-> | ->]; [apply Hk8 | apply Hk10]; reflexivity.
Qed.

(* ===================================== the journal-and-frame part across a step ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis ERR : api_env rsegs B.

(* [RPgM02Base.v m2_core_step] *)
Lemma hvl_core_step : forall (cx : hs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
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
Lemma hvl_hc_core : forall (cx : hs_scx rsegs) sh E ly2 S2 W2 regs2 mem2 md2,
hs_pre rsegs B cx sh -> hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx sh E ly2 S2 W2 regs2 mem2 md2 HP Hcore.
pose proof HP as (_ & Hev & H2 & H3 & H4 & HSe & Hal & Hrsz & Hwin & _).
destruct Hcore as (HJ & Hr234 & _).
cbn [hi_rsz headamp_himg_A] in Hrsz.
split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hr234 2 (or_introl eq_refl))|].
split; [rewrite <- H3; exact (Hr234 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- H4; exact (Hr234 4 (or_intror (or_intror eq_refl)))|].
split; [apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]]|].
split; [exact Hwin | lia].
Qed.

(* ===================================== one cut FA ===================================== *)
Section fa.
Variables (cx : hs_scx rsegs) (POST : world rsegs -> config -> Prop) (r : Model.pod_rec) (ev : Z) (at0 m : nat).
Variables (fx2 : YK11.FPState) (ly2 : alayout) (S2 : astate) (W2 : world rsegs) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model).
Variables (kk : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z).
Hypothesis HS : @hq_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HFA : @hv_cut_FA fx rc SK B MT cx fx2 r at0 m kk v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2.

Definition hvl_R : Z := e_R (x_e rsegs cx).
Definition hvl_a : Z := hv_entA cx m.
Definition hvl_bd : Z := Cursor.rd32 (Model.e_body v).

Lemma hvl_pre : hs_pre rsegs B cx (hi_shA headamp_himg_A).
Proof. exact (proj1 HS). Qed.

(* the stack: R, its window and the allocator's ceiling *)
Lemma hvl_geo :
2 ^ 46 <= hvl_R <= 2 ^ 47 /\ hvl_R mod 32 = 0 /\ hvl_R + 0x1e0 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= hvl_R - T_SEG_STK /\ alloc_ceiling <= hvl_R - T_SEG_STK /\
x_sp0 rsegs cx <= 2 ^ 47 /\ spZ (x_regs rsegs cx) = hvl_R /\ T_SEG_STK = 16384 /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
destruct (hv_stack B cx _ hvl_pre) as (HR & Hal & Hrs & Hwin & Hceil & H46 & H47 & _).
pose proof asan_consts as (C1 & _).
unfold hvl_R. repeat split; try assumption; try lia; reflexivity.
Qed.

(* the cut's parts *)
Lemma hvl_FA_base : @hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2.
Proof. exact (proj1 HFA). Qed.

Definition hvl_LA : list (hd_loc * Z) :=
hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r.
Definition hvl_LK : list (hd_loc * Z) :=
hvl_LA ++ [(LReg 18, hvm_top p); (LReg 21, Z.of_nat m + 2); (LCell XR 0xa0, ch)].

Lemma hvl_FA_at : hs_at_cx rsegs cx W2 mem2 regs2
  (hvl_LA ++ [(LReg 10, hvl_a); (LReg 13, p); (LReg 18, hvm_top p); (LReg 21, Z.of_nat m + 2); (LCell XR 0xa0, ch)]).
Proof. pose proof HFA as (_ & HL & _). unfold hvl_LA, hvl_a. rewrite <- !app_assoc. exact HL. Qed.

Lemma hvl_at_reg : forall q w, In (LReg q, w) (hvl_LA ++
  [(LReg 10, hvl_a); (LReg 13, p); (LReg 18, hvm_top p); (LReg 21, Z.of_nat m + 2); (LCell XR 0xa0, ch)]) ->
getr regs2 (Z_to_bv 5 q) = w64 w.
Proof.
intros q w Hin. pose proof hvl_FA_at as HL. unfold hs_at_cx, hs_at in HL. rewrite Forall_forall in HL.
exact (HL _ Hin).
Qed.

Lemma hvl_at_cell : forall o w, In (LCell XR o, w) (hvl_LA ++
  [(LReg 10, hvl_a); (LReg 13, p); (LReg 18, hvm_top p); (LReg 21, Z.of_nat m + 2); (LCell XR 0xa0, ch)]) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_R + o) 8 (w mod 2 ^ 64).
Proof.
intros o w Hin. pose proof hvl_FA_at as HL. unfold hs_at_cx, hs_at in HL. rewrite Forall_forall in HL.
exact (HL _ Hin).
Qed.

Ltac hvl_in := unfold hvl_LA, hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body; cbn [In app];
  repeat (first [left; reflexivity | right]).

Lemma hvl_FA_regs :
getr regs2 (Z_to_bv 5 9) = w64 hvl_R /\ getr regs2 (Z_to_bv 5 23) = w64 SHADOW_OFF /\
getr regs2 (Z_to_bv 5 10) = w64 hvl_a /\ getr regs2 (Z_to_bv 5 13) = w64 p.
Proof.
split; [apply hvl_at_reg; unfold hvl_R; hvl_in|].
split; [apply hvl_at_reg; hvl_in|].
split; apply hvl_at_reg; hvl_in.
Qed.

Lemma hvl_FA_halves :
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_R + 0xb0) 8 HQ_HALF_HI /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_R + 0xa8) 8 HQ_MHALF_HI.
Proof.
split.
- replace HQ_HALF_HI with (HQ_HALF_HI mod 2 ^ 64) by reflexivity. apply hvl_at_cell. hvl_in.
- replace HQ_MHALF_HI with (HQ_MHALF_HI mod 2 ^ 64) by reflexivity. apply hvl_at_cell. hvl_in.
Qed.

(* the record, the pair and the value entry *)
Lemma hvl_FA_facts :
Model.pod_rec_wf r /\ hq_pair_inv rsegs cx r m kk v cs keys rf /\ Model.ent_wf v /\ (S m < 32)%nat /\
Model.e_type v = Model.POD_FLOAT /\ 0 <= p <= 2 /\ 0 <= ch < Headamp.HA_CHANNELS /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) kk) = Headamp.KCell ch p /\
(p = Headamp.HA_PHANTOM \/ p = Headamp.HA_PAD \/ p = Headamp.HA_SENS).
Proof.
pose proof HS as (_ & _ & Hwf & _).
pose proof HFA as (_ & _ & _ & _ & _ & _ & Hkey & Hty & Hpair & _).
pose proof Hpair as (Hv & _ & Hlen & _).
destruct (Model.ents_wf r Hwf) as (Hle & Hall).
destruct (hvm_key_cell _ _ _ Hkey) as (Hch & Hp).
split; [exact Hwf|]. split; [exact Hpair|].
split; [rewrite Hv; rewrite Forall_forall in Hall; apply Hall; apply nth_In; exact Hlen|].
split; [lia|]. split; [exact Hty|].
split; [destruct Hp as [E | [E | E]]; rewrite E; unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS; lia|].
split; [exact Hch|]. split; [exact Hkey | exact Hp].
Qed.

(* &ent[v]: inside the first block, below the ceiling, in application memory *)
Lemma hvl_ent_geo :
4096 <= hvl_a /\ hvl_a + 16 <= alloc_ceiling /\ (hvl_a + 16 <= kLowShadowBeg \/ kHighMemBeg <= hvl_a).
Proof.
destruct (hv_apart B cx _ hvl_pre) as (_ & Hp0 & Hpc & Happ & _).
pose proof hvl_FA_facts as (_ & _ & _ & Hm & _).
assert (Hps : Layout.PP_SIZE = 19744) by reflexivity.
unfold hvl_a, hv_entA, HQ_ENT0. rewrite Hps in Hpc, Happ.
split; [lia|]. split; [lia|]. destruct Happ as [H|H]; [left; lia | right; lia].
Qed.

Lemma hvl_FA_ent :
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_a + 4) 4 (Model.e_size v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_a + 8) 4 hvl_bd /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF hvl_a 16.
Proof.
pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsz & Hbd & Hra).
split; [exact Hsz|]. split; [exact Hbd | exact Hra].
Qed.

(* ===================================== what every state of the arm keeps ===================================== *)
Definition hvl_mid (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 : Prop :=
hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ hv_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) /\
(forall q, In q HVL_KR -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) /\
hvl_fxr fx2 fx3.

Lemma hvl_mid_FA : hvl_mid fx2 ly2 S2 W2 regs2 mem2 md2.
Proof.
pose proof hvl_FA_base as (Hcore & (_ & Hz) & _).
split; [exact Hcore|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
apply hvl_fxr_refl. exact Hz.
Qed.

(* the cells R+0x88 .. R+0xa0 are M03's own (hi_w3's real-frame cells [R, R+0x120)) *)
Lemma hvl_band_E3 : forall a, hvl_R + 0x88 <= a < hvl_R + 0xa0 -> hq_E3 rsegs B cx a.
Proof.
intros a Ha. left. unfold hd_inw. cbn [hi_w3 headamp_himg_A].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. unfold hvl_R in Ha. lia.
Qed.

(* across a run of the engine: the journal at the run's end, the I/O-equal model, the kept registers and every
   byte outside R+0x88 .. R+0xa0 *)
Lemma hvl_mid_run : forall fx3 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 ->
(forall rr, In rr HVL_KRB -> getr regs4 rr = getr regs3 rr) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R + 0x88 <= a < hvl_R + 0xa0) ->
 aview rsegs (w_H W3) mem4 a = aview rsegs (w_H W3) mem3 a) ->
hvl_mid fx3 ly3 S3 W3 regs4 mem4 md4.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (Hcore & HK & HR & Hfx) HJ4 Hio HR4 HK4.
split.
{ apply (hvl_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regs4 mem4 md4 Hcore HJ4);
  [ intros q Hq; apply HR4; apply hvl_krb; destruct Hq as [-> | [-> | ->]];
    [left | right; left | right; right; left]; reflexivity
  | reflexivity | apply Permutation_refl | exact Hio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ HE. apply HK4; [exact Ha|]. intros Hb. exact (HE (hvl_band_E3 a Hb)). }
split.
{ intros a Ha Hw. rewrite (HK4 a Ha); [exact (HK a Ha Hw)|].
  intros Hb. apply Hw. right. unfold HV_C_HI. unfold hvl_R in Hb. lia. }
split; [|exact Hfx].
intros q Hq. rewrite (HR4 (Z_to_bv 5 q) (hvl_krb q ltac:(right; right; right; exact Hq))). exact (HR q Hq).
Qed.

(* across one float step of HPgM3dFp: the registers but a0 / s4, the memory and the journal are kept; the model is
   its materialized copy *)
Lemma hvl_mid_fp : forall fx3 ly3 S3 W3 regs3 mem3 md3 fx4 regs4 X,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_fxr fx2 fx4 ->
(forall rr, In rr HVL_KRB -> getr regs4 rr = getr regs3 rr) ->
hvl_mid fx4 ly3 S3 W3 regs4 mem3 (with_vm_backing (m_vm_lazy md3) X md3).
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 fx4 regs4 X (Hcore & HK & HR & _) Hfx HR4.
split.
{ apply (hvl_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regs4 mem3 _ Hcore);
  [ exact (ajournal_materialize rsegs B (AR_laws_ok rsegs B) hv_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X (proj1 Hcore))
  | intros q Hq; apply HR4; apply hvl_krb; destruct Hq as [-> | [-> | ->]];
    [left | right; left | right; right; left]; reflexivity
  | reflexivity | apply Permutation_refl | apply hv_same_io_wvb | apply (mo_le_refl MT MTL) |].
  intros a _ _ _. reflexivity. }
split; [exact HK|]. split; [|exact Hfx].
intros q Hq. rewrite (HR4 (Z_to_bv 5 q) (hvl_krb q ltac:(right; right; right; exact Hq))). exact (HR q Hq).
Qed.

(* across a soft-float call (HPgCallsSF's continuation), whose callee writes at most [R - T, R) *)
Lemma hvl_mid_call : forall fx3 ly3 S3 W3 regs3 mem3 md3 fx4 ly4 S4 W4 regs4 mem4 md4 T,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> 0 <= T <= T_SEG_STK -> hd_fxk [] fx3 fx4 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly4 S4 W4 mem4 md4 regs4 hvl_R ->
aregs_preserved regs3 regs4 -> frames S4 = frames S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
same_io md3 md4 -> mo_le MT S3 S4 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R - T <= a < hvl_R) -> aview rsegs (w_H W4) mem4 a = aview rsegs (w_H W3) mem3 a) ->
hvl_mid fx4 ly4 S4 W4 regs4 mem4 md4.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 fx4 ly4 S4 W4 regs4 mem4 md4 T (Hcore & HK & HR & Hfx) HT Hfx4 HC4 Hpres
  Hfr Hperm Hio Hmo HK4.
pose proof hvl_geo as (_ & _ & _ & _ & _ & _ & Hsp & HTS & _).
split.
{ apply (hvl_core_step cx _ ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hcore (proj1 HC4));
  [ intros q Hq; apply Hpres; unfold acallee_saved; lia
  | exact Hfr | exact Hperm | exact Hio | exact Hmo |].
  intros a Ha Hs _. apply HK4; [exact Ha|]. rewrite Hsp in Hs. lia. }
split.
{ intros a Ha Hw. rewrite (HK4 a Ha); [exact (HK a Ha Hw)|].
  intros Hb. apply Hw. left. unfold hvl_R in Hb. lia. }
split; [|exact (hvl_fxr_keep _ _ _ Hfx Hfx4)].
intros q Hq. rewrite (Hpres q); [exact (HR q Hq)|].
unfold HVL_KR in Hq. cbn [In] in Hq. unfold acallee_saved. lia.
Qed.

(* the call adapters' premises at a state of the arm *)
Lemma hvl_mid_hc : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly3 S3 W3 mem3 md3 regs3 hvl_R.
Proof. intros fx3 ly3 S3 W3 regs3 mem3 md3 (Hcore & _). exact (hvl_hc_core cx _ _ _ _ _ _ _ _ hvl_pre Hcore). Qed.

(* a byte below the allocator's ceiling is as at FA *)
Lemma hvl_mid_low : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 (_ & HK & _) a Ha.
pose proof hvl_geo as (_ & _ & _ & _ & _ & _ & _ & _ & Hc).
apply HK; [lia|]. exact (hv_wz_low B cx _ hvl_pre a Ha).
Qed.

Lemma hvl_mid_rom : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> rom_view rsegs W3 mem3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
pose proof hvl_FA_base as (_ & _ & _ & Hrom & _).
pose proof hvl_geo as (_ & _ & _ & _ & _ & _ & _ & _ & Hc).
apply (hm_rom_kept rsegs W2 W3 mem2 mem3 Hrom). intros a (sg & Hin & _ & Hsb).
assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
pose proof (hv_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
apply (hvl_mid_low _ _ _ _ _ _ _ HM). lia.
Qed.

(* the float registers f9 = -1.0f, f18 = 256.0f and the frm = 0 of a state of the arm *)
Lemma hvl_mid_fs : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hq_fs fx3 9 HQ_F32_M1 /\ hq_fs fx3 18 HQ_F32_256 /\ YK0o.frm_zero (@fp_csr fx3) /\ @hq_fxk fx fx3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 (_ & _ & _ & (Hf & Hz)).
pose proof HFA as (Hb & _ & H9 & H18 & _).
pose proof Hb as (_ & (Hk & _) & _).
unfold hq_fs in *.
split; [rewrite (Hf (Z_to_bv 5 9)) by (intros E; vm_compute in E; discriminate E); exact H9|].
split; [rewrite (Hf (Z_to_bv 5 18)) by (intros E; vm_compute in E; discriminate E); exact H18|].
split; [exact Hz|].
split; [|exact Hz].
intros k Hk'. assert (H8 : bv_unsigned k <> 8) by (intros E; apply Hk'; rewrite E; cbn [In]; auto).
assert (H10 : bv_unsigned k <> 10) by (intros E; apply Hk'; rewrite E; cbn [In]; auto).
rewrite (Hf k H8 H10). exact (Hk k Hk').
Qed.

(* ===================================== the cuts at a state of the arm ===================================== *)
Definition hvl_locb (f : hd_loc * Z) : bool :=
match fst f with
| LReg q => existsb (Z.eqb q) HVL_KR
| LCell XR o => ((0 <=? o) && (o + 8 <=? 0x88)) || ((0xa0 <=? o) && (o + 8 <=? 0x200))
| LCell _ _ => false
end.

Lemma hvl_at_kept : forall fx3 ly3 S3 W3 regs3 mem3 md3 L,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
hs_at_cx rsegs cx W2 mem2 regs2 L -> forallb hvl_locb L = true ->
hs_at_cx rsegs cx W3 mem3 regs3 L.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 L (_ & HK & HR & _) HL Hb.
pose proof hvl_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
unfold hs_at_cx, hs_at in *.
apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) L HL).
intros f Hf. pose proof (proj1 (forallb_forall _ _) Hb f Hf) as Hl.
apply (hm_keeps_of rsegs (fun x => ~ (0 <= x < 2 ^ 64) \/ hv_wz cx x)).
- intros x Hx. apply HK; [|intros Hw; apply Hx; right; exact Hw].
  destruct (Z_lt_le_dec x 0) as [Hn|Hn]; [exfalso; apply Hx; left; lia|].
  destruct (Z_lt_le_dec x (2 ^ 64)) as [Hm|Hm]; [lia | exfalso; apply Hx; left; lia].
- destruct f as [[q|b o] w]; cbn [fst hvl_locb] in Hl |- *.
  + apply existsb_exists in Hl as (z & Hz & Hzq). apply Z.eqb_eq in Hzq. subst z. exact (HR q Hz).
  + destruct b; try (cbn in Hl; discriminate Hl).
    change (((0 <=? o) && (o + 8 <=? 0x88)) || ((0xa0 <=? o) && (o + 8 <=? 0x200)) = true) in Hl.
    intros i Hi. cbn [hd_xv]. unfold hv_wz, HV_C_HI.
    unfold hvl_R in H46.
    apply orb_true_iff in Hl as [Hl|Hl]; apply andb_true_iff in Hl as (Hl1 & Hl2);
    apply Z.leb_le in Hl1; apply Z.leb_le in Hl2; lia.
Qed.

Lemma hvl_at_K : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hs_at_cx rsegs cx W3 mem3 regs3 hvl_LK.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
apply (hvl_at_kept _ _ _ _ _ _ _ _ HM); [|reflexivity].
pose proof hvl_FA_at as HL. unfold hs_at_cx, hs_at in HL |- *. unfold hvl_LK.
rewrite Forall_app in HL |- *. destruct HL as (HL1 & HL2). split; [exact HL1|].
rewrite !Forall_cons_iff in HL2. destruct HL2 as (_ & _ & X18 & X21 & Xa0 & _).
repeat apply Forall_cons; try assumption. apply Forall_nil.
Qed.

(* hq_base3 and x at a state of the arm *)
Lemma hvl_base_at : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
@hq_base3 fx rc SK rsegs B MT cx fx3 r hq_shX ly3 S3 W3 regs3 mem3 md3 /\
hq_x_at rsegs cx W3 mem3 cs (keys + 1) rf.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM.
pose proof (hvl_mid_low _ _ _ _ _ _ _ HM) as Kl.
pose proof HM as (Hcore3 & _).
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (_ & _ & _ & Hfxk3).
pose proof hvl_FA_base as (_ & _ & Hfsh & _ & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxat & _).
pose proof HS as (HP & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (hv_apart B cx _ hvl_pre) as (Hppin & Hp0 & Hpc & _ & HF0 & HFc & _).
destruct (hv_blk_low B cx _ _ _ hvl_pre Hpodin) as (_ & Hpod0 & Hpodc).
destruct (hv_blk_low B cx _ _ _ hvl_pre Houtin) as (_ & Hout0 & Houtc).
pose proof asan_consts as (C1 & _).
assert (Hreq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (Hgarr : forall a l, garr8 rsegs (mrestrict (w_H W2) mem2) a (hd_zbytes l) ->
  0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  garr8 rsegs (mrestrict (w_H W3) mem3) a (hd_zbytes l)).
{ intros a l Hg Ha0 Ha1. apply (proj1 (hm_bytes_zbytes rsegs (w_H W3) mem3 a l)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 a l) Hg)|].
  intros y Hy. apply Kl. lia. }
assert (Hcells : Z.of_nat (length (ans_cells (hq_ans rsegs cx r))) <= e_cap (x_e rsegs cx)).
{ pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
    ltac:(lia)) as HO. fold (hq_ans rsegs cx r) in HO.
  apply answer_ok_parts in HO as [[(_ & E2 & _) | (E1 & E2 & _)] _]; [rewrite E2; cbn [length]|]; lia. }
split.
- split; [exact Hcore3|]. split; [exact Hfxk3|].
  split.
  { unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh).
    intros i Hi. rewrite hq_shX_len in Hi. apply Kl.
    assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
    assert (8 * (e_F (x_e rsegs cx) / 8) <= e_F (x_e rsegs cx)) by (apply Z.mul_div_le; lia).
    unfold shadow_addr, SHADOW_OFF. lia. }
  split; [exact (hvl_mid_rom _ _ _ _ _ _ _ HM)|].
  split.
  { unfold hs_pp_at in *. apply Hgarr; [exact Hpp | lia|].
    rewrite (Layout.length_pp_bytes r Hwf). exact Hpc. }
  split.
  { apply Hgarr; [exact Hpod | lia|]. rewrite <- Hlen. pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)). lia. }
  split.
  { apply Hgarr; [exact Hout | lia|]. rewrite length_ha_cells_bytes.
    pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)). lia. }
  split.
  { apply Hgarr; [exact Hres | unfold HQ_RES; lia|]. unfold ans_res_bytes. rewrite length_ha_res_bytes.
    unfold HQ_RES. lia. }
  exists ev2. intros j Hj.
  assert (Hj' : 0 <= Z.of_nat j < 4) by lia.
  rewrite (Kl _ (hv_errno_low B ERR (Z.of_nat j) Hj')). exact (Herr j Hj).
- destruct Hxat as (Hx & Hrest). split; [|exact Hrest].
  destruct Hrest as (HlX & _).
  apply Hgarr; [exact Hx | unfold HQ_XO; lia|].
  rewrite (hq_x_open_len cs (keys + 1) rf HlX). unfold HQ_XO. lia.
Qed.

(* RFA 0x83454 at a state of the arm, when the pair is refused as out of range *)
Lemma hvl_cut_RFA : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE ->
@hq_cut_RFA fx rc SK rsegs B MT cx fx3 r at0 m kk v cs keys rf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM Hcell.
destruct (hvl_base_at _ _ _ _ _ _ _ HM) as (Hb3 & Hx3).
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (H9 & H18 & _).
pose proof (hvl_at_K _ _ _ _ _ _ _ HM) as HK.
pose proof HFA as (_ & _ & _ & _ & Hlive & Hat0 & _ & _ & Hpair & _).
split; [exact Hb3|].
split.
{ unfold hs_at_cx, hs_at in HK |- *. unfold hvl_LK, hvl_LA in HK. rewrite <- !app_assoc in HK.
  rewrite !Forall_app in HK |- *. destruct HK as (K1 & K2 & K3 & K4).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
  rewrite !Forall_cons_iff in K4. destruct K4 as (_ & X21 & _).
  apply Forall_cons; [exact X21 | apply Forall_nil]. }
split; [exact H9|]. split; [exact H18|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hcell|]. split; [exact Hpair | exact Hx3].
Qed.

(* TAIL 0x83534 at a state of the arm: s4 = val, R+0x98 = p *)
Lemma hvl_cut_TAIL : forall fx3 ly3 S3 W3 regs3 mem3 md3 val,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 20) = w64 val ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x98) 8 (p mod 2 ^ 64) ->
Headamp.cell_value v = val -> 0 <= val <= 255 ->
@hv_cut_TAIL fx rc SK B MT cx fx3 r at0 m kk v ch p val cs keys rf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 val HM H20 H98 Hval Hrng.
destruct (hvl_base_at _ _ _ _ _ _ _ HM) as (Hb3 & Hx3).
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (H9 & H18 & _).
pose proof (hvl_at_K _ _ _ _ _ _ _ HM) as HK.
pose proof HFA as (_ & _ & _ & _ & Hlive & Hat0 & Hkey & _ & Hpair & Hcsk & _).
split; [exact Hb3|].
split.
{ unfold hs_at_cx, hs_at in HK |- *. unfold hvl_LK, hvl_LA in HK. rewrite <- !app_assoc in HK.
  rewrite !Forall_app in HK |- *. destruct HK as (K1 & K2 & K3 & K4).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
  rewrite !Forall_cons_iff in K4. destruct K4 as (X18 & X21 & Xa0 & _).
  apply Forall_cons; [exact X18|]. apply Forall_cons; [exact H20|]. apply Forall_cons; [exact X21|].
  apply Forall_cons; [exact H98|]. apply Forall_cons; [exact Xa0 | apply Forall_nil]. }
split; [exact H9|]. split; [exact H18|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hkey|]. split; [exact Hval|]. split; [exact Hrng|].
split; [exact Hpair|]. split; [exact Hcsk | exact Hx3].
Qed.

(* ===================================== the arm's exits and values ===================================== *)
Lemma hvl_R16 : hvl_R mod 16 = 0.
Proof.
pose proof hvl_geo as (_ & Hal & _).
apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]].
Qed.

Hypothesis HRFA : @hq_from_RFA fx rc SK rsegs B MT cx r POST at0 m.
Hypothesis HTAIL : @hv_from_TAIL fx rc SK B MT cx r POST at0 m.

Lemma hvl_go_RFA : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE ->
SRr rsegs W3 (mkCfg (@mkst fx3 regs3 (Z_to_bv 64 0x83454) mem3 (seg_rom rsegs)) md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM Hc.
exact (HRFA fx3 ly3 S3 W3 regs3 mem3 md3 kk v cs keys rf (hvl_cut_RFA fx3 ly3 S3 W3 regs3 mem3 md3 HM Hc)).
Qed.

Lemma hvl_go_TAIL : forall fx3 ly3 S3 W3 regs3 mem3 md3 val,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 20) = w64 val ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x98) 8 (p mod 2 ^ 64) ->
Headamp.cell_value v = val -> 0 <= val <= 255 ->
SRr rsegs W3 (mkCfg (@mkst fx3 regs3 (Z_to_bv 64 0x83534) mem3 (seg_rom rsegs)) md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 val HM H20 H98 Hv Hr.
exact (HTAIL fx3 ly3 S3 W3 regs3 mem3 md3 kk v ch p val cs keys rf
  (hvl_cut_TAIL fx3 ly3 S3 W3 regs3 mem3 md3 val HM H20 H98 Hv Hr)).
Qed.

(* the value: a size below 4 or no nearest byte is a refusal; a nearest byte n is the cell's value *)
Lemma hvl_cell_small : Model.e_size v < 4 -> Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof.
intros Hs. pose proof hvl_FA_facts as (_ & _ & Hvwf & _ & _ & _ & _ & Hkey & _).
apply (hvm_cell_inl kk v ch p Hkey). left. rewrite (hvm_cv_small v Hvwf Hs). lia.
Qed.

Lemma hvl_cell_none : 4 <= Model.e_size v -> NearVal.hn_bin hvl_bd = None ->
Headamp.expect_cell kk v = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof.
intros Hs Hn. pose proof hvl_FA_facts as (_ & _ & Hvwf & _ & Hty & _ & _ & Hkey & _).
apply (hvm_cell_inl kk v ch p Hkey). left. rewrite (hvm_cv_float v Hvwf Hty Hs).
rewrite <- (hvm_hn_nearest _ (Cursor.rd32_range _)). fold hvl_bd. rewrite Hn. lia.
Qed.

Lemma hvl_cell_some : forall n, 4 <= Model.e_size v -> NearVal.hn_bin hvl_bd = Some n ->
Headamp.cell_value v = n /\ 0 <= n <= 255.
Proof.
intros n Hs Hn. pose proof hvl_FA_facts as (_ & _ & Hvwf & _ & Hty & _).
split; [|exact (hvm_hn_range _ _ Hn)].
rewrite (hvm_cv_float v Hvwf Hty Hs). rewrite <- (hvm_hn_nearest _ (Cursor.rd32_range _)). fold hvl_bd.
rewrite Hn. reflexivity.
Qed.

(* ===================================== the engine's helpers ===================================== *)
(* the registers of HVL_KRB a run does not write keep their value *)
Ltac hvl_kept_regs :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) ?E |- _ =>
  let rr := fresh "rr" in let Hr := fresh "Hr" in
  intros rr Hr; exact (YI04.regs_kept_of_st_ok rsegs E ss (restrict H ms) rg ex0 HVL_KRB HS HAE
    ltac:(vm_compute; reflexivity) rr Hr) end.


(* a stored 8-byte cell of the real-frame region at a run's end *)
Lemma hvl_reg_cell : forall E (mm : word -> option byte) lo hi wlo whi (cs0 : list YP09.chunk) off e w,
region_ok rsegs E mm (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs0) ->
In (YP09.mkChunk off (CVal 8 e)) cs0 ->
bv_unsigned (ew E 9) = hvl_R -> sv_denot E e = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
val_mem rsegs mm (hvl_R + off) 8 w.
Proof.
intros E mm lo hi wlo whi cs0 off e w (_ & _ & _ & Hcs) Hin H9 He Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base base_val] in Hc. rewrite H9 in Hc.
change 8%nat with (N.to_nat 8). eapply val_of_chunk_ok; [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.

Lemma hvl_set_get : forall (f : YK11.FPState) k w, Sem.reg_get (@fp_regs (hvf_set k f w)) (Z_to_bv 5 k) = w.
Proof.
intros f k w. unfold hvf_set. cbn [fp_regs].
change (bvmap_set (Z_to_bv 5 k) w (@fp_regs f)) with (regupd (@fp_regs f) (Z_to_bv 5 k) w). apply regupd_same.
Qed.

Ltac hvl_io := first [ apply same_io_refl | apply hv_same_io_wvb
  | (eapply same_io_trans; [| apply hv_same_io_wvb]; hvl_io) ].
(* the goal's machine state, at the pc of the run's last state *)
Ltac hvl_seat pc :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with pc by (vm_compute; reflexivity) end.
(* hvl_mid at a run's last state, from hvl_mid at its first (the run's kept zone lies inside R+0x88 .. R+0xa0) *)
Ltac hvl_mid_after HM HMn :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _ |- _ =>
  assert (HMn := hvl_mid_run _ _ _ _ _ _ _ (ms_regs ms) (ms_mem ms) mdT HM HJ ltac:(hvl_io) ltac:(hvl_kept_regs)
    (fun a Ha Hn => KE a Ha ltac:(cbv beta; first [exact (fun x => x) | lia])))
end.
(* the register r at a run's last state is the atom n of the run's environment *)
Ltac hvl_reg0 r n G :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  assert (G : getr (ms_regs ms) r = ew E n)
  by (rewrite (st_ok_restrict_reg rsegs H E ss ms r HS);
      replace (sr_get (ss_regs ss) r) with (SOff n 0) by (vm_compute; reflexivity);
      cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned) end.
(* the value v of register r at a run's last state, whose engine value is e (tac: U E e = v) *)
Ltac hvl_reg r e v tac G :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  assert (G : getr (ms_regs ms) r = w64 v)
  by (rewrite (st_ok_restrict_reg rsegs H E ss ms r HS);
      replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
      apply hv_denot_of_U; tac) end.


Lemma hvl_krb_not : forall rr, In rr HVL_KRB -> rr <> Z_to_bv 5 10 /\ rr <> Z_to_bv 5 20.
Proof.
unfold HVL_KRB, HVL_KR. cbn [map In]. intros rr Hr.
repeat (destruct Hr as [<- | Hr]; [split; intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz;
  discriminate Hz |]).
destruct Hr.
Qed.

Lemma hvl_fxk_get : forall (f g : YK11.FPState) k, hd_fxk [] f g -> Sem.reg_get (@fp_regs g) k = Sem.reg_get (@fp_regs f) k.
Proof. intros f g k (H & _). exact (H k (fun x => x)). Qed.

Lemma hvl_set_other : forall (f : YK11.FPState) k w (r : bv 5), r <> Z_to_bv 5 k ->
Sem.reg_get (@fp_regs (hvf_set k f w)) r = Sem.reg_get (@fp_regs f) r.
Proof.
intros f k w r0 Hr. unfold hvf_set. cbn [fp_regs].
change (bvmap_set (Z_to_bv 5 k) w (@fp_regs f)) with (regupd (@fp_regs f) (Z_to_bv 5 k) w).
exact (regupd_other _ _ _ _ Hr).
Qed.

(* an entry state with no region and no fact, a0 pinned to the literal c *)
Ltac hvl_enter_a0 HM fxc pc W rg mm c G10 :=
pose proof (proj1 (proj1 HM)) as HJ;
pose proof (hv_entry (fx := fxc) pc [((Z_to_bv 5 10), SLit c)] [] (mkFacts [] [] []) W rg [] mm
  ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
        [ let Hq := fresh "Hq" in intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq
        | rewrite hv_lit; symmetry; exact G10 ])
  eq_refl (Forall_nil _) I ltac:(repeat split)) as HS1;
remember (Ereg rg []) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg rg []) E) by (subst E; apply env_agree_refl);
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W) mm)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mm a = aview rsegs (w_H W) mm a)
  by (intros; reflexivity);
pose proof hv_wx as Hwx; pose proof hv_segs_low as Hsegs; pose proof (AR_laws_ok rsegs B) as LAWS.

(* the float-step stages' registers: a step of HPgM3dFp writes a0 or s4 only *)
Lemma hvl_krb_upd : forall regs (q : Z) w, q = 10 \/ q = 20 ->
forall rr, In rr HVL_KRB -> getr (regupd regs (Z_to_bv 5 q) w) rr = getr regs rr.
Proof.
intros regs q w Hq rr Hr. apply getr_other. destruct (hvl_krb_not rr Hr) as (H1 & H2).
destruct Hq as [-> | ->]; assumption.
Qed.

(* the facts every stage after the `flw` carries *)
Definition hvl_f8 (fx3 : YK11.FPState) : Prop :=
Sem.reg_get (@fp_regs fx3) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 hvl_bd).
Definition hvl_c98 (W3 : world rsegs) (mem3 : word -> option byte) : Prop :=
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x98) 8 (p mod 2 ^ 64).

(* ===================================== P2: 0x834a8 feq.s, 0x834ac beqz -> RFA ===================================== *)
Lemma hvl_p2 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
  fst (fp_eq fmt_single hvl_bd hvl_bd) = true ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_FLT1 regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_FEQ regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM Hf8 C98 Hge.
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (_ & _ & Hz & _).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbdr. fold hvl_bd in Hbdr.
unfold cfg_at. change (w64 HV_FEQ) with (Z_to_bv 64 0x834a8).
apply (hvf_feq (fx := fx3) W3 regs3 mem3 md3 POST hvl_bd Hf8 Hbdr Hz).
intros fx4 regs4 X Hfx4 Hr4 G10.
assert (HM4 : hvl_mid fx4 ly3 S3 W3 regs4 mem3 (with_vm_backing (m_vm_lazy md3) X md3)).
{ apply (hvl_mid_fp _ _ _ _ _ _ _ _ _ X HM); [exact (hvl_fxr_keep _ _ _ (proj2 (proj2 (proj2 HM))) Hfx4)|].
  rewrite Hr4. apply hvl_krb_upd. left; reflexivity. }
assert (Hf8' : hvl_f8 fx4) by (unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx4); exact Hf8).
clear Hr4.
destruct (fst (fp_eq fmt_single hvl_bd hvl_bd)) eqn:Heq; cbn iota in G10.
- (* not a NaN: `beqz` not taken, on to 0x834b0 *)
  hvl_enter_a0 HM4 fx4 0x834ac W3 regs4 mem3 1 G10.
  unfold cfg_at. change (w64 0x834ac) with (Z_to_bv 64 0x834ac).
  hv_run_to hv_awr 0x834b0. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x834b0.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  apply (K fx4 ly3 S3 W3 rg mm d HM5 Hf8'); [|exact Hge | first [exact Heq | reflexivity]];
  unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
  intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0;
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
    apply KE; [pose proof hvl_geo as (H46 & _); unfold hvl_R in *; lia | exact (fun x => x)] end
  end.
- (* a NaN: `beqz` taken, RFA *)
  hvl_enter_a0 HM4 fx4 0x834ac W3 regs4 mem3 0 G10.
  unfold cfg_at. change (w64 0x834ac) with (Z_to_bv 64 0x834ac).
  hv_run_to hv_awr 0x83454. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x83454.
  exact (hvl_go_RFA _ _ _ _ _ _ _ HM5 (hvl_cell_none Hge (hvm_hn_nan _ Heq))).
Qed.

(* ===================================== P3: 0x834b0 flt.s (< -1.0f), 0x834b4 bnez -> RFA ===================================== *)
Lemma hvl_p3 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
  fst (fp_eq fmt_single hvl_bd hvl_bd) = true -> fst (fp_lt fmt_single hvl_bd 0xbf800000) = false ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_FLT2 regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
fst (fp_eq fmt_single hvl_bd hvl_bd) = true ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_FLT1 regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM Hf8 C98 Hge Hq1.
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (H9 & _ & Hz & _).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbdr. fold hvl_bd in Hbdr.
unfold cfg_at. change (w64 HV_FLT1) with (Z_to_bv 64 0x834b0).
apply (hvf_lt1 (fx := fx3) W3 regs3 mem3 md3 POST hvl_bd Hf8 Hbdr H9 Hz).
intros fx4 regs4 X Hfx4 Hr4 G10.
assert (HM4 : hvl_mid fx4 ly3 S3 W3 regs4 mem3 (with_vm_backing (m_vm_lazy md3) X md3)).
{ apply (hvl_mid_fp _ _ _ _ _ _ _ _ _ X HM); [exact (hvl_fxr_keep _ _ _ (proj2 (proj2 (proj2 HM))) Hfx4)|].
  rewrite Hr4. apply hvl_krb_upd. left; reflexivity. }
assert (Hf8' : hvl_f8 fx4) by (unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx4); exact Hf8).
clear Hr4.
destruct (fst (fp_lt fmt_single hvl_bd 0xbf800000)) eqn:Heq; cbn iota in G10.
- (* below -1.0f: `bnez` taken, RFA *)
  hvl_enter_a0 HM4 fx4 0x834b4 W3 regs4 mem3 1 G10.
  unfold cfg_at. change (w64 0x834b4) with (Z_to_bv 64 0x834b4).
  hv_run_to hv_awr 0x83454. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x83454.
  exact (hvl_go_RFA _ _ _ _ _ _ _ HM5 (hvl_cell_none Hge (hvm_hn_lo _ Heq))).
- (* not below: on to 0x834b8 *)
  hvl_enter_a0 HM4 fx4 0x834b4 W3 regs4 mem3 0 G10.
  unfold cfg_at. change (w64 0x834b4) with (Z_to_bv 64 0x834b4).
  hv_run_to hv_awr 0x834b8. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x834b8.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  apply (K fx4 ly3 S3 W3 rg mm d HM5 Hf8'); [|exact Hge | exact Hq1 | first [exact Heq | reflexivity]];
  unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
  intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0;
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
    apply KE; [pose proof hvl_geo as (H46 & _); unfold hvl_R in *; lia | exact (fun x => x)] end
  end.
Qed.

(* ===================================== P4: 0x834b8 flt.s (256.0f <), 0x834bc bnez -> RFA ===================================== *)
Lemma hvl_p4 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
  fst (fp_eq fmt_single hvl_bd hvl_bd) = true -> fst (fp_lt fmt_single hvl_bd 0xbf800000) = false ->
  fst (fp_lt fmt_single 0x43800000 hvl_bd) = false ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_FMV regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
fst (fp_eq fmt_single hvl_bd hvl_bd) = true -> fst (fp_lt fmt_single hvl_bd 0xbf800000) = false ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_FLT2 regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM Hf8 C98 Hge Hq1 Hq2.
pose proof (hvl_mid_fs _ _ _ _ _ _ _ HM) as (_ & H18 & Hz & _).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbdr. fold hvl_bd in Hbdr.
unfold cfg_at. change (w64 HV_FLT2) with (Z_to_bv 64 0x834b8).
apply (hvf_lt2 (fx := fx3) W3 regs3 mem3 md3 POST hvl_bd Hf8 Hbdr H18 Hz).
intros fx4 regs4 X Hfx4 Hr4 G10.
assert (HM4 : hvl_mid fx4 ly3 S3 W3 regs4 mem3 (with_vm_backing (m_vm_lazy md3) X md3)).
{ apply (hvl_mid_fp _ _ _ _ _ _ _ _ _ X HM); [exact (hvl_fxr_keep _ _ _ (proj2 (proj2 (proj2 HM))) Hfx4)|].
  rewrite Hr4. apply hvl_krb_upd. left; reflexivity. }
assert (Hf8' : hvl_f8 fx4) by (unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx4); exact Hf8).
clear Hr4.
destruct (fst (fp_lt fmt_single 0x43800000 hvl_bd)) eqn:Heq; cbn iota in G10.
- (* above 256.0f: `bnez` taken, RFA *)
  hvl_enter_a0 HM4 fx4 0x834bc W3 regs4 mem3 1 G10.
  unfold cfg_at. change (w64 0x834bc) with (Z_to_bv 64 0x834bc).
  hv_run_to hv_awr 0x83454. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x83454.
  exact (hvl_go_RFA _ _ _ _ _ _ _ HM5 (hvl_cell_none Hge (hvm_hn_hi _ Heq))).
- (* in range: on to 0x834c0 *)
  hvl_enter_a0 HM4 fx4 0x834bc W3 regs4 mem3 0 G10.
  unfold cfg_at. change (w64 0x834bc) with (Z_to_bv 64 0x834bc).
  hv_run_to hv_awr 0x834c0. hv_keep hv_kwr.
  hvl_mid_after HM4 HM5.
  hvl_seat 0x834c0.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  apply (K fx4 ly3 S3 W3 rg mm d HM5 Hf8'); [|exact Hge | exact Hq1 | exact Hq2 | first [exact Heq | reflexivity]];
  unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
  intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0;
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
    apply KE; [pose proof hvl_geo as (H46 & _); unfold hvl_R in *; lia | exact (fun x => x)] end
  end.
Qed.

(* the binary32 tests' outcome on the way to the conversions *)
Definition hvl_ok : Prop :=
fst (fp_eq fmt_single hvl_bd hvl_bd) = true /\ fst (fp_lt fmt_single hvl_bd 0xbf800000) = false /\
fst (fp_lt fmt_single 0x43800000 hvl_bd) = false.
Definition hvl_d : Z := C_extendsftf2.f128_of_f32 hvl_bd.

(* ===================================== P5: 0x834c0 fmv.s, 0x834c4 jal __extendsftf2 ===================================== *)
Lemma hvl_p5 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
  getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_d) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_d) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_EXTR regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v ->
fst (fp_eq fmt_single hvl_bd hvl_bd) = true -> fst (fp_lt fmt_single hvl_bd 0xbf800000) = false ->
fst (fp_lt fmt_single 0x43800000 hvl_bd) = false ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_FMV regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM Hf8 C98 Hge Hq1 Hq2 Hq3.
unfold cfg_at. change (w64 HV_FMV) with (Z_to_bv 64 0x834c0).
apply (hvf_fmv (fx := fx3) W3 regs3 mem3 md3 POST hvl_bd Hf8). intros X.
assert (HM4 := hvl_mid_fp _ _ _ _ _ _ _ (hvf_set 10 fx3 (Sem.nan_box (Z_to_bv 32 hvl_bd))) regs3 X HM
  ltac:(apply hvl_fxr_set; [exact (proj2 (proj2 (proj2 HM))) | right; reflexivity]) ltac:(intros; reflexivity)).
pose proof (proj1 (proj1 HM4)) as HJ.
pose proof (hv_entry (fx := hvf_set 10 fx3 (Sem.nan_box (Z_to_bv 32 hvl_bd))) 0x834c4 [] [] (mkFacts [] [] []) W3 regs3 []
  mem3 (Forall_nil _) eq_refl (Forall_nil _) I ltac:(repeat split)) as HS1.
remember (Ereg regs3 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 0x834c4) with (Z_to_bv 64 0x834c4).
hv_run hv_awr. hv_keep hv_kwr.
hvl_mid_after HM4 HM5.
hvl_reg (Z_to_bv 5 1) (SLit 537800) RA_SF_EXT ltac:(rewrite U_lit by lia; reflexivity) G1.
hvl_seat A_SF_EXT.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hsf_extendsftf2_call (fx := hvf_set 10 fx3 (Sem.nan_box (Z_to_bv 32 hvl_bd))) B MT MTL POST
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mm d rg hvl_R (NearVal.fbox hvl_bd)
    (hvl_mid_hc _ _ _ _ _ _ _ HM5) G1 (f_equal (@bv_unsigned 64) (hvl_set_get fx3 10 (Sem.nan_box (Z_to_bv 32 hvl_bd)))) (hvl_mid_rom _ _ _ _ _ _ _ HM5)
    (proj2 (proj2 (proj2 (proj2 HM5)))));
  intros W4 fx6 ly4 S4 regs4 mem4 md4 Hle Hfx6 HC4 Hpres Hfr Hperm Hio Hmo Hkeep Hrom4 E10 E11;
  assert (HM6 := hvl_mid_call _ _ _ _ _ _ _ fx6 ly4 S4 W4 regs4 mem4 md4 0 HM5 ltac:(rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hvl_geo)))))))); lia)
    Hfx6 HC4 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha));
  rewrite hvm_f128_fbox in E10, E11 by exact (Cursor.rd32_range _);
  apply (K fx6 ly4 S4 W4 regs4 mem4 md4 HM6);
  [ unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx6), hvl_set_other; [exact Hf8|];
    let Hq := fresh "Hq" in intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq
  | unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W4) mem3 mem4 _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; pose proof hvl_geo as (H46 & _); unfold hvl_R in *;
    rewrite Hkeep by lia; apply KE; [lia | exact (fun x => x)]
  | exact Hge
  | exact (conj Hq1 (conj Hq2 Hq3))
  | exact E10
  | exact E11 ]
  end
end.
Qed.

Definition hvl_t : Z := NearVal.pn_t hvl_bd.
Definition hvl_fd : Z := C_floatditf.f128_of_i64 hvl_t.
Definition hvl_facts9 : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Lemma hvl_facts9_ok : forall E, bv_unsigned (ew E 9) = hvl_R -> facts_ok E hvl_facts9.
Proof.
intros E H9. pose proof hvl_geo as (H46 & _). pose proof hvl_R16 as Hal.
split; [|split; [exact I | exact I]]. cbn [hvl_facts9 f_atoms atoms_ok]. unfold afact_ok.
cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 4) with 16. repeat split; lia.
Qed.
(* the frame region over [R + lo, R + hi), writable on [R + wlo, R + whi), at a state of the arm *)
Lemma hvl_frame_ok : forall fx3 ly3 S3 W3 regs3 mem3 md3 E lo hi wlo whi cs0,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> bv_unsigned (ew E 9) = hvl_R ->
0 <= lo -> hi <= 0x1e0 -> (wlo < whi -> 0 <= wlo /\ whi <= 0x1e0) ->
Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W3) mem3) hvl_R) cs0 ->
region_ok rsegs E (mrestrict (w_H W3) mem3) (hv_frame lo hi wlo whi cs0).
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 E lo hi wlo whi cs0 HM H9 Hlo Hhi Hw Hcs.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof (proj1 (proj1 HM)) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
apply (hv_frame_ok E W3 mem3 hvl_R (x_STK rsegs cx) (x_sp0 rsegs cx) lo hi wlo whi cs0 H9);
  [lia | lia | exact Hpres | intros Hlt; destruct (Hw Hlt); split; lia | exact Hcs].
Qed.

(* a real-frame cell outside hv_wz, from FA to a state of the arm *)
Lemma hvl_mid_cell : forall fx3 ly3 S3 W3 regs3 mem3 md3 o w,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> 0xa0 <= o <= 0x1d8 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (hvl_R + o) 8 w -> val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + o) 8 w.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 o w (_ & HK & _) Ho Hv.
pose proof hvl_geo as (H46 & _ & _ & _ & _ & _ & _ & HTS & _).
apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ 8 _); [|exact Hv].
intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0. apply HK; [lia|]. unfold hv_wz, HV_C_HI. unfold hvl_R in *. lia.
Qed.

Lemma hvl_soff : forall E n z c, ew E n = w64 z -> sv_denot E (SOff n c) = w64 (z + c).
Proof.
intros E n z c H. cbn [sv_denot]. rewrite H. unfold w64.
rewrite <- (HPgSteps.Z_to_bv_mod64 (bv_unsigned (Z_to_bv 64 z) + c)), <- (HPgSteps.Z_to_bv_mod64 (z + c)).
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.

Lemma hvl_ge3 : forall a b, SF.f128_ge a b = -1 \/ SF.f128_ge a b = 0 \/ SF.f128_ge a b = 1.
Proof.
intros a b. unfold SF.f128_ge, SoftFloat.nez64, SoftFloat.b2z. cbv zeta.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; auto.
Qed.
Lemma hvl_le3 : forall a b, SF.f128_le a b = -1 \/ SF.f128_le a b = 0 \/ SF.f128_le a b = 1.
Proof.
intros a b. unfold SF.f128_le, SoftFloat.nez64, SoftFloat.b2z. cbv zeta.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; auto.
Qed.

Definition hvl_s : Z := SF.f128_sub hvl_d hvl_fd.

Definition hvl_g : Z := SF.f128_ge hvl_s NearSF.HALF_128.
Definition hvl_l : Z := SF.f128_le hvl_s NearSF.MHALF_128.

Lemma hvl_half_words : 0 + 2 ^ 64 * HQ_HALF_HI = NearSF.HALF_128 /\ 0 + 2 ^ 64 * HQ_MHALF_HI = NearSF.MHALF_128.
Proof.
destruct hvm_half_rng as (Hr1 & Hr2 & L1 & L2 & H1 & H2).
split.
- rewrite <- (hvm_w128 _ Hr1), L1, H1. reflexivity.
- rewrite <- (hvm_w128 _ Hr2), L2, H2. reflexivity.
Qed.



(* ===================================== P11: 0x8352c li a0,0xff; bltu a0,s4 -> RFA / TAIL ===================================== *)
Lemma hvl_p11 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
getr regs3 (Z_to_bv 5 20) = w64 (NearVal.pn_r hvl_bd) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_JOIN regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM C98 Hge (Hq1 & Hq2 & Hq3) A20.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
set (rv := NearVal.pn_r hvl_bd mod 2 ^ 64).
assert (Hrv : 0 <= rv < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (E20 : ew (Ereg regs3 []) 20 = Z_to_bv 64 rv).
{ rewrite (ew_Ereg_nat regs3 [] 20 (Z_to_bv 5 20) eq_refl), A20. unfold rv, w64. symmetry. apply HPgSteps.Z_to_bv_mod64. }
assert (Hhn := hvm_hn_body _ Hq1 Hq2 Hq3). fold rv in Hhn.
pose proof (proj1 (proj1 HM)) as HJ.
pose proof (hv_entry (fx := fx3) 0x8352c [] [] (mkFacts [] [] []) W3 regs3 [] mem3
  (Forall_nil _) eq_refl (Forall_nil _) I ltac:(repeat split)) as HS1.
remember (Ereg regs3 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 HV_JOIN) with (Z_to_bv 64 0x8352c).
hv_run hv_awr. hv_keep hv_kwr.
hv_branch Hb.
all: rewrite branch_ltu_U, U_lit, (hv_U_atom E 20 rv E20 Hrv) in Hb by lia.
- (* 255 < r: RFA *)
  hv_run_to hv_awr 0x83454. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_seat 0x83454.
  rewrite Hb in Hhn.
  exact (hvl_go_RFA _ _ _ _ _ _ _ HM4 (hvl_cell_none Hge Hhn)).
- (* r <= 255: TAIL *)
  hv_run_to hv_awr 0x83534. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_reg (Z_to_bv 5 20) (SOff 20 0) rv ltac:(apply hv_U_atom; [exact E20 | exact Hrv]) G20.
  rewrite Hb in Hhn.
  destruct (hvl_cell_some rv Hge Hhn) as (Hcv & Hcr).
  hvl_seat 0x83534.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_go_TAIL _ _ _ _ _ _ _ rv HM4 G20); [|exact Hcv | exact Hcr];
  unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
  intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  end end.
Qed.

Lemma hvl_pnr : NearVal.pn_r hvl_bd = (if 0 <=? hvl_g then hvl_t + 1 else if hvl_l <? 0 then hvl_t - 1 else hvl_t).
Proof. exact (hvm_pnr_eq hvl_bd (Cursor.rd32_range _)). Qed.

(* ===================================== P10: 0x8351c bgez after __lttf2 ===================================== *)
Ltac hvl_regs r e G :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  assert (G : getr (ms_regs ms) r = sv_denot E e)
  by (rewrite (st_ok_restrict_reg rsegs H E ss ms r HS);
      replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity); reflexivity) end.

Lemma hvl_p10 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok -> hvl_g < 0 ->
getr regs3 (Z_to_bv 5 10) = w64 hvl_l -> getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_LTR regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM C98 Hge Hok Hg A10 A20.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
assert (E20 : ew (Ereg regs3 []) 20 = w64 hvl_t)
  by (rewrite (ew_Ereg_nat regs3 [] 20 (Z_to_bv 5 20) eq_refl); exact A20).
assert (Hg0 : (0 <=? hvl_g) = false) by (apply Z.leb_gt; exact Hg).
destruct (hvl_le3 hvl_s NearSF.MHALF_128) as [Hl | [Hl | Hl]]; fold hvl_l in Hl.
- (* l = -1: frac < -1/2, s4 - 1 *)
  rewrite Hl in A10.
  hvl_enter_a0 HM fx3 0x8351c W3 regs3 mem3 (-1) A10.
  unfold cfg_at. change (w64 HV_LTR) with (Z_to_bv 64 0x8351c).
  hv_run_to hv_awr 0x8352c. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_regs (Z_to_bv 5 20) (SOff 20 (-1)) G20.
  hvl_seat 0x8352c.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_p11 _ _ _ _ rg mm d HM4); [ | exact Hge | exact Hok | ];
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  | rewrite G20, (hvl_soff _ 20 hvl_t (-1) E20), hvl_pnr, Hg0, Hl; reflexivity ]
  end end.
- (* l = 0: frac >= -1/2, s4 *)
  rewrite Hl in A10.
  hvl_enter_a0 HM fx3 0x8351c W3 regs3 mem3 (0) A10.
  unfold cfg_at. change (w64 HV_LTR) with (Z_to_bv 64 0x8351c).
  hv_run_to hv_awr 0x8352c. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_reg0 (Z_to_bv 5 20) 20%nat G20.
  hvl_seat 0x8352c.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_p11 _ _ _ _ rg mm d HM4); [ | exact Hge | exact Hok | ];
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  | rewrite G20, E20, hvl_pnr, Hg0, Hl; reflexivity ]
  end end.
- (* l = 1: frac >= -1/2, s4 *)
  rewrite Hl in A10.
  hvl_enter_a0 HM fx3 0x8351c W3 regs3 mem3 (1) A10.
  unfold cfg_at. change (w64 HV_LTR) with (Z_to_bv 64 0x8351c).
  hv_run_to hv_awr 0x8352c. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_reg0 (Z_to_bv 5 20) 20%nat G20.
  hvl_seat 0x8352c.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_p11 _ _ _ _ rg mm d HM4); [ | exact Hge | exact Hok | ];
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  | rewrite G20, E20, hvl_pnr, Hg0, Hl; reflexivity ]
  end end.
Qed.

(* ===================================== P9: 0x83504 bgez after __getf2; else jal __lttf2 ===================================== *)
Lemma hvl_p9 : forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
getr regs3 (Z_to_bv 5 10) = w64 hvl_g -> getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x90) 8 (SF.lo64 hvl_s) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x88) 8 (SF.hi64 hvl_s) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_GER regs3 mem3 md3) POST.
Proof.
intros fx3 ly3 S3 W3 regs3 mem3 md3 HM C98 Hge Hok A10 A20 C90 C88.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof (HM) as (_ & _ & HR3 & _).
destruct (hvl_ge3 hvl_s NearSF.HALF_128) as [Hg | [Hg | Hg]]; fold hvl_g in Hg.
- (* g = -1: frac < 1/2, the call of __lttf2 *)
  rewrite Hg in A10.
  pose proof (hvl_mid_cell _ _ _ _ _ _ _ 0xa8 _ HM ltac:(lia) (proj2 hvl_FA_halves)) as Ca8.
  set (extra := [Z_to_bv 64 (SF.lo64 hvl_s); Z_to_bv 64 (SF.hi64 hvl_s); Z_to_bv 64 HQ_MHALF_HI] : list word).
  assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = hvl_R).
  { rewrite (ew_Ereg_nat regs3 extra 9 (Z_to_bv 5 9) eq_refl), (HR3 9 ltac:(cbn; tauto)), (proj1 hvl_FA_regs).
    unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew (Ereg regs3 extra) 32 = Z_to_bv 64 (SF.lo64 hvl_s))
    by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew (Ereg regs3 extra) 33 = Z_to_bv 64 (SF.hi64 hvl_s))
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew (Ereg regs3 extra) 34 = Z_to_bv 64 HQ_MHALF_HI)
    by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E20 : ew (Ereg regs3 extra) 20 = w64 hvl_t)
    by (rewrite (ew_Ereg_nat regs3 extra 20 (Z_to_bv 5 20) eq_refl); exact A20).
  pose proof (proj1 (proj1 HM)) as HJ.
  pose proof (hv_entry (fx := fx3) 0x83504 [((Z_to_bv 5 10), SLit (-1))]
    [hv_frame 0x88 0xb0 0 0 [YP09.mkChunk 0x88 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 32 0));
                             YP09.mkChunk 0xa8 (CVal 8 (SOff 34 0))]]
    hvl_facts9 W3 regs3 extra mem3
    ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
          [ let Hq := fresh "Hq" in intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq
          | rewrite hv_lit; symmetry; exact A10 ])
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [|apply Forall_nil];
      apply (hvl_frame_ok _ _ _ _ _ _ _ _ 0x88 0xb0 0 0 _ HM E9 ltac:(lia) ltac:(lia) ltac:(intros; lia));
      apply Forall_cons;
      [ apply (chunk_ok_val rsegs _ _ hvl_R 0x88 8 (SOff 33 0) (SF.hi64 hvl_s));
        [ apply hv_denot_of_U; apply hv_U_atom; [exact E33 | apply hvm_hi64_rng] | cbn; apply hvm_hi64_rng | cbn; lia
        | exact C88 ]
      | apply Forall_cons;
        [ apply (chunk_ok_val rsegs _ _ hvl_R 0x90 8 (SOff 32 0) (SF.lo64 hvl_s));
          [ apply hv_denot_of_U; apply hv_U_atom; [exact E32 | apply hvm_lo64_rng] | cbn; apply hvm_lo64_rng
          | cbn; lia | exact C90 ]
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val rsegs _ _ hvl_R 0xa8 8 (SOff 34 0) HQ_MHALF_HI);
          [ apply hv_denot_of_U; apply hv_U_atom; [exact E34 | unfold HQ_MHALF_HI; lia] | cbn; unfold HQ_MHALF_HI; lia
          | cbn; lia | exact Ca8 ] ] ])
    ltac:(cbn; repeat split; try exact I) (hvl_facts9_ok _ E9)) as HS1.
  remember (Ereg regs3 extra) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
    by (intros; reflexivity).
  pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
  unfold cfg_at. change (w64 HV_GER) with (Z_to_bv 64 0x83504).
  hv_run hv_awr. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_reg (Z_to_bv 5 1) (SLit 537884) RA_SF_LT ltac:(rewrite U_lit by lia; reflexivity) G1.
  hvl_reg (Z_to_bv 5 10) (SOff 32 0) (SF.lo64 hvl_s) ltac:(apply hv_U_atom; [exact E32 | apply hvm_lo64_rng]) G10.
  hvl_reg (Z_to_bv 5 11) (SOff 33 0) (SF.hi64 hvl_s) ltac:(apply hv_U_atom; [exact E33 | apply hvm_hi64_rng]) G11.
  hvl_reg (Z_to_bv 5 12) (SLit 0) 0 ltac:(rewrite U_lit by lia; reflexivity) G12.
  hvl_reg (Z_to_bv 5 13) (SOff 34 0) HQ_MHALF_HI ltac:(apply hv_U_atom; [exact E34 | unfold HQ_MHALF_HI; lia]) G13.
  hvl_reg0 (Z_to_bv 5 20) 20%nat G20. rewrite E20 in G20.
  hvl_seat A_SF_LT.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
    apply (hsf_lttf2_call (fx := fx3) B MT MTL POST
      (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
      (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mm d rg hvl_R
      (SF.lo64 hvl_s) (SF.hi64 hvl_s) 0 HQ_MHALF_HI
      (hvl_mid_hc _ _ _ _ _ _ _ HM4) G1 G10 G11 G12 G13 (hvm_lo64_rng _) (hvm_hi64_rng _) ltac:(lia)
      ltac:(unfold HQ_MHALF_HI; lia) (hvl_mid_rom _ _ _ _ _ _ _ HM4) (proj2 (proj2 (proj2 (proj2 HM4)))));
    intros W4 fx4 ly4 S4 regs4 mem4 md4 Hle Hfx4 HC4 Hpres Hfr Hperm Hio Hmo Hkeep Hrom4 R10;
    assert (HM5 := hvl_mid_call _ _ _ _ _ _ _ fx4 ly4 S4 W4 regs4 mem4 md4 0 HM4 ltac:(lia)
      Hfx4 HC4 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha));
    rewrite (hvm_w128 hvl_s (hvm_sub_range _ _)), (proj2 hvl_half_words) in R10;
    apply (hvl_p10 fx4 ly4 S4 W4 regs4 mem4 md4 HM5);
    [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W4) mem3 mem4 _ 8 _); [|exact C98];
      intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; unfold hvl_R in *;
      rewrite Hkeep by lia; apply KE; [lia | exact (fun x => x)]
    | exact Hge
    | exact Hok
    | lia
    | exact R10
    | rewrite (Hpres 20 ltac:(unfold acallee_saved; lia)); exact G20 ]
  end end.
- (* g = 0: frac >= 1/2, s4 + 1 *)
  rewrite Hg in A10.
  assert (E20 : ew (Ereg regs3 []) 20 = w64 hvl_t)
    by (rewrite (ew_Ereg_nat regs3 [] 20 (Z_to_bv 5 20) eq_refl); exact A20).
  hvl_enter_a0 HM fx3 0x83504 W3 regs3 mem3 (0) A10.
  unfold cfg_at. change (w64 HV_GER) with (Z_to_bv 64 0x83504).
  hv_run_to hv_awr 0x8352c. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_regs (Z_to_bv 5 20) (SOff 20 1) G20.
  hvl_seat 0x8352c.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_p11 _ _ _ _ rg mm d HM4); [ | exact Hge | exact Hok | ];
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  | rewrite G20, (hvl_soff _ 20 hvl_t 1 E20), hvl_pnr, Hg; reflexivity ]
  end end.
- (* g = 1: frac >= 1/2, s4 + 1 *)
  rewrite Hg in A10.
  assert (E20 : ew (Ereg regs3 []) 20 = w64 hvl_t)
    by (rewrite (ew_Ereg_nat regs3 [] 20 (Z_to_bv 5 20) eq_refl); exact A20).
  hvl_enter_a0 HM fx3 0x83504 W3 regs3 mem3 (1) A10.
  unfold cfg_at. change (w64 HV_GER) with (Z_to_bv 64 0x83504).
  hv_run_to hv_awr 0x8352c. hv_keep hv_kwr.
  hvl_mid_after HM HM4.
  hvl_regs (Z_to_bv 5 20) (SOff 20 1) G20.
  hvl_seat 0x8352c.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hvl_p11 _ _ _ _ rg mm d HM4); [ | exact Hge | exact Hok | ];
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 mm _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply KE; [unfold hvl_R in *; lia | exact (fun x => x)]
  | rewrite G20, (hvl_soff _ 20 hvl_t 1 E20), hvl_pnr, Hg; reflexivity ]
  end end.
Qed.

(* ===================================== P8: 0x834f0 the two stores of s, jal __getf2 ===================================== *)
Lemma hvl_p8 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
  getr regs3 (Z_to_bv 5 10) = w64 hvl_g -> getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x90) 8 (SF.lo64 hvl_s) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x88) 8 (SF.hi64 hvl_s) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_GER regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_s) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_s) ->
getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_SUBR regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM C98 Hge Hok A10 A11 A20.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof (HM) as (_ & _ & HR3 & _).
pose proof (hvl_mid_cell _ _ _ _ _ _ _ 0xb0 _ HM ltac:(lia) (proj1 hvl_FA_halves)) as Cb0.
set (extra := [Z_to_bv 64 HQ_HALF_HI] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = hvl_R).
{ rewrite (ew_Ereg_nat regs3 extra 9 (Z_to_bv 5 9) eq_refl), (HR3 9 ltac:(cbn; tauto)), (proj1 hvl_FA_regs).
  unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs3 extra) 32 = Z_to_bv 64 HQ_HALF_HI)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 (SF.lo64 hvl_s))
  by (rewrite (ew_Ereg_nat regs3 extra 10 (Z_to_bv 5 10) eq_refl); exact A10).
assert (E11 : ew (Ereg regs3 extra) 11 = Z_to_bv 64 (SF.hi64 hvl_s))
  by (rewrite (ew_Ereg_nat regs3 extra 11 (Z_to_bv 5 11) eq_refl); exact A11).
assert (E20 : ew (Ereg regs3 extra) 20 = w64 hvl_t)
  by (rewrite (ew_Ereg_nat regs3 extra 20 (Z_to_bv 5 20) eq_refl); exact A20).
pose proof (proj1 (proj1 HM)) as HJ.
pose proof (hv_entry (fx := fx3) 0x834f0 []
  [hv_frame 0x88 0xb8 0x88 0x98 [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))]]
  hvl_facts9 W3 regs3 extra mem3 (Forall_nil _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [|apply Forall_nil];
    apply (hvl_frame_ok _ _ _ _ _ _ _ _ 0x88 0xb8 0x88 0x98 _ HM E9 ltac:(lia) ltac:(lia) ltac:(intros; lia));
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val rsegs _ _ hvl_R 0xb0 8 (SOff 32 0) HQ_HALF_HI);
    [ apply hv_denot_of_U; apply hv_U_atom; [exact E32 | unfold HQ_HALF_HI; lia] | cbn; unfold HQ_HALF_HI; lia
    | cbn; lia | exact Cb0 ])
  ltac:(cbn; repeat split; try exact I) (hvl_facts9_ok _ E9)) as HS1.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R + 0x88 <= a < hvl_R + 0x98) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a) by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 HV_SUBR) with (Z_to_bv 64 0x834f0).
hv_run hv_awr. hv_keep hv_kwr.
hvl_mid_after HM HM4.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  pose proof (YN0d.st_ok_region rsegs E ss (restrict H ms) 0
    (YP09.mkRegion (Some 9%nat) 136 184 136 152
      [YP09.mkChunk 136 (CVal 8 (SOff 11 0)); YP09.mkChunk 144 (CVal 8 (SOff 10 0));
       YP09.mkChunk 176 (CVal 8 (SOff 32 0))]) HS
    ltac:(vm_compute; reflexivity)) as HRg;
  assert (C90 : val_mem rsegs (mrestrict H (ms_mem ms)) (hvl_R + 0x90) 8 (SF.lo64 hvl_s))
  by (apply (hvl_reg_cell E _ 136 184 136 152 _ 144 (SOff 10 0) _ HRg ltac:(right; left; reflexivity) E9);
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E10 | apply hvm_lo64_rng] | apply hvm_lo64_rng ]);
  assert (C88 : val_mem rsegs (mrestrict H (ms_mem ms)) (hvl_R + 0x88) 8 (SF.hi64 hvl_s))
  by (apply (hvl_reg_cell E _ 136 184 136 152 _ 136 (SOff 11 0) _ HRg ltac:(left; reflexivity) E9);
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E11 | apply hvm_hi64_rng] | apply hvm_hi64_rng ]);
  assert (C98' : hvl_c98 W3 (ms_mem ms))
  by (unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 (ms_mem ms) _ 8 _); [|exact C98];
      intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0;
      lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ms) a = _ |- _ => apply KE; lia end)
end.
hvl_reg (Z_to_bv 5 1) (SLit 537860) RA_SF_GE ltac:(rewrite U_lit by lia; reflexivity) G1.
hvl_reg0 (Z_to_bv 5 10) 10%nat G10. rewrite E10 in G10.
hvl_reg0 (Z_to_bv 5 11) 11%nat G11. rewrite E11 in G11.
hvl_reg (Z_to_bv 5 12) (SLit 0) 0 ltac:(rewrite U_lit by lia; reflexivity) G12.
hvl_reg (Z_to_bv 5 13) (SOff 32 0) HQ_HALF_HI ltac:(apply hv_U_atom; [exact E32 | unfold HQ_HALF_HI; lia]) G13.
hvl_reg0 (Z_to_bv 5 20) 20%nat G20. rewrite E20 in G20.
hvl_seat A_SF_GE.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  apply (hsf_getf2_call (fx := fx3) B MT MTL POST
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mm d rg hvl_R
    (SF.lo64 hvl_s) (SF.hi64 hvl_s) 0 HQ_HALF_HI
    (hvl_mid_hc _ _ _ _ _ _ _ HM4) G1 G10 G11 G12 G13 (hvm_lo64_rng _) (hvm_hi64_rng _) ltac:(lia)
    ltac:(unfold HQ_HALF_HI; lia) (hvl_mid_rom _ _ _ _ _ _ _ HM4) (proj2 (proj2 (proj2 (proj2 HM4)))));
  intros W4 fx4 ly4 S4 regs4 mem4 md4 Hle Hfx4 HC4 Hpres Hfr Hperm Hio Hmo Hkeep Hrom4 R10;
  assert (HM5 := hvl_mid_call _ _ _ _ _ _ _ fx4 ly4 S4 W4 regs4 mem4 md4 0 HM4 ltac:(lia)
    Hfx4 HC4 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha));
  rewrite (hvm_w128 hvl_s (hvm_sub_range _ _)), (proj1 hvl_half_words) in R10;
  apply (K fx4 ly4 S4 W4 regs4 mem4 md4 HM5);
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W4) mm mem4 _ 8 _); [|exact C98'];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Hkeep; unfold hvl_R in *; lia
  | exact Hge
  | exact Hok
  | exact R10
  | rewrite (Hpres 20 ltac:(unfold acallee_saved; lia)); exact G20
  | apply (val_mem_kept rsegs (w_H W3) (w_H W4) mm mem4 _ 8 _); [|exact C90];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Hkeep; unfold hvl_R in *; lia
  | apply (val_mem_kept rsegs (w_H W3) (w_H W4) mm mem4 _ 8 _); [|exact C88];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Hkeep; unfold hvl_R in *; lia ]
end.
Qed.

(* ===================================== P7: 0x834dc jal __subtf3 ===================================== *)
Lemma hvl_p7 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
  getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_s) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_s) ->
  getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_SUBR regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_fd) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_fd) ->
getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x90) 8 (SF.lo64 hvl_d) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x88) 8 (SF.hi64 hvl_d) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_FDR regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM _ C98 Hge Hok A10 A11 A20 C90 C88.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof (HM) as (_ & _ & HR3 & _).
set (extra := [Z_to_bv 64 (SF.lo64 hvl_d); Z_to_bv 64 (SF.hi64 hvl_d)] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = hvl_R).
{ rewrite (ew_Ereg_nat regs3 extra 9 (Z_to_bv 5 9) eq_refl), (HR3 9 ltac:(cbn; tauto)), (proj1 hvl_FA_regs).
  unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs3 extra) 32 = Z_to_bv 64 (SF.lo64 hvl_d))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs3 extra) 33 = Z_to_bv 64 (SF.hi64 hvl_d))
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10 : ew (Ereg regs3 extra) 10 = w64 (SF.lo64 hvl_fd))
  by (rewrite (ew_Ereg_nat regs3 extra 10 (Z_to_bv 5 10) eq_refl); exact A10).
assert (E11 : ew (Ereg regs3 extra) 11 = w64 (SF.hi64 hvl_fd))
  by (rewrite (ew_Ereg_nat regs3 extra 11 (Z_to_bv 5 11) eq_refl); exact A11).
assert (E20 : ew (Ereg regs3 extra) 20 = w64 hvl_t)
  by (rewrite (ew_Ereg_nat regs3 extra 20 (Z_to_bv 5 20) eq_refl); exact A20).
pose proof (proj1 (proj1 HM)) as HJ.
pose proof (hv_entry (fx := fx3) 0x834dc []
  [hv_frame 0x88 0x98 0 0 [YP09.mkChunk 0x88 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))]]
  hvl_facts9 W3 regs3 extra mem3 (Forall_nil _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [|apply Forall_nil];
    apply (hvl_frame_ok _ _ _ _ _ _ _ _ 0x88 0x98 0 0 _ HM E9 ltac:(lia) ltac:(lia) ltac:(intros; lia));
    apply Forall_cons;
    [ apply (chunk_ok_val rsegs _ _ hvl_R 0x88 8 (SOff 33 0) (SF.hi64 hvl_d));
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E33 | apply hvm_hi64_rng] | cbn; apply hvm_hi64_rng | cbn; lia | exact C88 ]
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ hvl_R 0x90 8 (SOff 32 0) (SF.lo64 hvl_d));
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E32 | apply hvm_lo64_rng] | cbn; apply hvm_lo64_rng | cbn; lia | exact C90 ] ])
  ltac:(cbn; repeat split; try exact I) (hvl_facts9_ok _ E9)) as HS1.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 HV_FDR) with (Z_to_bv 64 0x834dc).
hv_run hv_awr. hv_keep hv_kwr.
hvl_mid_after HM HM4.
hvl_reg (Z_to_bv 5 1) (SLit 537840) RA_SF_SUB ltac:(rewrite U_lit by lia; reflexivity) G1.
hvl_reg (Z_to_bv 5 10) (SOff 32 0) (SF.lo64 hvl_d) ltac:(apply hv_U_atom; [exact E32 | apply hvm_lo64_rng]) G10.
hvl_reg (Z_to_bv 5 11) (SOff 33 0) (SF.hi64 hvl_d) ltac:(apply hv_U_atom; [exact E33 | apply hvm_hi64_rng]) G11.
hvl_reg0 (Z_to_bv 5 12) 10%nat G12. rewrite E10 in G12.
hvl_reg0 (Z_to_bv 5 13) 11%nat G13. rewrite E11 in G13.
hvl_reg0 (Z_to_bv 5 20) 20%nat G20. rewrite E20 in G20.
hvl_seat A_SF_SUB.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hsf_subtf3_call (fx := fx3) B MT MTL POST
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mm d rg hvl_R
    (SF.lo64 hvl_d) (SF.hi64 hvl_d) (SF.lo64 hvl_fd) (SF.hi64 hvl_fd)
    (hvl_mid_hc _ _ _ _ _ _ _ HM4) G1 G10 G11 G12 G13 (hvm_lo64_rng _) (hvm_hi64_rng _) (hvm_lo64_rng _)
    (hvm_hi64_rng _) (hvl_mid_rom _ _ _ _ _ _ _ HM4) (proj2 (proj2 (proj2 (proj2 HM4)))));
  intros W4 fx4 ly4 S4 regs4 mem4 md4 Hle Hfx4 HC4 Hpres Hfr Hperm Hio Hmo Hkeep Hrom4 R10 R11;
  assert (HM5 := hvl_mid_call _ _ _ _ _ _ _ fx4 ly4 S4 W4 regs4 mem4 md4 HC_SUB_STK HM4
    ltac:(unfold HC_SUB_STK; lia) Hfx4 HC4 Hpres Hfr Hperm Hio Hmo Hkeep);
  rewrite (hvm_w128 hvl_d (hvm_ext_range _)), (hvm_w128 hvl_fd (hvm_fd_range _)) in R10, R11;
  apply (K fx4 ly4 S4 W4 regs4 mem4 md4 HM5);
  [ unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W4) mem3 mem4 _ 8 _); [|exact C98];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; unfold hvl_R in *;
    rewrite Hkeep by (unfold HC_SUB_STK; lia); apply KE; [lia | exact (fun x => x)]
  | exact Hge
  | exact Hok
  | exact R10
  | exact R11
  | rewrite (Hpres 20 ltac:(unfold acallee_saved; lia)); exact G20 ]
  end
end.
Qed.

(* ===================================== P6: 0x834c8 the two stores of d, fcvt.l.s, jal __floatditf ===================================== *)
Lemma hvl_p6 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
  getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_fd) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_fd) ->
  getr regs3 (Z_to_bv 5 20) = w64 hvl_t ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x90) 8 (SF.lo64 hvl_d) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x88) 8 (SF.hi64 hvl_d) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_FDR regs3 mem3 md3) POST) ->
forall fx3 ly3 S3 W3 regs3 mem3 md3,
hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 -> hvl_f8 fx3 -> hvl_c98 W3 mem3 -> 4 <= Model.e_size v -> hvl_ok ->
getr regs3 (Z_to_bv 5 10) = w64 (SF.lo64 hvl_d) -> getr regs3 (Z_to_bv 5 11) = w64 (SF.hi64 hvl_d) ->
SRr rsegs W3 (@cfg_at fx3 rsegs HV_EXTR regs3 mem3 md3) POST.
Proof.
intros K fx3 ly3 S3 W3 regs3 mem3 md3 HM Hf8 C98 Hge Hok A10 A11.
pose proof hvl_geo as (H46 & _ & Hrs & Hwin & _ & H47 & _ & HTS & _).
pose proof (HM) as (_ & _ & HR3 & _).
assert (E9 : bv_unsigned (ew (Ereg regs3 []) 9) = hvl_R).
{ rewrite (ew_Ereg_nat regs3 [] 9 (Z_to_bv 5 9) eq_refl), (HR3 9 ltac:(cbn; tauto)), (proj1 hvl_FA_regs).
  unfold w64. apply unsigned_lit_small. lia. }
pose proof (proj1 (proj1 HM)) as HJ.
pose proof (hv_entry (fx := fx3) 0x834c8 [] [hv_frame 0x88 0x98 0x88 0x98 []] hvl_facts9 W3 regs3 [] mem3
  (Forall_nil _) ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_cons; [|apply Forall_nil];
    exact (hvl_frame_ok _ _ _ _ _ _ _ _ 0x88 0x98 0x88 0x98 [] HM E9 ltac:(lia) ltac:(lia)
      ltac:(intros; lia) (Forall_nil _)))
  ltac:(cbn; repeat split; try exact I) (hvl_facts9_ok _ E9)) as HS1.
remember (Ereg regs3 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R + 0x88 <= a < hvl_R + 0xa0) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a) by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 HV_EXTR) with (Z_to_bv 64 0x834c8).
assert (E10 : ew E 10 = Z_to_bv 64 (SF.lo64 hvl_d))
  by (subst E; rewrite (ew_Ereg_nat regs3 [] 10 (Z_to_bv 5 10) eq_refl), A10; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 (SF.hi64 hvl_d))
  by (subst E; rewrite (ew_Ereg_nat regs3 [] 11 (Z_to_bv 5 11) eq_refl), A11; reflexivity).
clear KE.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R + 0x88 <= a < hvl_R + 0x98) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a) by (intros; reflexivity).
hv_run hv_awr. hv_keep hv_kwr.
hvl_mid_after HM HM4.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m) (with_vm_backing _ ?x _) _ |- _ =>
  rename m into msA; rename x into matA end.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  pose proof (YN0d.st_ok_region rsegs E ss (restrict H ms) 0
    (YP09.mkRegion (Some 9%nat) 136 152 136 152
      [YP09.mkChunk 136 (CVal 8 (SOff 11 0)); YP09.mkChunk 144 (CVal 8 (SOff 10 0))]) HS
    ltac:(vm_compute; reflexivity)) as HRg;
  assert (C90 : val_mem rsegs (mrestrict H (ms_mem ms)) (hvl_R + 0x90) 8 (SF.lo64 hvl_d))
  by (apply (hvl_reg_cell E _ 136 152 136 152 _ 144 (SOff 10 0) _ HRg ltac:(right; left; reflexivity) E9);
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E10 | apply hvm_lo64_rng] | apply hvm_lo64_rng ]);
  assert (C88 : val_mem rsegs (mrestrict H (ms_mem ms)) (hvl_R + 0x88) 8 (SF.hi64 hvl_d))
  by (apply (hvl_reg_cell E _ 136 152 136 152 _ 136 (SOff 11 0) _ HRg ltac:(left; reflexivity) E9);
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E11 | apply hvm_hi64_rng] | apply hvm_hi64_rng ]);
  assert (C98' : hvl_c98 W3 (ms_mem ms))
  by (unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 (ms_mem ms) _ 8 _); [|exact C98];
      intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0;
      lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ms) a = _ |- _ => apply KE; lia end)
end.
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbdr. fold hvl_bd in Hbdr.
hvl_seat 0x834d0.
set (dA := with_vm_backing (m_vm_lazy md3) matA md3) in *.
clear dependent E. clear KE HJ C98.
apply (hvf_fcvt (fx := fx3) W3 (ms_regs msA) (ms_mem msA) dA POST hvl_bd Hf8 Hbdr (proj2 (proj2 (proj2 (proj2 HM4))))).
intros fx4 regs4 X Hfx4 Hr4 G20.
change (fst (fp_to_int fmt_single RTZ true 64 hvl_bd)) with hvl_t in G20, Hr4.
assert (HM5 : hvl_mid fx4 ly3 S3 W3 regs4 (ms_mem msA) (with_vm_backing (m_vm_lazy dA) X dA)).
{ apply (hvl_mid_fp _ _ _ _ _ _ _ _ _ X HM4); [exact (hvl_fxr_keep _ _ _ (proj2 (proj2 (proj2 HM4))) Hfx4)|].
  rewrite Hr4. apply hvl_krb_upd. right; reflexivity. }
assert (Hf8' : hvl_f8 fx4) by (unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx4); exact Hf8).
clear Hr4.
pose proof (proj1 (proj1 HM5)) as HJ.
pose proof (hv_entry (fx := fx4) 0x834d4 [] [] (mkFacts [] [] []) W3 regs4 [] (ms_mem msA)
  (Forall_nil _) eq_refl (Forall_nil _) I ltac:(repeat split)) as HS1.
assert (E20 : ew (Ereg regs4 []) 20 = w64 hvl_t) by (rewrite (ew_Ereg_nat regs4 [] 20 (Z_to_bv 5 20) eq_refl); exact G20).
remember (Ereg regs4 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs4 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W3) (ms_mem msA))) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview rsegs (w_H W3) (ms_mem msA) a = aview rsegs (w_H W3) (ms_mem msA) a) by (intros; reflexivity).
unfold cfg_at. change (w64 0x834d4) with (Z_to_bv 64 0x834d4).
hv_run hv_awr. hv_keep hv_kwr.
hvl_mid_after HM5 HM6.
hvl_reg (Z_to_bv 5 1) (SLit 537820) RA_SF_FD ltac:(rewrite U_lit by lia; reflexivity) G1.
hvl_reg0 (Z_to_bv 5 10) 20%nat G10. rewrite E20 in G10.
hvl_reg0 (Z_to_bv 5 20) 20%nat G20'. rewrite E20 in G20'.
hvl_seat A_SF_FD.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ =>
  apply (hsf_floatditf_call (fx := fx4) B MT MTL POST
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly3 S3 W3 mm d rg hvl_R hvl_t
    (hvl_mid_hc _ _ _ _ _ _ _ HM6) G1 G10 (hvl_mid_rom _ _ _ _ _ _ _ HM6)
    (proj2 (proj2 (proj2 (proj2 HM6)))));
  intros W5 fx6 ly5 S5 regs5 mem5 md5 Hle Hfx6 HC5 Hpres Hfr Hperm Hio Hmo Hkeep Hrom5 R10 R11;
  assert (HM7 := hvl_mid_call _ _ _ _ _ _ _ fx6 ly5 S5 W5 regs5 mem5 md5 0 HM6 ltac:(lia)
    Hfx6 HC5 Hpres Hfr Hperm Hio Hmo (fun a Ha _ => Hkeep a Ha));
  assert (Kall : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W3) (ms_mem msA) a)
  by (intros a Ha; rewrite (Hkeep a Ha); apply KE; [exact Ha | exact (fun x => x)]);
  apply (K fx6 ly5 S5 W5 regs5 mem5 md5 HM7);
  [ unfold hvl_f8 in *; rewrite (hvl_fxk_get _ _ _ Hfx6); exact Hf8'
  | unfold hvl_c98 in *; apply (val_mem_kept rsegs (w_H W3) (w_H W5) (ms_mem msA) mem5 _ 8 _); [|exact C98'];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Kall; lia
  | exact Hge
  | exact Hok
  | exact R10
  | exact R11
  | rewrite (Hpres 20 ltac:(unfold acallee_saved; lia)); exact G20'
  | apply (val_mem_kept rsegs (w_H W3) (w_H W5) (ms_mem msA) mem5 _ 8 _); [|exact C90];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Kall; lia
  | apply (val_mem_kept rsegs (w_H W3) (w_H W5) (ms_mem msA) mem5 _ 8 _); [|exact C88];
    intros k0 Hk0; change (Z.of_nat 8) with 8 in Hk0; apply Kall; lia ]
  end
end.
Qed.

(* ===================================== P1: FA 0x83430 -> RFA / the `flw` ===================================== *)
Lemma hvl_p1 :
(forall fx3 ly3 S3 W3 regs3 mem3 md3,
  hvl_mid fx3 ly3 S3 W3 regs3 mem3 md3 ->
  Sem.reg_get (@fp_regs fx3) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 hvl_bd) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (hvl_R + 0x98) 8 (p mod 2 ^ 64) ->
  4 <= Model.e_size v ->
  SRr rsegs W3 (@cfg_at fx3 rsegs HV_FEQ regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx2 rsegs HV_FLT regs2 mem2 md2) POST.
Proof.
intros K.
pose proof hvl_geo as (H46 & Hal & Hrs & Hwin & Hceil & H47 & Hsp & HTS & Hc).
pose proof hvl_R16 as Hal16.
pose proof hvl_FA_regs as (A9 & A23 & A10 & A13).
pose proof hvl_FA_facts as (Hwf & Hpair & Hvwf & HSm & Hty & Hp & Hch & Hkey & Hpv).
pose proof hvl_ent_geo as (Ha0 & Ha1 & Happ).
pose proof hvl_FA_ent as (Hsz & Hbd & Hra).
pose proof hvl_mid_FA as HM2.
pose proof hvl_FA_base as (Hcore & _).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hszr : 0 <= Model.e_size v <= 45) by (destruct Hvwf as (_ & _ & H); exact H).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbdr. fold hvl_bd in Hbdr.
set (extra := [Z_to_bv 64 (Model.e_size v); Z_to_bv 64 hvl_bd] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs2 extra) 9) = hvl_R).
{ rewrite (ew_Ereg_nat regs2 extra 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : bv_unsigned (ew (Ereg regs2 extra) 10) = hvl_a).
{ rewrite (ew_Ereg_nat regs2 extra 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64. apply unsigned_lit_small. lia. }
assert (E10w : ew (Ereg regs2 extra) 10 = Z_to_bv 64 hvl_a).
{ rewrite (ew_Ereg_nat regs2 extra 10 (Z_to_bv 5 10) eq_refl), A10. reflexivity. }
assert (E23 : bv_unsigned (ew (Ereg regs2 extra) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 extra 23 (Z_to_bv 5 23) eq_refl), A23. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E23w : ew (Ereg regs2 extra) 23 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 extra 23 (Z_to_bv 5 23) eq_refl), A23. reflexivity. }
assert (E13 : ew (Ereg regs2 extra) 13 = Z_to_bv 64 p).
{ rewrite (ew_Ereg_nat regs2 extra 13 (Z_to_bv 5 13) eq_refl), A13. reflexivity. }
assert (E32 : ew (Ereg regs2 extra) 32 = Z_to_bv 64 (Model.e_size v))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 extra) 33 = Z_to_bv 64 hvl_bd)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (hv_entry (fx := fx2) HV_FLT []
  [hv_frame 0x98 0xa0 0x98 0xa0 [];
   YP09.mkRegion (Some 10%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))]]
  hv_facts10 W2 regs2 extra mem2 (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
specialize (HS1 ltac:(
  apply Forall_cons;
  [ apply (hv_frame_ok _ W2 mem2 hvl_R (x_STK rsegs cx) (x_sp0 rsegs cx) 0x98 0xa0 0x98 0xa0 [] E9);
    [ lia | lia | exact Hpres | intros _; split; lia | apply Forall_nil ]
  | apply Forall_cons; [|apply Forall_nil];
    apply (hm_ro_region rsegs _ (w_H W2) mem2 10 hvl_a 4 12); [exact E10 | lia | lia |];
    apply Forall_cons;
    [ apply (chunk_ok_val rsegs _ _ hvl_a 4 4 (SOff 32 0) (Model.e_size v));
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hsz ]
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ hvl_a 8 4 (SOff 33 0) hvl_bd);
      [ apply hv_denot_of_U; apply hv_U_atom; [exact E33 | lia] | cbn; lia | cbn; lia | exact Hbd ] ] ])).
specialize (HS1 ltac:(cbn; repeat split; try exact I;
  unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val hv_frame]; rewrite ?E9, ?E10; lia)).
specialize (HS1 (hv_facts10_ok _ hvl_R hvl_a E9 ltac:(lia) Hal16 E23 E10 ltac:(lia))).
remember (Ereg regs2 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx hv_SH E (mrestrict (w_H W2) mem2)).
{ apply (hv_sh_ok W2 mem2 E hvl_a); [ | | exact Hra | exact Happ ].
  - unfold HV_Bx. apply hv_U_atom; [exact E23w | unfold SHADOW_OFF; lia].
  - apply hv_U_atom; [exact E10w | lia]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (hvl_R + 0x88 <= a < hvl_R + 0xa0) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold cfg_at. change (w64 HV_FLT) with (Z_to_bv 64 HV_FLT).
hv_run hv_awr. hv_keep hv_kwr.
assert (Usz : U E (SExt true 32 (SOff 32 0)) = Model.e_size v).
{ subst E. rewrite (hv_U_sext32 _ 32 (Model.e_size v) E32 ltac:(lia)).
  destruct (Z.ltb_spec (Model.e_size v) (2 ^ 31)); lia. }
hv_branch Hb.
all: rewrite branch_geu_U, Usz, U_lit in Hb by lia.
- (* 0x83450 bgeu taken: size >= 4, the body's check, then the `flw` *)
  assert (Hge : 4 <= Model.e_size v) by (apply negb_true_iff, Z.ltb_ge in Hb; exact Hb).
  hv_run hv_awr. hv_keep hv_kwr.
  hvl_mid_after HM2 HM3.
  hvl_reg (Z_to_bv 5 10) (SOff 10 8) (hvl_a + 8) ltac:(apply U_atom_off; [exact E10w | lia | lia]) G10.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (YN0d.st_ok_region rsegs E ss (restrict H ms) 0
      (YP09.mkRegion (Some 9%nat) 152 160 152 160 [YP09.mkChunk 152 (CVal 8 (SOff 13 0))]) HS
      ltac:(vm_compute; reflexivity)) as HRg;
    assert (C98 : val_mem rsegs (mrestrict H (ms_mem ms)) (hvl_R + 0x98) 8 (p mod 2 ^ 64))
    by (apply (hvl_reg_cell E _ 152 160 152 160 _ 152 (SOff 13 0) (p mod 2 ^ 64) HRg ltac:(left; reflexivity) E9);
        [ apply hv_denot_of_U; apply hv_U_atom; [rewrite Z.mod_small by lia; exact E13 | apply Z.mod_pos_bound; lia]
        | apply Z.mod_pos_bound; lia ])
  end.
  hvl_seat 0x834a4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?d) _ =>
  apply (hvf_flw (fx := fx2) W2 rg mm d POST (hvl_a + 8) hvl_bd G10 ltac:(lia) ltac:(lia));
  [ apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mm (hvl_a + 8) 4 hvl_bd); [|exact Hbd];
    intros k0 Hk0; change (Z.of_nat 4) with 4 in Hk0;
    lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ mm a = _ |- _ => apply KE; lia end
  | exact Hbdr
  | intros X;
    apply (K (hvf_set 8 fx2 (Sem.nan_box (Z_to_bv 32 hvl_bd))) ly2 S2 W2 rg mm (with_vm_backing (m_vm_lazy d) X d));
    [ apply (hvl_mid_fp _ _ _ _ _ _ _ _ _ X HM3);
      [ apply hvl_fxr_set; [apply hvl_fxr_refl; exact (proj2 (proj2 (proj2 (proj2 HM2)))) | left; reflexivity]
      | intros; reflexivity ]
    | apply hvl_set_get
    | exact C98
    | exact Hge ] ]
  end.
- (* not taken: size < 4, RFA *)
  assert (Hlt : Model.e_size v < 4) by (apply negb_false_iff, Z.ltb_lt in Hb; exact Hb).
  hv_run_to hv_awr 0x83454. hv_keep hv_kwr.
  hvl_mid_after HM2 HM3.
  hvl_seat 0x83454.
  exact (hvl_go_RFA _ _ _ _ _ _ _ HM3 (hvl_cell_small Hlt)).
Qed.

(* ===================================== the arm ===================================== *)
Lemma hvl_from_FA_inst : SRr rsegs W2 (@cfg_at fx2 rsegs HV_FLT regs2 mem2 md2) POST.
Proof. exact (hvl_p1 (hvl_p2 (hvl_p3 (hvl_p4 (hvl_p5 (hvl_p6 (hvl_p7 (hvl_p8 hvl_p9)))))))). Qed.
End fa.

(* ===================================== the lane's statement ===================================== *)
Theorem hvl_flt_A : @hv_piece_flt_stmt fx rc SK B MT.
Proof.
intros cx POST r ev at0 m HS HRFA HTAIL fx2 ly2 S2 W2 regs2 mem2 md2 kk v ch p cs keys rf HFA.
eapply hvl_from_FA_inst; eassumption.
Qed.
Print Assumptions hvl_flt_A.
End k.

Print Assumptions hvl_core_step.
Print Assumptions hvl_hc_core.
Print Assumptions hvl_mid_run.
Print Assumptions hvl_mid_fp.
Print Assumptions hvl_mid_call.
Print Assumptions hvl_cut_RFA.
Print Assumptions hvl_cut_TAIL.
Print Assumptions hvl_p1.
Print Assumptions hvl_p5.
Print Assumptions hvl_p9.
Print Assumptions hvl_flt_A.
