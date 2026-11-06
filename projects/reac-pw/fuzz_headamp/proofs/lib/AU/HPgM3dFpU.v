(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheck.v (ck_entry, the code table ck_tbl / ck_wx / ck_segs_low) and
   lib/A/RPgCheckStr.v (rl_cstr_kept) at 77f59d02b01 for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02:
   the half's code table, the entry state of a run that starts at one of its cuts (the registers, the real frame at
   s1 and the role cell as regions), the stack facts of lib/A/RPgSeg.v's rs_pre, the seam between RPgSeg's rs_core and
   lib/A/RPgCSpec.v's callee contracts (rl_pre before a call, rl_post after it), and the strings and cells the callees
   read, carried from the segment's start to a cut (rl_cstr_kept with two worlds and the half's write set). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 for reac-pw/fuzz_headamp image A: only regs_ok_override, ck_sr and ck_regs_ok are kept (renamed hvf_regs_ok_override, hvf_sr, hvf_regs_ok), and ck_entry is restated with the regions and facts as arguments as proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v states m2_entry at 7e8cf15c304 (hvf_entry); the check functions, their code table, region, facts and walk tactics are dropped; the one-step route of m2f_flw in proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304 becomes hvf_srr_one; lor_shift_add, nan_box_unsigned, unbox_nan_box and sgnj_self32 are copied from proofs/reac-pw/fuzz_headamp/lib/Prog/HeadCheck/Near.v at c63be0f19045 (hvf_ prefix added); the exact float step lemmas and the six site wrappers are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dFp.v, with its addresses and numbers changed; 83 of its 235 lines of code are new or changed and 214 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dFp.v at 771429d4e3a3 (part 2: hvf_entry,
   hvf_srr_one, hvf_fcmp_x10 and the wrappers) restated over image B's segments lib/AU/Img0U.v rsegs with image B's
   seven float sites; part 1 (the exact step lemmas and the NaN-box lemmas) is Required from that file, not copied. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on its unstripped twin sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the seven float instructions of the Float arm
   of M03's value piece (the inlined cell_value + pod_nearest, pod.h:116-163), each stepped exactly in the harness's
   SRr form, so that a walk can go back into the kit's engine (lib/Reusable/YCbq.v aj_run_tok / aj_run_to_tok, which
   has no rule for a float instruction) at the next pc. Proves no function (kind: step kit).

   THE SEVEN SITES (each 4 bytes; each word is checked against lib/AU/Img0U.v rsegs by computation in its proof):
     HVFU_FLW 0x835bc  0x000c2407  flw      fs0,0(s8)        f8 := nan_box (the 4 bytes at s8)
     HVFU_FEQ 0x835c0  0xa0842553  feq.s    a0,fs0,fs0       x10 := (f8 == f8)
     HVFU_FMV 0x835c8  0x20840553  fmv.s    fa0,fs0          f10 := f8 (fsgnj.s fa0,fs0,fs0)
     HVFU_LT1 0x835d4  0xa0941553  flt.s    a0,fs0,fs1       x10 := (f8 < f9),  f9  = -1.0f  (0xbf800000)
     HVFU_LT2 0x835e0  0xa0891553  flt.s    a0,fs2,fs0       x10 := (f18 < f8), f18 = 256.0f (0x43800000)
     HVFU_LT3 0x835e8  0xa1341553  flt.s    a0,fs0,fs3       x10 := (f8 < f19), f19 = 2^63   (0x5f000000), the
                                                             pod.h:160 float-cast check (image B only)
     HVFU_CVT 0x83608  0xc0241953  fcvt.l.s s2,fs0,rtz       x18 := the signed 64-bit integer of f8, toward zero
   Each wrapper hands its continuation the state at the next pc with the exact new register map (regupd regs rd v)
   and float state (hvf_set k fx w, or some fx2 with hd_fxk [] fx fx2: every float register as at entry and a zero
   rounding mode). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YN2e.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgM3dFp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module FP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.HPgM3dFp.

(* ======================================== the seven sites ======================================== *)
Definition HVFU_FLW : Z := 0x835bc.
Definition HVFU_FEQ : Z := 0x835c0.
Definition HVFU_FMV : Z := 0x835c8.
Definition HVFU_LT1 : Z := 0x835d4.
Definition HVFU_LT2 : Z := 0x835e0.
Definition HVFU_LT3 : Z := 0x835e8.
Definition HVFU_CVT : Z := 0x83608.

(* image B's writable segments do not wrap (SRr_msteps_st's premise) *)
Lemma hvfu_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the entry state of a run at pc: the registers as atoms with the overrides ov, the regions rs, the facts G *)
Lemma hvfu_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 extra) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
pairwise_disjoint (Ereg regs2 extra) rs ->
facts_ok (Ereg regs2 extra) G ->
st_ok rsegs (Ereg regs2 extra) (mkSS pc (FP.hvf_sr ov) rs None G)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs))).
Proof.
intros pc ov rs G W regs2 extra mem2 Hov Hwf Hrs Hpd HG.
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); try assumption. apply FP.hvf_regs_ok. exact Hov.
Qed.
End e.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* One machine step that changes only the registers and the float state, memory as before: the SRr goal at pc
   follows from the continuation at pc'. *)
Lemma hvfu_srr_one : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) pc pc'
(fx2 : YK11.FPState) regs2,
RiscvSemantics.step rsegs (@mkst fx regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs)) =
MachineOk (@mkst fx2 regs2 (Z_to_bv 64 pc') (mrestrict (w_H W) mem) (seg_rom rsegs)) ->
(forall X, SRr rsegs W (@cfg_at fx2 rsegs pc' regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q pc pc' fx2 regs2 Hst HK.
pose proof (hvfu_entry (fx := fx2) pc' [] [] (mkFacts [] [] []) W regs2 [] mem (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS'.
refine (@SRr_msteps_st rsegs fx2 hvfu_wx W _ _ (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs))
  _ md Q _ HS' _).
- rewrite !restrict_mkst_fx. apply msteps_one; [reflexivity | exact Hst].
- intros ms' mat' HS2 Hlo Hhi Hreg.
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl).
  assert (Hm : ms_mem ms' = mem).
  { apply functional_extensionality. intros x. destruct (w_H W x) eqn:Hx.
    - rewrite (Hhi x Hx). reflexivity.
    - rewrite (Hlo x Hx). cbn [ms_mem restrict mkst]. unfold mrestrict. rewrite Hx. reflexivity. }
  rewrite Hm, Hreg. exact (HK mat').
Qed.

Lemma hvfu_x18_nz : Z_to_bv 5 18 <> 0%bv.
Proof. intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz. Qed.

(* A compare at pc into a0 with both operands NaN-boxed binary32 values va (rs1) and vb (rs2). *)
Lemma hvfu_fcmp_x10 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) pc pc' w op rs1 rs2
va vb,
fetch_word rsegs (Z_to_bv 64 pc) = Some w -> is_ecall w = false ->
decode_any w = Some (Fcmp op FMT_S (Z_to_bv 5 10) rs1 rs2, 4%Z) ->
v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 pc' ->
Sem.reg_get (@fp_regs fx) rs1 = Sem.nan_box (Z_to_bv 32 va) -> 0 <= va < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) rs2 = Sem.nan_box (Z_to_bv 32 vb) -> 0 <= vb < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if FP.hvf_fcmp_s op va vb then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if FP.hvf_fcmp_s op va vb then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs pc' regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q pc pc' w op rs1 rs2 va vb Hf He Hd Hpc H1 Ha H2 Hb Hz HK.
destruct (FP.hvf_step_fcmp_s fx rsegs regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs) w op
  (Z_to_bv 5 10) rs1 rs2 Hf He Hd Hz) as (cs' & Hz' & Hst).
unfold FP.hvf_fread_s in Hst. rewrite H1, H2, !FP.hvf_unbox_nan_box in Hst.
rewrite (YK0o.fp_u_Z2bv32 va Ha), (YK0o.fp_u_Z2bv32 vb Hb), Hpc in Hst.
apply (hvfu_srr_one W regs mem md Q pc pc' (YK11.mkFP (@fp_regs fx) cs')
  (regupd regs (Z_to_bv 5 10) (w64 (if FP.hvf_fcmp_s op va vb then 1 else 0)))).
- rewrite Hst. destruct (FP.hvf_fcmp_s op va vb); reflexivity.
- intros X. apply (HK (YK11.mkFP (@fp_regs fx) cs') _ X).
  + split; [intros k _; reflexivity | exact Hz'].
  + reflexivity.
  + apply getr_same. exact FP.hvf_x10_nz.
Qed.

(* ---- HVFU_FLW 0x835bc flw fs0,0(s8) ---- *)
Lemma hvfu_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 24) = w64 a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall X, SRr rsegs W (@cfg_at (FP.hvf_set 8 fx (Sem.nan_box (Z_to_bv 32 b))) rsegs 0x835c0 regs mem
  (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835bc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H24 Ha0 Ha1 Hval Hb HK.
change (w64 a) with (Z_to_bv 64 a) in H24.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (YN2e.le_list b 4))
by (apply YN2e.rdn_cell; intros k Hk; exact (Hval k Hk)).
assert (Hw : bv_extract 0 32 (le_bytes_to_word (YN2e.le_list b 4)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, YN2e.bytes_le_to_Z_le_list.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
apply (hvfu_srr_one W regs mem md Q 0x835bc 0x835c0 (FP.hvf_set 8 fx (Sem.nan_box (Z_to_bv 32 b))) regs);
  [|exact HK].
rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x835bc) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0x000c2407) (Z_to_bv 5 8) (Z_to_bv 5 24) (Z_to_bv 12 0) (Z_to_bv 64 a) (YN2e.le_list b 4));
[ | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
  | rewrite H24; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
  | exact Hrd ].
rewrite Hw. reflexivity.
Qed.

(* ---- HVFU_FEQ 0x835c0 feq.s a0,fs0,fs0 ---- *)
Lemma hvfu_feq : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_eq fmt_single b b) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_eq fmt_single b b) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x835c4 regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835c0) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb Hz HK.
apply (hvfu_fcmp_x10 W regs mem md Q 0x835c0 0x835c4 (Z_to_bv 32 0xa0842553) F_EQ (Z_to_bv 5 8) (Z_to_bv 5 8) b b);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H8 | exact Hb | exact H8 | exact Hb | exact Hz | exact HK ].
Qed.

(* ---- HVFU_FMV 0x835c8 fmv.s fa0,fs0 (fsgnj.s fa0,fs0,fs0) ---- *)
Lemma hvfu_fmv : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) ->
(forall X, SRr rsegs W (@cfg_at (FP.hvf_set 10 fx (Sem.nan_box (Z_to_bv 32 b))) rsegs 0x835cc regs mem
  (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835c8) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 HK.
apply (hvfu_srr_one W regs mem md Q 0x835c8 0x835cc (FP.hvf_set 10 fx (Sem.nan_box (Z_to_bv 32 b))) regs);
  [|exact HK].
rewrite (FP.hvf_step_fsgnj_s fx rsegs regs (Z_to_bv 64 0x835c8) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0x20840553) F_SGNJ (Z_to_bv 5 10) (Z_to_bv 5 8) (Z_to_bv 5 8));
  [ | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv ].
rewrite H8, FP.hvf_unbox_nan_box, FP.hvf_sgnj_self32. reflexivity.
Qed.

(* ---- HVFU_LT1 0x835d4 flt.s a0,fs0,fs1 (fs1 = -1.0f) ---- *)
Lemma hvfu_lt1 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 0xbf800000) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_lt fmt_single b 0xbf800000) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single b 0xbf800000) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x835d8 regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835d4) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb H9 Hz HK.
apply (hvfu_fcmp_x10 W regs mem md Q 0x835d4 0x835d8 (Z_to_bv 32 0xa0941553) F_LT (Z_to_bv 5 8) (Z_to_bv 5 9)
  b 0xbf800000);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H8 | exact Hb | exact H9 | lia | exact Hz | exact HK ].
Qed.

(* ---- HVFU_LT2 0x835e0 flt.s a0,fs2,fs0 (fs2 = 256.0f) ---- *)
Lemma hvfu_lt2 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 0x43800000) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_lt fmt_single 0x43800000 b) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single 0x43800000 b) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x835e4 regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835e0) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb H18 Hz HK.
apply (hvfu_fcmp_x10 W regs mem md Q 0x835e0 0x835e4 (Z_to_bv 32 0xa0891553) F_LT (Z_to_bv 5 18) (Z_to_bv 5 8)
  0x43800000 b);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H18 | lia | exact H8 | exact Hb | exact Hz | exact HK ].
Qed.

(* ---- HVFU_LT3 0x835e8 flt.s a0,fs0,fs3 (fs3 = 2^63: the pod.h:160 float-cast check) ---- *)
Lemma hvfu_lt3 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 0x5f000000) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_lt fmt_single b 0x5f000000) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single b 0x5f000000) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x835ec regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x835e8) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb H19 Hz HK.
apply (hvfu_fcmp_x10 W regs mem md Q 0x835e8 0x835ec (Z_to_bv 32 0xa1341553) F_LT (Z_to_bv 5 8) (Z_to_bv 5 19)
  b 0x5f000000);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H8 | exact Hb | exact H19 | lia | exact Hz | exact HK ].
Qed.

(* ---- HVFU_CVT 0x83608 fcvt.l.s s2,fs0,rtz ---- *)
Lemma hvfu_fcvt : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 18) (w64 (fst (fp_to_int fmt_single RTZ true 64 b))) ->
 getr regs2 (Z_to_bv 5 18) = w64 (fst (fp_to_int fmt_single RTZ true 64 b)) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x8360c regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x83608) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb Hz HK.
assert (Hf : fetch_word rsegs (Z_to_bv 64 0x83608) = Some (Z_to_bv 32 0xc0241953)) by vm_refl_bv.
assert (He : is_ecall (Z_to_bv 32 0xc0241953) = false) by (vm_compute; reflexivity).
assert (Hd : decode_any (Z_to_bv 32 0xc0241953) =
  Some (Fcvt FC_L FC_S (Z_to_bv 5 18) (Z_to_bv 5 8) (Z_to_bv 3 1), 4%Z)) by vm_refl_bv.
destruct (FP.hvf_step_fcvt_l_s fx rsegs regs (Z_to_bv 64 0x83608) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0xc0241953) (Z_to_bv 5 18) (Z_to_bv 5 8) (Z_to_bv 3 1) Hf He Hd eq_refl Hz) as (cs' & Hz' & Hst).
unfold FP.hvf_fread_s in Hst. rewrite H8, FP.hvf_unbox_nan_box, (YK0o.fp_u_Z2bv32 b Hb) in Hst.
apply (hvfu_srr_one W regs mem md Q 0x83608 0x8360c (YK11.mkFP (@fp_regs fx) cs')
  (regupd regs (Z_to_bv 5 18) (w64 (fst (fp_to_int fmt_single RTZ true 64 b))))).
- rewrite Hst. reflexivity.
- intros X. apply (HK (YK11.mkFP (@fp_regs fx) cs') _ X).
  + split; [intros k _; reflexivity | exact Hz'].
  + reflexivity.
  + apply getr_same. exact hvfu_x18_nz.
Qed.
End b.

Print Assumptions hvfu_entry.
Print Assumptions hvfu_srr_one.
Print Assumptions hvfu_flw.
Print Assumptions hvfu_feq.
Print Assumptions hvfu_fmv.
Print Assumptions hvfu_lt1.
Print Assumptions hvfu_lt2.
Print Assumptions hvfu_lt3.
Print Assumptions hvfu_fcvt.
