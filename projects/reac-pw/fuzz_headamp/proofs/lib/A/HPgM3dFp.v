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
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on its unstripped twin sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the six float instructions of the value arm of
   M03's value_nearest piece (the inlined cell_value + pod_nearest, pod.h:120-161), each stepped EXACTLY in the
   harness's SRr form so that the walk can go back into the kit's engine (lib/Reusable/YCbq.v aj_run_tok /
   aj_run_to_tok, which has no rule for a float instruction) at the next pc.
   Proves no function (kind: step kit).

   THE SIX SITES (each 4 bytes; the words are checked against lib/A/Img0.v rsegs by vm_compute in each proof):
     HVF_FLW 0x834a4  0x00052407  flw    fs0,0(a0)        f8 := nan_box (the 4 bytes at a0)
     HVF_FEQ 0x834a8  0xa0842553  feq.s  a0,fs0,fs0       x10 := (f8 == f8)
     HVF_LT1 0x834b0  0xa0941553  flt.s  a0,fs0,fs1       x10 := (f8 < f9),  f9  = -1.0f   (0xbf800000)
     HVF_LT2 0x834b8  0xa0891553  flt.s  a0,fs2,fs0       x10 := (f18 < f8), f18 = 256.0f  (0x43800000)
     HVF_FMV 0x834c0  0x20840553  fmv.s  fa0,fs0          f10 := f8 (fsgnj.s fa0,fs0,fs0)
     HVF_CVT 0x834d0  0xc0241a53  fcvt.l.s s4,fs0,rtz     x20 := the signed 64-bit integer of f8, rounded to zero

   PART 1, the exact step lemmas over the machine (lib/Reusable/YK0o.v states fp_step_fcmp, fp_step_fcvt_to_x and
   fp_step_fsgnj with an existential result; these name it): hvf_step_fcmp_s (the boolean is hvf_fcmp_s, the first
   component of Sem.exec's Fcmp arm at the two FMT_S operands hvf_fread_s), hvf_step_fcvt_l_s (rm field 1 = RTZ;
   the integer is the first component of Fpu.fp_to_int at FMT_S, RTZ, signed, 64 bits), hvf_step_fsgnj_s (fcsr
   unchanged). The fcsr of the first two is existential but keeps a zero rounding mode (YK0o.frm_zero).
   PART 2, the six wrappers hvf_flw, hvf_feq, hvf_lt1, hvf_lt2, hvf_fmv, hvf_fcvt: one machine step by hvf_srr_one
   (the route of fuzz_role's m2f_flw: SRr_msteps_st into the entry state at the next pc with no region and no fact,
   memory unchanged), handing the continuation the state at the next pc with the exact new register map
   (regupd regs rd v, so every other register is read off regs) and float state (hvf_set k fx w, or a state fx2
   with hd_fxk [] fx fx2: every float register as at entry and a zero rounding mode). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the six sites ======================================== *)
Definition HVF_FLW : Z := 0x834a4.
Definition HVF_FEQ : Z := 0x834a8.
Definition HVF_LT1 : Z := 0x834b0.
Definition HVF_LT2 : Z := 0x834b8.
Definition HVF_FMV : Z := 0x834c0.
Definition HVF_CVT : Z := 0x834d0.

(* ======================================== binary32 in a 64-bit float register ======================================== *)
(* [Near.v lor_shift_add, nan_box_unsigned, unbox_nan_box, sgnj_self32] *)
Lemma hvf_lor_shift_add : forall a v n, 0 <= n -> 0 <= v < 2^n -> Z.lor (a * 2^n) v = a * 2^n + v.
Proof.
  intros a v n Hn Hv.
  assert (L : Z.land (a * 2^n) v = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [H|H].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small v (2^n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma hvf_nan_box_unsigned : forall v : bv 32, bv_unsigned (nan_box v) = 4294967295 * 2^32 + bv_unsigned v.
Proof.
  intros v. unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32) with (2^32) in R.
  replace (bv_unsigned (Z_to_bv 32 (-1))) with 4294967295 by (vm_compute; reflexivity).
  change (Z.of_N 32) with 32. rewrite Z.shiftl_mul_pow2 by lia. apply hvf_lor_shift_add; lia.
Qed.

Lemma hvf_unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  unfold unbox_s, low32. rewrite bv_extract_unsigned, hvf_nan_box_unsigned. change (Z.of_N 32) with 32.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((4294967295 * 2^32 + bv_unsigned v) / 2^32) with 4294967295
    by (rewrite Z.div_add_l by lia; rewrite (Z.div_small (bv_unsigned v)) by lia; lia).
  replace (bv_wrap 32 4294967295 =? Z.ones 32) with true by (vm_compute; reflexivity).
  apply bv_eq. rewrite bv_extract_unsigned, hvf_nan_box_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hvf_sgnj_self32 : forall v : bv 32, sgnj_val F_SGNJ v v = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  apply bv_eq. unfold sgnj_val, bit. cbv zeta.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (Z.of_N (32 - 1)) with 31.
  unfold bv_wrap. change (bv_modulus (32 - 1)) with (2^31). change (bv_modulus 1) with 2.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 31) as [H1|H1].
  - rewrite Z.shiftl_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite orb_false_r. rewrite Z.shiftl_spec by lia.
    destruct (Z.eqb_spec i 31) as [->|Hne].
    + destruct (Z.testbit (bv_unsigned v) 31); reflexivity.
    + assert (Hi31 : 0 < i - 31) by lia.
      assert (Hv : Z.testbit (bv_unsigned v) i = false).
      { rewrite <- (Z.mod_small (bv_unsigned v) (2^32)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite Hv. destruct (Z.testbit (bv_unsigned v) 31).
      * change ((if true then 1 else 0) mod 2) with 1.
        apply Z.bits_above_log2; [apply Z.le_0_1 | change (Z.log2 1) with 0; exact Hi31].
      * change ((if false then 1 else 0) mod 2) with 0. apply Z.bits_0.
Qed.

(* ======================================== PART 1: exact step lemmas ======================================== *)
(* The FMT_S operand of a float register file fr at r, as Sem.fread reads it (hvf_fread_s_ok). *)
Definition hvf_fread_s (fr : bvmap 5 word) (r : bv 5) : Z := bv_unsigned (unbox_s (reg_get fr r)).
Lemma hvf_fread_s_ok : forall (c : Sem.core) (r : bv 5), hvf_fread_s (Sem.c_fregs c) r = Sem.fread c FMT_S r.
Proof. reflexivity. Qed.
(* The boolean Sem.exec's Fcmp arm writes (as 1 / 0) for format FMT_S at the operands a, b. *)
Definition hvf_fcmp_s (op : fcmpop) (a b : Z) : bool :=
fst (match op with
     | F_EQ => fp_eq (fp_format FMT_S) a b
     | F_LT => fp_lt (fp_format FMT_S) a b
     | F_LE => fp_le (fp_format FMT_S) a b
     end).

Lemma hvf_step_fcmp_s : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcmp op FMT_S rd rs1 rs2, 4%Z) ->
YK0o.frm_zero (@fp_csr fx) ->
exists cs',
YK0o.frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs')
(if bv_eqb rd 0 then regs
 else regupd regs rd (if hvf_fcmp_s op (hvf_fread_s (@fp_regs fx) rs1) (hvf_fread_s (@fp_regs fx) rs2)
                      then Z_to_bv 64 1 else Z_to_bv 64 0))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op rd rs1 rs2 Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
assert (Hacc : forall fl, YK0o.frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply YK0o.fp_frm_zero_accrue; [apply YK0o.fp_fflags_bits_range | exact Hz]).
YK0o.fp_pipeline Hf He Hd.
lazymatch goal with |- context [let '(_, _) := ?p in _] => rewrite (surjective_pairing p) end.
cbv beta iota.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; (eexists; split; [apply Hacc | reflexivity]).
Qed.

Lemma hvf_step_fcvt_l_s : forall (fx : FPState) segs regs pc mem rom w rd rs1 (rm : bv 3),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcvt FC_L FC_S rd rs1 rm, 4%Z) ->
bv_unsigned rm = 1 ->
YK0o.frm_zero (@fp_csr fx) ->
exists cs',
YK0o.frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs')
(if bv_eqb rd 0 then regs
 else regupd regs rd (Z_to_bv 64 (fst (fp_to_int (fp_format FMT_S) RTZ true 64 (hvf_fread_s (@fp_regs fx) rs1)))))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 rm Hf He Hd Hrm Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
(* the rm field 1 resolves to RTZ: rmode_of_field 1 _ = rmode_of_Z 1 = Some RTZ (Fpu.v) *)
assert (Hmd : rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned cs) 5) 7) = Some RTZ).
{ unfold YK0o.frm_zero in Hz. rewrite Hrm, Hz. reflexivity. }
assert (Hacc : forall fl, YK0o.frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply YK0o.fp_frm_zero_accrue; [apply YK0o.fp_fflags_bits_range | exact Hz]).
YK0o.fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
lazymatch goal with |- context [let '(_, _) := ?p in _] => rewrite (surjective_pairing p) end.
cbv beta iota.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; (eexists; split; [apply Hacc | reflexivity]).
Qed.

Lemma hvf_step_fsgnj_s : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fsgnj op FMT_S rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (sgnj_val op (unbox_s (reg_get (@fp_regs fx) rs1))
                                                           (unbox_s (reg_get (@fp_regs fx) rs2))))
                                  (@fp_regs fx)) (@fp_csr fx))
regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op rd rs1 rs2 Hf He Hd.
YK0o.fp_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.

(* ======================================== PART 2: the entry state and the six wrappers ======================================== *)
(* the float state with register k set to w, fcsr unchanged *)
Definition hvf_set (k : Z) (f : YK11.FPState) (w : word) : YK11.FPState :=
  YK11.mkFP (bvmap_set (Z_to_bv 5 k) w (@fp_regs f)) (@fp_csr f).

(* the image's writable segments do not wrap (SRr_msteps_st's premise) *)
Lemma hvf_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* the entry registers: sr_atoms with the overrides ov (register, value it already has) [RPgCheck.v ck_sr] *)
Definition hvf_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* an override of a register by a value it already has keeps regs_ok [RPgCheck.v regs_ok_override] *)
Lemma hvf_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
(* [RPgCheck.v ck_regs_ok] *)
Lemma hvf_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (hvf_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold hvf_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply hvf_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the entry state of a run at pc: the registers as atoms with the overrides ov, the regions rs, the facts G
   [RPgM02Base.v m2_entry, RPgCheck.v ck_entry] *)
Lemma hvf_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 extra) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
pairwise_disjoint (Ereg regs2 extra) rs ->
facts_ok (Ereg regs2 extra) G ->
st_ok rsegs (Ereg regs2 extra) (mkSS pc (hvf_sr ov) rs None G)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs))).
Proof.
intros pc ov rs G W regs2 extra mem2 Hov Hwf Hrs Hpd HG.
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); try assumption. apply hvf_regs_ok. exact Hov.
Qed.
End e.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* One machine step that changes only the registers and the float state, memory as before: the SRr goal at pc
   follows from the continuation at pc' [RPgM02KeyF.v m2f_flw]. *)
Lemma hvf_srr_one : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) pc pc'
(fx2 : YK11.FPState) regs2,
RiscvSemantics.step rsegs (@mkst fx regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs)) =
MachineOk (@mkst fx2 regs2 (Z_to_bv 64 pc') (mrestrict (w_H W) mem) (seg_rom rsegs)) ->
(forall X, SRr rsegs W (@cfg_at fx2 rsegs pc' regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q pc pc' fx2 regs2 Hst HK.
pose proof (hvf_entry (fx := fx2) pc' [] [] (mkFacts [] [] []) W regs2 [] mem (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS'.
refine (@SRr_msteps_st rsegs fx2 hvf_wx W _ _ (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs))
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

(* x10 <> x0 and x20 <> x0 *)
Lemma hvf_x10_nz : Z_to_bv 5 10 <> 0%bv.
Proof. intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz. Qed.
Lemma hvf_x20_nz : Z_to_bv 5 20 <> 0%bv.
Proof. intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz. Qed.

(* A compare at pc into a0 with both operands NaN-boxed binary32 values va (rs1) and vb (rs2). *)
Lemma hvf_fcmp_x10 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) pc pc' w op rs1 rs2
va vb,
fetch_word rsegs (Z_to_bv 64 pc) = Some w -> is_ecall w = false ->
decode_any w = Some (Fcmp op FMT_S (Z_to_bv 5 10) rs1 rs2, 4%Z) ->
v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 pc' ->
Sem.reg_get (@fp_regs fx) rs1 = Sem.nan_box (Z_to_bv 32 va) -> 0 <= va < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) rs2 = Sem.nan_box (Z_to_bv 32 vb) -> 0 <= vb < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if hvf_fcmp_s op va vb then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if hvf_fcmp_s op va vb then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs pc' regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q pc pc' w op rs1 rs2 va vb Hf He Hd Hpc H1 Ha H2 Hb Hz HK.
destruct (hvf_step_fcmp_s fx rsegs regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs) w op
  (Z_to_bv 5 10) rs1 rs2 Hf He Hd Hz) as (cs' & Hz' & Hst).
unfold hvf_fread_s in Hst. rewrite H1, H2, !hvf_unbox_nan_box in Hst.
rewrite (YK0o.fp_u_Z2bv32 va Ha), (YK0o.fp_u_Z2bv32 vb Hb), Hpc in Hst.
apply (hvf_srr_one W regs mem md Q pc pc' (YK11.mkFP (@fp_regs fx) cs')
  (regupd regs (Z_to_bv 5 10) (w64 (if hvf_fcmp_s op va vb then 1 else 0)))).
- rewrite Hst. destruct (hvf_fcmp_s op va vb); reflexivity.
- intros X. apply (HK (YK11.mkFP (@fp_regs fx) cs') _ X).
  + split; [intros k _; reflexivity | exact Hz'].
  + reflexivity.
  + apply getr_same. exact hvf_x10_nz.
Qed.

(* ---- HVF_FLW 0x834a4 flw fs0,0(a0) ---- *)
Lemma hvf_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 10) = w64 a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall X, SRr rsegs W (@cfg_at (hvf_set 8 fx (Sem.nan_box (Z_to_bv 32 b))) rsegs 0x834a8 regs mem
  (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834a4) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H10 Ha0 Ha1 Hval Hb HK.
change (w64 a) with (Z_to_bv 64 a) in H10.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (YN2e.le_list b 4))
by (apply YN2e.rdn_cell; intros k Hk; exact (Hval k Hk)).
assert (Hw : bv_extract 0 32 (le_bytes_to_word (YN2e.le_list b 4)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, YN2e.bytes_le_to_Z_le_list.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
apply (hvf_srr_one W regs mem md Q 0x834a4 0x834a8 (hvf_set 8 fx (Sem.nan_box (Z_to_bv 32 b))) regs);
  [|exact HK].
rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x834a4) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0x00052407) (Z_to_bv 5 8) (Z_to_bv 5 10) (Z_to_bv 12 0) (Z_to_bv 64 a) (YN2e.le_list b 4));
[ | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
  | rewrite H10; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
  | exact Hrd ].
rewrite Hw. reflexivity.
Qed.

(* ---- HVF_FEQ 0x834a8 feq.s a0,fs0,fs0 ---- *)
Lemma hvf_feq : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_eq fmt_single b b) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_eq fmt_single b b) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x834ac regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834a8) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb Hz HK.
apply (hvf_fcmp_x10 W regs mem md Q 0x834a8 0x834ac (Z_to_bv 32 0xa0842553) F_EQ (Z_to_bv 5 8) (Z_to_bv 5 8) b b);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H8 | exact Hb | exact H8 | exact Hb | exact Hz | exact HK ].
Qed.

(* ---- HVF_LT1 0x834b0 flt.s a0,fs0,fs1 (fs1 = -1.0f) ---- *)
Lemma hvf_lt1 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 0xbf800000) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_lt fmt_single b 0xbf800000) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single b 0xbf800000) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x834b4 regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834b0) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb H9 Hz HK.
apply (hvf_fcmp_x10 W regs mem md Q 0x834b0 0x834b4 (Z_to_bv 32 0xa0941553) F_LT (Z_to_bv 5 8) (Z_to_bv 5 9)
  b 0xbf800000);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H8 | exact Hb | exact H9 | lia | exact Hz | exact HK ].
Qed.

(* ---- HVF_LT2 0x834b8 flt.s a0,fs2,fs0 (fs2 = 256.0f) ---- *)
Lemma hvf_lt2 : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 0x43800000) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 10) (w64 (if fst (fp_lt fmt_single 0x43800000 b) then 1 else 0)) ->
 getr regs2 (Z_to_bv 5 10) = w64 (if fst (fp_lt fmt_single 0x43800000 b) then 1 else 0) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x834bc regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834b8) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb H18 Hz HK.
apply (hvf_fcmp_x10 W regs mem md Q 0x834b8 0x834bc (Z_to_bv 32 0xa0891553) F_LT (Z_to_bv 5 18) (Z_to_bv 5 8)
  0x43800000 b);
  [ vm_refl_bv | vm_compute; reflexivity | vm_refl_bv | reflexivity
  | exact H18 | lia | exact H8 | exact Hb | exact Hz | exact HK ].
Qed.

(* ---- HVF_FMV 0x834c0 fmv.s fa0,fs0 (fsgnj.s fa0,fs0,fs0) ---- *)
Lemma hvf_fmv : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) ->
(forall X, SRr rsegs W (@cfg_at (hvf_set 10 fx (Sem.nan_box (Z_to_bv 32 b))) rsegs 0x834c4 regs mem
  (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834c0) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 HK.
apply (hvf_srr_one W regs mem md Q 0x834c0 0x834c4 (hvf_set 10 fx (Sem.nan_box (Z_to_bv 32 b))) regs);
  [|exact HK].
rewrite (hvf_step_fsgnj_s fx rsegs regs (Z_to_bv 64 0x834c0) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0x20840553) F_SGNJ (Z_to_bv 5 10) (Z_to_bv 5 8) (Z_to_bv 5 8));
  [ | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv ].
rewrite H8, hvf_unbox_nan_box, hvf_sgnj_self32. reflexivity.
Qed.

(* ---- HVF_CVT 0x834d0 fcvt.l.s s4,fs0,rtz ---- *)
Lemma hvf_fcvt : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) b,
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b) -> 0 <= b < 2 ^ 32 ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx2 : YK11.FPState) regs2 X, hd_fxk [] fx fx2 ->
 regs2 = regupd regs (Z_to_bv 5 20) (w64 (fst (fp_to_int fmt_single RTZ true 64 b))) ->
 getr regs2 (Z_to_bv 5 20) = w64 (fst (fp_to_int fmt_single RTZ true 64 b)) ->
 SRr rsegs W (@cfg_at fx2 rsegs 0x834d4 regs2 mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x834d0) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q b H8 Hb Hz HK.
assert (Hf : fetch_word rsegs (Z_to_bv 64 0x834d0) = Some (Z_to_bv 32 0xc0241a53)) by vm_refl_bv.
assert (He : is_ecall (Z_to_bv 32 0xc0241a53) = false) by (vm_compute; reflexivity).
assert (Hd : decode_any (Z_to_bv 32 0xc0241a53) =
  Some (Fcvt FC_L FC_S (Z_to_bv 5 20) (Z_to_bv 5 8) (Z_to_bv 3 1), 4%Z)) by vm_refl_bv.
destruct (hvf_step_fcvt_l_s fx rsegs regs (Z_to_bv 64 0x834d0) (mrestrict (w_H W) mem) (seg_rom rsegs)
  (Z_to_bv 32 0xc0241a53) (Z_to_bv 5 20) (Z_to_bv 5 8) (Z_to_bv 3 1) Hf He Hd eq_refl Hz) as (cs' & Hz' & Hst).
unfold hvf_fread_s in Hst. rewrite H8, hvf_unbox_nan_box, (YK0o.fp_u_Z2bv32 b Hb) in Hst.
apply (hvf_srr_one W regs mem md Q 0x834d0 0x834d4 (YK11.mkFP (@fp_regs fx) cs')
  (regupd regs (Z_to_bv 5 20) (w64 (fst (fp_to_int fmt_single RTZ true 64 b))))).
- rewrite Hst. reflexivity.
- intros X. apply (HK (YK11.mkFP (@fp_regs fx) cs') _ X).
  + split; [intros k _; reflexivity | exact Hz'].
  + reflexivity.
  + apply getr_same. exact hvf_x20_nz.
Qed.
End b.

Print Assumptions hvf_step_fcmp_s.
Print Assumptions hvf_step_fcvt_l_s.
Print Assumptions hvf_step_fsgnj_s.
Print Assumptions hvf_flw.
Print Assumptions hvf_feq.
Print Assumptions hvf_lt1.
Print Assumptions hvf_lt2.
Print Assumptions hvf_fmv.
Print Assumptions hvf_fcvt.
