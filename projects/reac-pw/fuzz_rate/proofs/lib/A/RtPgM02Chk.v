(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e887 (its two check
   walks ch_mal / ch_abs and the cut lemma ch_cut_T, with the call-in-the-middle pattern they take from
   lib/A/RPgCheckStr.v) for reac-pw/fuzz_rate image A: role's pcs become rate's (ABS 0x82b7c, MAL 0x82c9c, the
   join A 0x82ca8), the one-byte role cell becomes rate's four-byte hz cell holding 0x5a5a5a5a, the register the
   cell's address lives in moves from role's s6 to rate's s5 (atom 21), the two real-frame cells the absent arm
   reloads are rate's R+0x78 (F) and R+0x58 (the flags byte) instead of role's R+0x28 and R+0x80, and the join's
   cut is rs_cut_A, which carries the flags byte where role's rs_cut_T carried the first block. *)
(* reac-pw/fuzz_rate, image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, the same loaded bytes). Proves no function
   (kind: segment lemma): the piece W11b-checks of LLVMFuzzerTestOneInput's segment M02, whose statement is
   lib/A/RtPgSeg.v's rs_piece_W11b_checks_stmt; nothing here restates a cut.

   THE CODE (lib/A/RtPgM02Base.v lists the whole half):
     MAL 0x82c9c lw a1,0(s5) (the hz cell at F+0x180, 0x5a5a5a5a, no instrumented check: a constant offset in the
         frame for locals); 0x82ca0 mv a0,s8 (= -1); 0x82ca4 jal check_malformed 0x836e4, whose return address is
         the join A 0x82ca8 itself.
     ABS 0x82b7c lw a1,0(s5); 0x82b80 mv a0,s8 (= 0); 0x82b84 jal check_absent 0x83690, ra = 0x82b88;
         0x82b88 ld s6,0x78(s1) (= F); 0x82b8c ld s10,0x58(s1) (= the flags byte); 0x82b90 j A.
   Each arm is one run of the engine with the hz cell as its only region, the callee's theorem through SRr_bind
   (RtPgCheck.rt_check_absent_A / rt_check_malformed_A) with RtPgM02Base.m2_pre_call for its rt_cpre and
   m2_core_call for rs_core at the return pc, and - for the absent arm - a second run from 0x82b88 with the two
   real-frame cells as its region. Both callees return at the float state they were called at and write no byte,
   so every state of this piece is at the cut's own float state fx2 and the whole of rs_cut_A's memory side is the
   cut's; ch_cut_A rebuilds it.

   SECTION HYPOTHESES: MTL : ameter_laws MT only (the frame's laws come from the kernel theorem
   YG0q.AR_laws_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSiteA RtPgSeg RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck RtPgM02Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* the registers both arms keep for the join's cut (rs_L_chk's five, s8 and sp); all are callee-saved and neither
   the runs nor the two callees write them *)
Definition ch_L : list (bv 5) := [2; 8; 9; 18; 20; 21; 24]%bv.
Lemma ch_L_cs : forall r, In r ch_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [ch_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
(* a register of the kept list, read through it *)
Ltac ch_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [ch_L In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* what reaching the join A means: rs_core, the registers of ch_L as at the check's cut, s6 = vF and s10 = vL,
   and every byte outside the callees' stack as at the cut *)
Definition ch_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word)
(W0 : world rsegs) (mem0 : word -> option byte) (vF vL : Z) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs0 regs3 ->
getr regs3 (Z_to_bv 5 22) = w64 vF -> getr regs3 (Z_to_bv 5 26) = w64 vL ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs M2_A regs3 mem3 md3) POST.

(* the enter step at a check's cut: the hz cell as the one region (s5 = F + 0x180, value 0x5a5a5a5a) *)
Ltac ch_enter :=
lazymatch goal with
| Hpre : rs_pre _ _ ?cx, Hcore : rs_core _ _ _ ?cx _ ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2,
  Hcell : val_mem _ _ (_ + 0x180) 4 _, E21 : bv_unsigned (ew _ 21) = _
  |- SRr rsegs ?W2 (cfg_at rsegs ?pc ?regs2 ?mem2 ?md2) _ =>
let HS := fresh "HS" in
pose proof (m2_entry pc [] [m2_hzcell (SLit 0x5a5a5a5a)] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SLit 0x5a5a5a5a) 0x5a5a5a5a);
  [exact E21 | lia | lia | reflexivity | lia | exact Hcell])
  ltac:(cbn; tauto) ltac:(repeat split));
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs2 []) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity);
let HJ := fresh "HJ" in pose proof (proj1 Hcore) as HJ;
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

(* ---- MAL 0x82c9c: lw a1,0(s5) (0x5a5a5a5a); mv a0,s8 (-1); jal check_malformed, ra = A ---- *)
Lemma ch_mal : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vL,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x180) -> getr regs2 (Z_to_bv 5 24) = w64 (-1) ->
getr regs2 (Z_to_bv 5 22) = w64 vF -> getr regs2 (Z_to_bv 5 26) = w64 vL ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x180) 4 0x5a5a5a5a ->
ch_K cx POST regs2 W2 mem2 vF vL ->
SRr rsegs W2 (cfg_at rsegs M2_MAL regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vL Hpre Hcore Hsp H21 H24 H22 H26 Hcell HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 []) 21) = q_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x180)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
ch_enter.
m2_run m2_awr. ck_keep m2_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 M2_A) by exact R1.
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [22; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2226;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_MALFORMED by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_malformed_A B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64, M2_A; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E24. exact H24.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
- etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2226 22%bv ltac:(cbv [In]; left; reflexivity))|]. exact H22.
- etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2226 26%bv ltac:(cbv [In]; right; left; reflexivity))|]. exact H26.
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)).
Qed.

(* ---- ABS 0x82b7c: lw a1,0(s5) (0x5a5a5a5a); mv a0,s8 (0); jal check_absent, ra = 0x82b88; then
       0x82b88 ld s6,0x78(s1); ld s10,0x58(s1); j A (the two real-frame cells as the one region, env slots
       32 / 33 = the flags byte and F) ---- *)
Lemma ch_abs : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vL,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x180) -> getr regs2 (Z_to_bv 5 24) = w64 0 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x180) 4 0x5a5a5a5a ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x78) 8 vF -> 0 <= vF < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x58) 8 vL -> 0 <= vL < 2 ^ 64 ->
ch_K cx POST regs2 W2 mem2 vF vL ->
SRr rsegs W2 (cfg_at rsegs M2_ABS regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vL Hpre Hcore Hsp H9 H21 H24 Hcell H78 HvF H58 HvL HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 []) 21) = q_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x180)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
ch_enter.
m2_run m2_awr. ck_keep m2_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82b88) by exact R1.
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_ABSENT by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_absent_A B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E24. exact H24.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x82b88 *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq ch_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
assert (Hsp3 : spZ regs3 = q_R (x_e rsegs cx)) by (rewrite (m2_sp_pres _ _ Hpres3); exact HspT).
assert (H93 : getr regs3 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx))) by (ch_get CL3 (9%bv : bv 5); exact H9).
assert (H783 : val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x78) 8 vF).
{ eapply (val_mem_kept rsegs); [|exact H78]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
assert (H583 : val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x58) 8 vL).
{ eapply (val_mem_kept rsegs); [|exact H58]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as HJ3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E9 : bv_unsigned (ew (Ereg regs3 [Z_to_bv 64 vL; Z_to_bv 64 vF]) 9) = q_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl);
    assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact H93;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (m2_entry 0x82b88 []
  [m2_frame 0 0x80 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))]]
  (mkFacts [] [] []) W3 regs3 [Z_to_bv 64 vL; Z_to_bv 64 vF] mem3 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_frame_ok _ W3 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
  [exact E9 | lia | lia | exact Hpres | lia |];
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (chunk_ok_val rsegs _ _ _ 0x58 8 (SOff 32 0) vL); [| cbn; lia | cbn; lia | exact H583];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (chunk_ok_val rsegs _ _ _ 0x78 8 (SOff 33 0) vF); [| cbn; lia | cbn; lia | exact H783];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia ])
  ltac:(cbn; tauto) ltac:(repeat split)).
remember (Ereg regs3 [Z_to_bv 64 vL; Z_to_bv 64 vF]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 vL; Z_to_bv 64 vF]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
change (cfg_at rsegs 0x82b88 regs3 mem3 md3) with (mkCfg (mkst regs3 (Z_to_bv 64 0x82b88) mem3 (seg_rom rsegs)) md3).
m2_run_to m2_awr M2_A. ck_keep m2_kwr.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
assert (E32 : ew E 32 = Z_to_bv 64 vL) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 vF) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2_A by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 _ _ _ Hcore3 ltac:(eassumption));
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- etransitivity; [exact R22|]. exact E33.
- etransitivity; [exact R26|]. exact E32.
- intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (K3 a Ha Hs).
Qed.
End w.

(* ======================================= the piece ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the bytes a cut of this half names and neither run nor callee writes: below the allocator's ceiling, or in the
   real frame at R and above *)
Lemma ch_far : forall cx : rs_scx rsegs, rs_pre rsegs B cx -> forall a,
(0 <= a < alloc_ceiling) \/ (q_R (x_e rsegs cx) <= a < q_R (x_e rsegs cx) + 0x1e0) ->
0 <= a < 2 ^ 64 /\ ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)).
Proof.
intros cx Hpre a Ha. pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in *. lia.
Qed.
Lemma ch_garr8_kept : forall H H' (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as (Hv & Hr). split; [|exact Hr].
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
replace k with 0 by lia. rewrite Z.add_0_r. exact (K j Hj).
Qed.

(* the join's cut from a check cut's facts, carried to a state whose memory agrees outside the callees' stack and
   whose registers of ch_L agree, with s6 = F and s10 = the flags byte *)
Lemma ch_cut_A : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx) -> rs_hz_at rsegs cx rec W2 mem2 ->
getr regs3 (Z_to_bv 5 24) = w64 (snd (rs_PA rsegs cx rec)) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x78) 8 (q_F (x_e rsegs cx) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0xc0) 8 (q_pp (x_e rsegs cx) mod 2 ^ 64) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 26) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_A (fx := fx) rsegs B MT cx fx2 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1) Hat Hhz H24 H78 Hc0 Hcore3 HL H22 H26 K3.
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2_pp B cx Hpre) as (P4096 & Pceil & _).
pose proof (ch_far cx Hpre) as Far.
pose proof ck_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                 (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, AC138, A21, AC18, AC58, AC20, AC38, AC40, AC48, AC50, AC120.
assert (Kcell : forall o v, 0 <= o -> o + 8 <= 0x1e0 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + o) 8 v).
{ intros o v Ho Hn Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  destruct (Far (q_R (x_e rsegs cx) + o + k) ltac:(right; lia)) as (Hb & Hs). apply K3; assumption. }
split; [|split].
- (* rs_chk_base *)
  split; [exact Hcore3|]. split; [exact Hfxk|].
  split.
  { apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
    assert (Hlen56 : Z.of_nat (length rs_PZ) = 56) by (vm_compute; reflexivity). rewrite Hlen56 in Hi.
    assert (Hsh : 0 <= shadow_addr (q_F (x_e rsegs cx)) + i < alloc_ceiling).
    { unfold shadow_addr, SHADOW_OFF.
      pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as M.
      assert (0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
      lia. }
    destruct (Far (shadow_addr (q_F (x_e rsegs cx)) + i) (or_introl Hsh)) as (Hb & Hs).
    apply K3; assumption. }
  split.
  { eapply (rtm_rom_kept rsegs); [exact Hrom|]. intros a (sg & Hsg & _ & Hr).
    pose proof (Hsegs a ltac:(exists sg; split; [exact Hsg | exact Hr])) as Hl. unfold kLowMemEnd in Hl.
    destruct (Far a ltac:(left; lia)) as (Hb & Hs). apply K3; assumption. }
  split.
  { unfold rs_pp_at in *. apply (ch_garr8_kept _ _ _ _ _ _ Hpp). intros j Hj.
    unfold rs_u8s in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes rec Hwf) as HL0.
    destruct (Far (q_pp (x_e rsegs cx) + Z.of_nat j) ltac:(left; lia))
      as (Hb & Hs). apply K3; assumption. }
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- (* the registers and cells *)
  unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
  + ch_get HL (8%bv : bv 5). exact A8.
  + ch_get HL (9%bv : bv 5). exact A9.
  + ch_get HL (20%bv : bv 5). exact A20.
  + ch_get HL (18%bv : bv 5). exact A18.
  + apply (Kcell 0x138); [lia | lia | exact AC138].
  + ch_get HL (21%bv : bv 5). exact A21.
  + apply (Kcell 0x18); [lia | lia | exact AC18].
  + apply (Kcell 0x58); [lia | lia | exact AC58].
  + apply (Kcell 0x20); [lia | lia | exact AC20].
  + apply (Kcell 0x38); [lia | lia | exact AC38].
  + apply (Kcell 0x40); [lia | lia | exact AC40].
  + apply (Kcell 0x48); [lia | lia | exact AC48].
  + apply (Kcell 0x50); [lia | lia | exact AC50].
  + apply (Kcell 0x120); [lia | lia | exact AC120].
  + exact H24.
  + exact H22.
  + exact H26.
  + apply (Kcell 0x78); [lia | lia | exact H78].
  + apply (Kcell 0xc0); [lia | lia | exact Hc0].
- (* the hz cell *)
  unfold rs_hz_at in *. eapply (val_mem_kept rsegs); [|exact Hhz]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  destruct (Far (q_F (x_e rsegs cx) + 0x180 + k) ltac:(left; lia)) as (Hb & Hs). apply K3; assumption.
Qed.

Theorem rt_m02_checks_A : rs_piece_W11b_checks_stmt rsegs B MT.
Proof using MTL.
unfold rs_piece_W11b_checks_stmt. intros cx POST inp Hst HA.
destruct Hst as (Hpre & _).
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
split.
- unfold rs_from_ABS. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HAb.
  destruct HAb as (Hbase & Hat & Hhz & Hn & H0).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat'.
  rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as (((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                     (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) & (A24 & AC78 & ACc0 & _)).
  cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, AC78, ACc0.
  assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  assert (Hcell : val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x180) 4 0x5a5a5a5a).
  { unfold rs_hz_at, rs_hz, Rate.written_or in Hhz. rewrite Hn in Hhz. cbn [fst] in Hhz.
    change (0x5a5a5a5a mod 2 ^ 32) with 0x5a5a5a5a in Hhz. exact Hhz. }
  apply (ch_abs (fx := fx2) B MT MTL cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A9 A21
    A24 Hcell AC78 ltac:(apply Z.mod_pos_bound; lia) AC58
    ltac:(apply Z.mod_pos_bound; lia)).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H22 H26 K3.
  apply (HA fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_A cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; assumption.
  + exact Hhz.
  + ch_get HL (24%bv : bv 5). rewrite H0. exact A24.
  + exact AC78.
  + exact ACc0.
  + exact Hcore3.
  + exact HL.
  + rewrite H22. apply m2_w64_mod.
  + rewrite H26. apply m2_w64_mod.
  + exact K3.
- unfold rs_from_MAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HM.
  destruct HM as (Hbase & Hat & Hhz & Hn & H1).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat'.
  rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as (((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                     (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) & (A24 & A22 & A26 & AC78 & ACc0 & _)).
  cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, A22, A26, AC78, ACc0.
  assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  assert (Hcell : val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x180) 4 0x5a5a5a5a).
  { unfold rs_hz_at, rs_hz, Rate.written_or in Hhz. rewrite Hn in Hhz. cbn [fst] in Hhz.
    change (0x5a5a5a5a mod 2 ^ 32) with 0x5a5a5a5a in Hhz. exact Hhz. }
  apply (ch_mal (fx := fx2) B MT MTL cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A21
    A24 A22 A26 Hcell).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H22 H26 K3.
  apply (HA fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_A cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; assumption.
  + exact Hhz.
  + ch_get HL (24%bv : bv 5). rewrite H1. exact A24.
  + exact AC78.
  + exact ACc0.
  + exact Hcore3.
  + exact HL.
  + exact H22.
  + exact H26.
  + exact K3.
Qed.
End m.

Print Assumptions rt_m02_checks_A.
