(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e887 (its two check
   walks ch_mal / ch_abs and the cut lemma ch_cut_T, with the call-in-the-middle pattern they take from
   lib/A/RPgCheckStr.v) for reac-pw/fuzz_rate image A: role's pcs become rate's (ABS 0x82b7c, MAL 0x82c9c, the
   join A 0x82ca8), the one-byte role cell becomes rate's four-byte hz cell holding 0x5a5a5a5a, the register the
   cell's address lives in moves from role's s6 to rate's s5 (atom 21), the two real-frame cells the absent arm
   reloads are rate's R+0x78 (F) and R+0x58 (the flags byte) instead of role's R+0x28 and R+0x80, and the join's
   cut is rs_cut_A, which carries the flags byte where role's rs_cut_T carried the first block. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Chk.v at 48d3cf0d8e40; for image B
   (fuzz_rate.asan-ubsan): image B's pcs (ABS 0x82d1c, MAL 0x82de0, the join A 0x82dec), the hz cell at F+0x2a0, the
   code in s10 instead of s8, the absent arm's first run reads the code from the real-frame cell R+0x170 and its
   second run reloads the mask (R+0x148) into s6 and the flags byte (R+0x50) into s7, the join's cut is
   lib/AU/RtPgSegB.v's rsb_cut_A (s10 = the code, s6 = the mask, s7 = the flags byte), rebuilt by
   lib/AU/RtPgM02KitB.v's chb_cut_A, which now holds the shared lemmas ch_L, ch_far, ch_garr8_kept and ch_cut_A. *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves
   no function (kind: segment lemma): the piece W11b-checks of LLVMFuzzerTestOneInput's segment M02, whose statement
   is lib/AU/RtPgSegB.v's rsb_piece_W11b_checks_stmt; nothing here restates a cut.

   THE CODE (lib/AU/RtPgM02BaseB.v lists the whole half):
     MAL 0x82de0 lw a1,0(s5) (the hz cell at F+0x2a0, 0x5a5a5a5a, no instrumented check: a constant offset in the
         frame for locals); 0x82de4 mv a0,s10 (= -1); 0x82de8 jal check_malformed 0x835b4, whose return address is
         the join A 0x82dec itself.
     ABS 0x82d1c lw a1,0(s5); 0x82d20 ld s10,0x170(s1) (the code, 0); 0x82d24 mv a0,s10; 0x82d28 jal check_absent
         0x83558, ra = 0x82d2c; 0x82d2c ld s6,0x148(s1) (the mask); 0x82d30 ld s7,0x50(s1) (the flags byte);
         0x82d34 j A.
   Each arm is one run of the engine up to the call (MAL: the hz cell as its one region; ABS: the hz cell and the
   real-frame cell R+0x170), the callee's theorem through SRr_bind (RtPgCheck.rt_check_absent_B /
   rt_check_malformed_B) with RtPgM02BaseB.m2b_pre_call for its rt_cpre and m2b_core_call for rsb_core at the return
   pc, and - for the absent arm - a second run from 0x82d2c with the two real-frame cells R+0x50 and R+0x148 as its
   region (env slots 32 / 33). Both callees return at the float state they were called at and write no byte, so
   every state of this piece is at the cut's own float state fx2 and the whole of rsb_cut_A's memory side is the
   cut's; RtPgM02KitB.chb_cut_A rebuilds it.

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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB RtPgM02KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* the return address of check_absent: ld s6,0x148(s1) *)
Definition CHB_ABS_RET : Z := 0x82d2c.

(* the state of a run's start, after its st_ok HS: the env E, the shadow seam (no shadow entry), the kept-memory
   fact KE and the journal HJ, and the goal in the engine's form *)
Ltac chb_env Hcore W2 regs2 extra mem2 pc :=
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs2 extra) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs2 extra) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity);
let HJ := fresh "HJ" in pose proof (proj1 Hcore) as HJ;
try unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc).

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* what reaching the join A means: rsb_core, the registers of chb_L as at the check's cut, s10 = v26, s6 = v22 and
   s7 = v23, and every byte outside the callees' stack as at the cut *)
Definition chb_K (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word)
(W0 : world rsegs) (mem0 : word -> option byte) (v26 v22 v23 : Z) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq chb_L regs0 regs3 ->
getr regs3 (Z_to_bv 5 26) = w64 v26 -> getr regs3 (Z_to_bv 5 22) = w64 v22 ->
getr regs3 (Z_to_bv 5 23) = w64 v23 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs M2B_A regs3 mem3 md3) POST.

(* ---- MAL 0x82de0: lw a1,0(s5) (0x5a5a5a5a); mv a0,s10 (-1); jal check_malformed, ra = A ---- *)
Lemma chb_mal : forall (cx : rsb_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vM vL,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x2a0) -> getr regs2 (Z_to_bv 5 26) = w64 (-1) ->
getr regs2 (Z_to_bv 5 22) = w64 vM -> getr regs2 (Z_to_bv 5 23) = w64 vL ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x2a0) 4 0x5a5a5a5a ->
chb_K cx POST regs2 W2 mem2 (-1) vM vL ->
SRr rsegs W2 (cfg_at rsegs M2B_MAL regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vM vL Hpre Hcore Hsp H21 H26 H22 H23 Hcell HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 []) 21) = q_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x2a0)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
(* the run's start: the hz cell (s5 = F + 0x2a0, atom 21) as its one region *)
pose proof (m2b_entry M2B_MAL [] [m2b_hzcell (SLit 0x5a5a5a5a)] (mkFacts [] [] []) W2 regs2 [] mem2
  (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2b_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SLit 0x5a5a5a5a) 0x5a5a5a5a);
  [exact E21 | lia | lia | reflexivity | lia | exact Hcell])
  ltac:(cbn; tauto) ltac:(repeat split)).
chb_env Hcore W2 regs2 constr:(@nil word) mem2 M2B_MAL.
m2b_run m2b_awr. ck_keep m2b_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 M2B_A) by exact R1.
assert (E26 : ew E 26 = getr regs2 (Z_to_bv 5 26)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ chb_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [22; 23; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_MALFORMED by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2b_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore
      ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_malformed_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2b_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64, M2B_A; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E26. exact H26.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres chb_L _ _ chb_L_cs Hpres3)).
- etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2 26%bv ltac:(cbv [In]; right; right; left; reflexivity))|]. exact H26.
- etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2 22%bv ltac:(cbv [In]; left; reflexivity))|]. exact H22.
- etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2 23%bv ltac:(cbv [In]; right; left; reflexivity))|]. exact H23.
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)).
Qed.

(* ---- ABS 0x82d1c: lw a1,0(s5) (0x5a5a5a5a); ld s10,0x170(s1) (0); mv a0,s10; jal check_absent, ra = 0x82d2c;
       then 0x82d2c ld s6,0x148(s1); ld s7,0x50(s1); j A (the two real-frame cells as the one region, env slots
       32 / 33 = the flags byte and the mask) ---- *)
Lemma chb_abs : forall (cx : rsb_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vM vL,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x2a0) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x2a0) 4 0x5a5a5a5a ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x170) 8 0 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x148) 8 vM -> 0 <= vM < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x50) 8 vL -> 0 <= vL < 2 ^ 64 ->
chb_K cx POST regs2 W2 mem2 0 vM vL ->
SRr rsegs W2 (cfg_at rsegs M2B_ABS regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vM vL Hpre Hcore Hsp H9 H21 Hcell H170 H148 HvM H50 HvL HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 []) 21) = q_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x2a0)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (E9 : bv_unsigned (ew (Ereg regs2 []) 9) = q_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl);
    assert (G : getr regs2 9%bv = w64 (q_R (x_e rsegs cx))) by exact H9;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (proj1 Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
(* the first run's start: the hz cell (atom 21) and the real-frame cell R+0x170 (atom 9 = R), read only *)
pose proof (m2b_entry M2B_ABS []
  [m2b_hzcell (SLit 0x5a5a5a5a); m2b_frame 0x170 0x178 0 0 [YP09.mkChunk 0x170 (CVal 8 (SLit 0))]]
  (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (m2b_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SLit 0x5a5a5a5a) 0x5a5a5a5a);
    [exact E21 | lia | lia | reflexivity | lia | exact Hcell]
  | apply (m2b_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres0 | lia |];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val rsegs _ _ _ 0x170 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact H170] ])
  ltac:(change (((bv_unsigned (ew (Ereg regs2 []) 21) + 4 <= bv_unsigned (ew (Ereg regs2 []) 9) + 0x170 \/
                  bv_unsigned (ew (Ereg regs2 []) 9) + 0x178 <= bv_unsigned (ew (Ereg regs2 []) 21) + 0) /\ True) /\
                (True /\ True));
        rewrite E21, E9; refine (conj (conj _ I) (conj I I)); left; unfold T_SEG_STK, ASTACK in *; lia)
  ltac:(repeat split)).
chb_env Hcore W2 regs2 constr:(@nil word) mem2 M2B_ABS.
m2b_run m2b_awr. ck_keep m2b_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 CHB_ABS_RET) by exact R1.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ chb_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_ABSENT by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2b_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore
      ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_absent_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2b_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64, CHB_ABS_RET; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - exact R10.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x82d2c *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq chb_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres chb_L _ _ chb_L_cs Hpres3)).
assert (H93 : getr regs3 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx))) by (m2kb_get CL3 (9%bv : bv 5); exact H9).
assert (R263 : getr regs3 (Z_to_bv 5 26) = w64 0)
by (etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|]; exact R26).
assert (H1483 : val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x148) 8 vM).
{ eapply (val_mem_kept rsegs); [|exact H148]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
assert (H503 : val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x50) 8 vL).
{ eapply (val_mem_kept rsegs); [|exact H50]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E9 : bv_unsigned (ew (Ereg regs3 [Z_to_bv 64 vL; Z_to_bv 64 vM]) 9) = q_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl);
    assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact H93;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (m2b_entry CHB_ABS_RET []
  [m2b_frame 0 0x150 0 0 [YP09.mkChunk 0x50 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0))]]
  (mkFacts [] [] []) W3 regs3 [Z_to_bv 64 vL; Z_to_bv 64 vM] mem3 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2b_frame_ok _ W3 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
  [exact E9 | lia | lia | exact Hpres | lia |];
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (chunk_ok_val rsegs _ _ _ 0x50 8 (SOff 32 0) vL); [| cbn; lia | cbn; lia | exact H503];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (chunk_ok_val rsegs _ _ _ 0x148 8 (SOff 33 0) vM); [| cbn; lia | cbn; lia | exact H1483];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia ])
  ltac:(cbn; tauto) ltac:(repeat split)).
chb_env Hcore3 W3 regs3 constr:([Z_to_bv 64 vL; Z_to_bv 64 vM]) mem3 CHB_ABS_RET.
m2b_run_to m2b_awr M2B_A. ck_keep m2b_kwr.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
assert (E32 : ew E 32 = Z_to_bv 64 vL) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 vM) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ chb_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C26;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2B_A by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2b_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 _ _ _ Hcore3 ltac:(eassumption));
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- etransitivity; [exact (C26 26%bv ltac:(cbv [In]; left; reflexivity))|]. exact R263.
- etransitivity; [exact R22|]. exact E33.
- etransitivity; [exact R23|]. exact E32.
- intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (K3 a Ha Hs).
Qed.
End w.

(* ======================================= the piece ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Theorem rt_m02_checks_B : rsb_piece_W11b_checks_stmt rsegs B MT.
Proof using MTL.
unfold rsb_piece_W11b_checks_stmt. intros cx POST inp Hst HA.
destruct Hst as (Hpre & _).
pose proof (m2b_stack B cx Hpre) as (HR & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
split.
- unfold rsb_from_ABS. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HAb.
  destruct HAb as (Hbase & Hat & Hhz & Hn & H0).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat'.
  rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as (((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                     (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) & (AC170 & AC60 & AC168 & _)).
  cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, A21, AC50, AC148, AC170, AC60, AC168.
  assert (AC170' : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x170) 8 0) by exact AC170.
  assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  assert (Hcell : val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x2a0) 4 0x5a5a5a5a).
  { unfold rsb_hz_at, rsb_hz, Rate.written_or in Hhz. rewrite Hn in Hhz. cbn [fst] in Hhz.
    change (0x5a5a5a5a mod 2 ^ 32) with 0x5a5a5a5a in Hhz. exact Hhz. }
  apply (chb_abs (fx := fx2) B MT MTL cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A9 A21
    Hcell AC170' AC148 ltac:(apply Z.mod_pos_bound; lia) AC50 ltac:(apply Z.mod_pos_bound; lia)).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H26 H22 H23 K3.
  apply (HA fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (chb_cut_A B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc, m2kb_L_FP. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; assumption.
  + exact Hhz.
  + exact Hcore3.
  + exact HL.
  + rewrite H0. exact H26.
  + rewrite H22. apply m2b_w64_mod.
  + rewrite H23. apply m2b_w64_mod.
  + exact K3.
- unfold rsb_from_MAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HM.
  destruct HM as (Hbase & Hat & Hhz & Hn & H1).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat'.
  rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as (((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                     (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) & (A26 & A22 & A23 & AC60 & AC168 & _)).
  cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, A21, A26, A22, A23, AC60, AC168.
  assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  assert (Hcell : val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x2a0) 4 0x5a5a5a5a).
  { unfold rsb_hz_at, rsb_hz, Rate.written_or in Hhz. rewrite Hn in Hhz. cbn [fst] in Hhz.
    change (0x5a5a5a5a mod 2 ^ 32) with 0x5a5a5a5a in Hhz. exact Hhz. }
  apply (chb_mal (fx := fx2) B MT MTL cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A21
    A26 A22 A23 Hcell).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H26 H22 H23 K3.
  apply (HA fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (chb_cut_A B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc, m2kb_L_FP. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; assumption.
  + exact Hhz.
  + exact Hcore3.
  + exact HL.
  + rewrite H1. exact H26.
  + exact H22.
  + exact H23.
  + exact K3.
Qed.
End m.

Print Assumptions rt_m02_checks_B.
