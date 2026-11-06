(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyV.v at 887bee7c56d (the value tail:
   the role's range test, check_role and the jump to T) and proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02KeyVB.v at
   f07713e8e823 (its join m2kv_jn_walk / m2kb_join: the entry state over the frame cell, the call through the seam of
   lib/AU/RtPgM02BaseB.v and the second run after the return) for reac-pw/fuzz_role image B (fuzz_role.asan-ubsan):
   image B's pcs (JN 0x824dc, check_role 0x82aac called from 0x824f0 with ra 0x824f4, MAL 0x824f8, T 0x82504); the
   role cell is at F+0x2a0 held in s4 (atom 20; image A: F+0x180 in s6); the code is s9 (image A: s8); the registers
   the join keeps are sp, rs_L_chk's six (m2k_L6) and s6, s8, s9, s10 (m2kv_L; image A: ch_L and s9, s11); the cut
   after the join is rebuilt by lib/AU/RPgM02KeyBase.v's m2k_cut_T (image A: lib/A/RPgM02Tail.v's ch_cut_T), and the
   run after the return enters a state with no region in place of image A's tl_enter. *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes). Proves no function
   (kind: segment lemma): rl_m02_key_tail_B : lib/AU/RPgM02KeyBase.v's m2k_join_stmt, JN 0x824dc -> MAL 0x824f8 /
   T 0x82504, a piece of LLVMFuzzerTestOneInput's segment M02.

   THE CODE (lib/AU/RPgM02Base.v lists it with every pc):
     0x824dc li a0,2; 0x824e0 bgeu a2,a0 -> MAL (the value is not a role); 0x824e4 lw a1,0(s4) (the role cell, no
     check: a constant offset in the frame for locals); 0x824e8 sext.w a2,a2; 0x824ec mv a0,s9 (= 1);
     0x824f0 jal check_role 0x82aac (ra 0x824f4); 0x824f4 j T 0x82504.
   check_role's contract is lib/AU/RPgCheck.v's rl_check_role_B; it returns at the float state it was called at and
   writes no byte outside its stack. Section hypotheses: MTL : ameter_laws MT and LAWS : AR_laws rsegs B. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck RPgCheckStr RPgM02Base RPgM02KeyBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers the join keeps beyond m2k_L6: s6 = pp, s8 = the flags byte, s9 = the code, s10 = F; all
   callee-saved, and neither the join's runs nor check_role write them *)
Definition m2kv_L : list (bv 5) := [22; 24; 25; 26]%bv.
Lemma m2kv_L_cs : forall r, In r m2kv_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kv_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Ltac m2kv_in := cbv [m2kv_L m2k_L6 In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Lemma m2kv_r234 : forall (regs regs' : bvmap 5 word), cs_eq [2; 3; 4]%bv regs regs' ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' H r Hr. destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
[left; apply bv_eq; reflexivity | right; left; apply bv_eq; reflexivity
| right; right; left; apply bv_eq; reflexivity].
Qed.

(* the role cell holds 0, 1 or 0x5a *)
Lemma m2kv_rcell_range : forall o, 0 <= rs_rcell o < 2 ^ 32.
Proof. intros [[|]|]; cbn [rs_rcell Role.role_z]; lia. Qed.

(* ======================================= the walk, at the configurations' float state ======================================= *)
Section kw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* 0x824dc li a0,2; 0x824e0 bgeu a2,a0 -> MAL 0x824f8; 0x824e4 lw a1,0(s4); 0x824e8 sext.w a2,a2; 0x824ec mv a0,s9;
   0x824f0 jal check_role (ra = 0x824f4); 0x824f4 j T 0x82504. The role cell is the one region (env slot 32 = its
   value cv); a2 = v is the atom of register 12. *)
Lemma m2kv_walk : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 v cv,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 20) = w64 (e_F (x_e rsegs cx) + 0x2a0) ->
getr regs2 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2a0) 4 cv -> 0 <= cv < 2 ^ 32 ->
(v < 2 -> getr regs2 (Z_to_bv 5 25) = w64 1 /\ cv = v) ->
(2 <= v -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
  cs_eq m2k_L6 regs2 regs3 -> cs_eq m2kv_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (cfg_at rsegs M2_MAL regs3 mem3 md3) POST) ->
(v < 2 -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
  cs_eq m2k_L6 regs2 regs3 -> cs_eq m2kv_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (cfg_at rsegs M2_T regs3 mem3 md3) POST) ->
SRr rsegs W2 (cfg_at rsegs M2K_JN regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 v cv Hpre Hcore Hsp H20 H12 Hv Hcell Hcv Hlt KMAL KT.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E20 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 cv]) 20) = e_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl);
    assert (G : getr regs2 20%bv = w64 (e_F (x_e rsegs cx) + 0x2a0)) by exact H20;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs2 [Z_to_bv 64 cv]) (SOff 32 0) = Z_to_bv 64 cv)
by (apply (m2k_den_extra regs2 _ 0 cv); [reflexivity | lia]).
pose proof (m2_entry M2K_JN [] [m2_rcell (SOff 32 0)] (mkFacts [] [] []) W2 regs2 [Z_to_bv 64 cv] mem2
  (Forall_nil _) eq_refl
  ltac:(apply Forall_cons; [exact (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SOff 32 0) cv E20 ltac:(lia) ltac:(lia)
    D32 Hcv Hcell) | apply Forall_nil])
  ltac:(cbn; tauto) ltac:(repeat split)) as HS.
remember (Ereg regs2 [Z_to_bv 64 cv]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 cv]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 v)
by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl); exact H12).
assert (E25 : ew E 25 = getr regs2 (Z_to_bv 5 25)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 cv) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2K_JN) with (Z_to_bv 64 M2K_JN).
(* 0x824dc li a0,2; stop at 0x824e0 bgeu a2,a0 *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_geu_U, (U_atom E 12 v E12 Hv), U_lit in Hb by lia.
- (* taken: v >= 2, to MAL *)
  assert (Hv2 : 2 <= v) by (destruct (Z.ltb_spec v 2); [discriminate Hb | lia]).
  m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2k_L6 HS HAE ltac:(vm_compute; reflexivity)) as CL;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2kv_L HS HAE ltac:(vm_compute; reflexivity)) as CV;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hv2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT); [| exact CL | exact CV |];
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
      (m2kv_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x))
  | intros a Ha _; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: v < 2, check_role *)
  assert (Hv2 : v < 2) by (destruct (Z.ltb_spec v 2); [lia | discriminate Hb]).
  destruct (Hlt Hv2) as (H25 & Hcvv).
  m2_run m2_awr. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
  let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
  m2k_rsv HS (11%bv : bv 5) G11.
  m2k_rsv HS (12%bv : bv 5) G12.
  assert (R1' : getr (ms_regs msT) 1 = w64 0x824f4) by exact R1.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2k_L6 HS HAE ltac:(vm_compute; reflexivity)) as CL;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2kv_L HS HAE ltac:(vm_compute; reflexivity)) as CV;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with A_CHECK_ROLE by (vm_compute; reflexivity)
  end.
  assert (HspT : spZ (ms_regs msT) = e_R (x_e rsegs cx))
  by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
  by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ
        (m2kv_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2_io | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
  end.
  assert (U11 : U E (SExt true 32 (SOff 32 0)) = v)
  by (rewrite (m2k_U_sext32 E 32 cv E32 Hcv), Hcvv; apply m2k_sx_id; lia).
  assert (U12 : U E (SAluw ALU_ADD (SOff 12 0) (SLit 0)) = v)
  by (apply m2k_U_sextw; [exact (U_atom E 12 v E12 Hv) | lia]).
  eapply SRr_bind.
  { apply (rl_check_role_B B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
      (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _
      (x_k rsegs cx) (ms_regs msT)).
    - apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T_check_STK Hpre HcoreT);
      [ rewrite R1'; vm_compute; reflexivity
      | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
      | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
    - etransitivity; [exact R10|]. rewrite E25. exact H25.
    - etransitivity; [exact G11|]. etransitivity; [|symmetry; exact G12].
      rewrite !denot_lit_U, U11, U12. reflexivity. }
  intros W3 c3 _ Hpost.
  destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ _ _ W3 c3
    Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
  as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
  subst fx3 c3. rewrite R1'.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
    exact (KE a Ha (fun x => x)). }
  assert (CL3 : cs_eq m2k_L6 regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres m2k_L6 _ _ m2k_L6_cs Hpres3)).
  assert (CV3 : cs_eq m2kv_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CV (cs_eq_of_pres m2kv_L _ _ m2kv_L_cs Hpres3)).
  clear dependent msT. clear dependent E.
  (* 0x824f4 j T: one run with no region to 0x82504 *)
  pose proof (proj1 Hcore3) as HJ3.
  pose proof (m2_entry 0x824f4 [] [] (mkFacts [] [] []) W3 regs3 [] mem3 (Forall_nil _) eq_refl (Forall_nil _)
    ltac:(cbn; tauto) ltac:(repeat split)) as HS.
  remember (Ereg regs3 []) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
  change (w64 0x824f4) with (Z_to_bv 64 0x824f4).
  m2_run_to m2_awr M2_T. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2k_L6 HS HAE ltac:(vm_compute; reflexivity)) as CL';
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2kv_L HS HAE ltac:(vm_compute; reflexivity)) as CV';
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234';
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_T by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KT Hv2 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT Hcore3 HJ
      (m2kv_r234 _ _ C234') eq_refl (Permutation_refl _)); [m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x))
  | exact (cs_eq_trans _ _ _ _ CL3 CL')
  | exact (cs_eq_trans _ _ _ _ CV3 CV')
  | intros a Ha Hs; rewrite (KE a Ha (fun x => x)); exact (K3 a Ha Hs) ]
  end.
Qed.
End kw.

(* ======================================= the piece ======================================= *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ---- JN -> MAL / T ---- *)
Lemma rl_m02_key_tail_B : m2k_join_stmt B MT.
Proof using MTL LAWS.
unfold m2k_join_stmt, m2k_K_join.
intros cx POST rec Hpre HMAL HT fx3 ly3 S3 W3 regs3 mem3 md3 v HcT H12 Hv Hlt Hge.
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof HcT as (Hbase & Hat & Hro).
pose proof Hbase as (Hcore & Hfxk & _).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'.
rewrite Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as ((A8 & A9 & A19 & A27 & A18 & A20 & AC20 & AC40 & _) &
                  (A25 & A22 & A24 & A26 & AC38 & AC140 & _)).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A27, A18, A20, AC20, AC40, A25, A22, A24, A26, AC38, AC140.
assert (HatFP : rs_at_cx rsegs cx W3 mem3 regs3 (rs_L_chk rsegs cx ++ m2k_L_FP cx)).
{ unfold rs_at_cx, rs_at, rs_L_chk, m2k_L_FP. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; assumption. }
assert (Hsp : spZ regs3 = e_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
pose proof (m2kv_rcell_range (fst (rs_PA rsegs cx rec))) as Hcv.
pose proof Hro as Hro'. unfold rs_role_at in Hro'.
(* the kept registers give T's four beyond rs_L_chk at a later state *)
assert (KT4 : forall regs4, cs_eq m2kv_L regs3 regs4 ->
  getr regs4 (Z_to_bv 5 25) = w64 (snd (rs_PA rsegs cx rec)) /\
  getr regs4 (Z_to_bv 5 22) = w64 (e_pp (x_e rsegs cx)) /\
  getr regs4 (Z_to_bv 5 24) = w64 (e_fl (x_e rsegs cx)) /\
  getr regs4 (Z_to_bv 5 26) = w64 (e_F (x_e rsegs cx))).
{ intros regs4 CV.
  split; [etransitivity; [exact (CV 25%bv ltac:(m2kv_in))|]; exact A25|].
  split; [etransitivity; [exact (CV 22%bv ltac:(m2kv_in))|]; exact A22|].
  split; [etransitivity; [exact (CV 24%bv ltac:(m2kv_in))|]; exact A24|].
  etransitivity; [exact (CV 26%bv ltac:(m2kv_in))|]; exact A26. }
apply (m2kv_walk (fx := fx3) B MT MTL LAWS cx POST ly3 S3 W3 regs3 mem3 md3 v (rs_rcell (fst (rs_PA rsegs cx rec)))
  Hpre Hcore Hsp A20 H12 Hv Hro' Hcv).
- intros Hv2. destruct (Hlt Hv2) as (H1 & H2). split; [rewrite <- H1; exact A25 | exact H2].
- intros Hv2 ly4 S4 W4 regs4 mem4 md4 Hcore4 CL CV K4.
  destruct (Hge Hv2) as (Hn & Hm1).
  destruct (KT4 regs4 CV) as (H25 & H22 & H24 & H26).
  apply (HMAL fx3 ly4 S4 W4 regs4 mem4 md4 rec).
  apply (m2k_mal_of_T B MT cx fx3 rec ly4 S4 W4 regs4 mem4 md4); [| exact Hn | exact Hm1].
  apply (m2k_cut_T B MT LAWS cx fx3 fx3 rec ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase Hro HatFP
    Hcore4 Hfxk (m2k_cs_sub _ _ _ _ m2k_L5_L6 CL) H25 H22 H24 H26).
  intros a Ha Hz. apply K4; [exact Ha|]. intros Hs. apply Hz. left. exact Hs.
- intros Hv2 ly4 S4 W4 regs4 mem4 md4 Hcore4 CL CV K4.
  destruct (KT4 regs4 CV) as (H25 & H22 & H24 & H26).
  apply (HT fx3 ly4 S4 W4 regs4 mem4 md4 rec).
  apply (m2k_cut_T B MT LAWS cx fx3 fx3 rec ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase Hro HatFP
    Hcore4 Hfxk (m2k_cs_sub _ _ _ _ m2k_L5_L6 CL) H25 H22 H24 H26).
  intros a Ha Hz. apply K4; [exact Ha|]. intros Hs. apply Hz. left. exact Hs.
Qed.
End k.
