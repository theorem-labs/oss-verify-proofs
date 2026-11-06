(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc) for the common value
   tail of reac-pw/fuzz_role's image-A segment M02 (0x823e0 .. 0x823f8: the role's range test, check_role, the jump
   to T). *)
(* reac-pw/fuzz_role, image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes). Proves no function
   (kind: segment lemma): rl_m02_key_tail, the last block both value arms of the key piece (Int and Float) jump into,
   for lib/A/RPgM02Key.v.

   THE CODE: 0x823e0 li a0,2; 0x823e4 bgeu a2,a0 -> MAL 0x823fc; 0x823e8 lw a1,0(s6) (the role cell, no check);
   0x823ec sext.w a2,a2; 0x823f0 mv a0,s8; 0x823f4 jal check_role 0x82bdc (ra = 0x823f8); 0x823f8 j T 0x82408.
   a2 = v is the value the arm read. v >= 2: the run goes to MAL with the answer (None, -1). v < 2: the answer is
   (Some role, 1) with the role cell holding v, so check_role's two premises hold: a0 = s8 = 1, and a1 (the cell,
   sign-extended by the `lw`) = a2 (sign-extended by the `sext.w`) = v (lib/A/RPgM02KeyBase.v's m2k_U_sext32 and
   m2k_U_sextw); after the call
   one run with no region takes the `j` to T. The cuts MAL and T are RPgSeg's, rebuilt by RPgM02Tail.ch_cut_T from
   the facts of the state at 0x823e0 (the six registers of ch_L and s9 / s11 kept, no byte outside the callees'
   stack written). Section hypotheses: MTL : ameter_laws MT and LAWS : AR_laws rsegs B; nothing else is assumed. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSiteA RPgSeg RPgMem RPgScanF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgCheck RPgCheckStr RPgRefuse RPgCfgChanges RPgCfgApply.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02Base.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02Tail RPgM02KeyBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the two sign extensions of 0x823e8 `lw a1,0(s6)` and 0x823ec `sext.w a2,a2` are lib/A/RPgM02KeyBase.v's
   m2k_sx / m2k_sx_id / m2k_U_sext32 / m2k_U_sextw *)
(* a register's value as the denotation of its symbolic value, without unfolding sv_denot *)
Ltac m2k_rsv HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hr : getr (ms_regs ms) r = sv_denot E e)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) (f_equal (sv_denot E) _)); vm_compute; reflexivity)
end.

(* ======================================= the walk, at the configurations' float state ======================================= *)
Section kw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* 0x823e0 li a0,2; 0x823e4 bgeu a2,a0 -> MAL 0x823fc; 0x823e8 lw a1,0(s6); 0x823ec sext.w a2,a2; 0x823f0 mv a0,s8;
   0x823f4 jal check_role (ra = 0x823f8); 0x823f8 j T 0x82408. The role cell is the one region (env slot 32 = its
   value cv); a2 = v is the atom of s2's neighbour register 12. *)
Lemma m2k_walk : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 v cv,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 22) = w64 (e_F (x_e rsegs cx) + 0x180) ->
getr regs2 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x180) 4 cv -> 0 <= cv < 2 ^ 32 ->
(v < 2 -> getr regs2 (Z_to_bv 5 24) = w64 1 /\ cv = v) ->
(2 <= v -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
  cs_eq ch_L regs2 regs3 -> cs_eq [25; 27]%bv regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (cfg_at rsegs 0x823fc regs3 mem3 md3) POST) ->
(v < 2 -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
  cs_eq ch_L regs2 regs3 -> cs_eq [25; 27]%bv regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (cfg_at rsegs 0x82408 regs3 mem3 md3) POST) ->
SRr rsegs W2 (cfg_at rsegs 0x823e0 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 v cv Hpre Hcore Hsp H22 H12 Hv Hcell Hcv Hlt KMAL KT.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E22 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 cv]) 22) = e_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl);
    assert (G : getr regs2 22%bv = w64 (e_F (x_e rsegs cx) + 0x180)) by exact H22;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs2 [Z_to_bv 64 cv]) (SOff 32 0) = Z_to_bv 64 cv).
{ apply bv_eq. rewrite denot_SOff, Z.add_0_r. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth].
  rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
pose proof (m2_entry 0x823e0 [] [m2_rcell (SOff 32 0)] (mkFacts [] [] []) W2 regs2 [Z_to_bv 64 cv] mem2
  (Forall_nil _) eq_refl
  ltac:(apply Forall_cons; [exact (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SOff 32 0) cv E22 ltac:(lia) ltac:(lia)
    D32 Hcv Hcell) | apply Forall_nil])
  ltac:(cbn; tauto) ltac:(repeat split)) as HS.
remember (Ereg regs2 [Z_to_bv 64 cv]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 cv]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 v)
by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl); exact H12).
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 cv) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x823e0) with (Z_to_bv 64 0x823e0).
(* 0x823e0 li a0,2; stop at 0x823e4 bgeu a2,a0 *)
m2_run m2_awr. ck_keep kwr_stk.
m2_branch Hb.
all: rewrite branch_geu_U, (U_atom E 12 v E12 Hv), U_lit in Hb by lia.
- (* taken: v >= 2, to MAL *)
  assert (Hv2 : 2 <= v) by (destruct (Z.ltb_spec v 2); [discriminate Hb | lia]).
  m2_run_to m2_awr 0x823fc. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [25; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2527;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with 0x823fc by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hv2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT); [| exact CL | exact C2527 |];
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
      (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x))
  | intros a Ha _; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: v < 2, check_role *)
  assert (Hv2 : v < 2) by (destruct (Z.ltb_spec v 2); [lia | discriminate Hb]).
  destruct (Hlt Hv2) as (H24 & Hcvv).
  m2_run m2_awr. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
  let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
  m2k_rsv HS (11%bv : bv 5) G11.
  m2k_rsv HS (12%bv : bv 5) G12.
  assert (R1' : getr (ms_regs msT) 1 = w64 0x823f8) by exact R1.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [25; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2527;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with A_CHECK_ROLE by (vm_compute; reflexivity)
  end.
  assert (HspT : spZ (ms_regs msT) = e_R (x_e rsegs cx)) by (rewrite (tl_sp_of_cs _ _ C234); exact Hsp).
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
  by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ
        (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
  end.
  assert (U11 : U E (SExt true 32 (SOff 32 0)) = v)
  by (rewrite (m2k_U_sext32 E 32 cv E32 Hcv), Hcvv; apply m2k_sx_id; lia).
  assert (U12 : U E (SAluw ALU_ADD (SOff 12 0) (SLit 0)) = v)
  by (apply m2k_U_sextw; [exact (U_atom E 12 v E12 Hv) | lia]).
  eapply SRr_bind.
  { apply (rl_check_role_A B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
      (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _
      (x_k rsegs cx) (ms_regs msT)).
    - apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T_check_STK Hpre HcoreT);
      [ rewrite R1'; vm_compute; reflexivity
      | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
      | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
    - etransitivity; [exact R10|]. rewrite E24. exact H24.
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
  assert (CL3 : cs_eq ch_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
  assert (C3 : cs_eq [25; 27]%bv regs2 regs3).
  { apply (cs_eq_trans _ _ _ _ C2527). apply cs_eq_of_pres; [|exact Hpres3].
    intros r Hr. cbv [In] in Hr. unfold acallee_saved.
    destruct Hr as [<- | [<- | []]];
    lazymatch goal with |- context [bv_unsigned ?x] => let w := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with w end;
    lia. }
  clear dependent msT. clear dependent E.
  (* 0x823f8 j T: one run with no region to 0x82408 *)
  change (SRr rsegs W3 (cfg_at rsegs 0x823f8 regs3 mem3 md3) POST).
  pose proof (proj1 Hcore3) as HJ3.
  tl_enter.
  m2_run_to m2_awr 0x82408. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [25; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2527';
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234';
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with 0x82408 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KT Hv2 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT Hcore3 HJ
      (tl_r234 _ _ C234') eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x))
  | exact (cs_eq_trans _ _ _ _ CL3 CL')
  | exact (cs_eq_trans _ _ _ _ C3 C2527')
  | intros a Ha Hs; rewrite (KE a Ha (fun x => x)); exact (K3 a Ha Hs) ]
  end.
Qed.
End kw.

(* ======================================= the statement M02Key's piece uses ======================================= *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma rl_m02_key_tail : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : Model.pod_rec)
  (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 (v : Z),
rs_pre rsegs B cx ->
@rs_from_MAL fx rc SK rsegs B MT cx POST ->
@rs_from_T fx rc SK rsegs B MT cx POST ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 ->
Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                         (LReg 27, e_pp (x_e rsegs cx))]) ->
getr regs2 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
(v < 2 -> snd (rs_PA rsegs cx rec) = 1 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = v) ->
(2 <= v -> fst (rs_PA rsegs cx rec) = None /\ snd (rs_PA rsegs cx rec) = -1) ->
SRr rsegs W2 (@cfg_at fx2 rsegs 0x823e0 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST rec fx2 ly2 S2 W2 regs2 mem2 md2 v Hpre HMAL HT Hbase Hrole Hlen Hat H12 Hv Hlt Hge.
pose proof Hbase as (Hcore & _).
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'. rewrite Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & A25 & A27 & _).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30, A24, A25, A27.
assert (HatL : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx)).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app in Hat. exact (proj1 Hat). }
assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (Hcv : 0 <= rs_rcell (fst (rs_PA rsegs cx rec)) < 2 ^ 32)
by (destruct (rk_rcell_cases (fst (rs_PA rsegs cx rec))) as [E|[E|E]]; rewrite E; lia).
pose proof Hrole as Hrole'. unfold rs_role_at in Hrole'.
apply (m2k_walk (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 v (rs_rcell (fst (rs_PA rsegs cx rec)))
  Hpre Hcore Hsp A22 H12 Hv Hrole' Hcv).
- intros Hv2. destruct (Hlt Hv2) as (H1 & H2). split; [rewrite <- H1; exact A24 | exact H2].
- intros Hv2 ly3 S3 W3 regs3 mem3 md3 Hcore3 CL C2527 K3.
  destruct (Hge Hv2) as (Hn & Hm1).
  assert (H25 : getr regs3 (Z_to_bv 5 25) = w64 (e_F (x_e rsegs cx)))
  by (etransitivity; [exact (C2527 25%bv ltac:(cbv [In]; left; reflexivity))|]; exact A25).
  assert (H27 : getr regs3 (Z_to_bv 5 27) = w64 (e_pp (x_e rsegs cx)))
  by (etransitivity; [exact (C2527 27%bv ltac:(cbv [In]; right; left; reflexivity))|]; exact A27).
  destruct (ch_cut_T (fx := fx) B MT LAWS cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase
    HatL Hrole A24 Hcore3 CL H25 H27 K3) as (Hb3 & Ha3 & Hr3).
  apply (HMAL fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  unfold rs_cut_MAL. rewrite Hm1 in Ha3.
  split; [exact Hb3|]. split; [exact Ha3|]. split; [exact Hr3|]. split; [exact Hn | exact Hm1].
- intros Hv2 ly3 S3 W3 regs3 mem3 md3 Hcore3 CL C2527 K3.
  assert (H25 : getr regs3 (Z_to_bv 5 25) = w64 (e_F (x_e rsegs cx)))
  by (etransitivity; [exact (C2527 25%bv ltac:(cbv [In]; left; reflexivity))|]; exact A25).
  assert (H27 : getr regs3 (Z_to_bv 5 27) = w64 (e_pp (x_e rsegs cx)))
  by (etransitivity; [exact (C2527 27%bv ltac:(cbv [In]; right; left; reflexivity))|]; exact A27).
  apply (HT fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  exact (ch_cut_T (fx := fx) B MT LAWS cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase
    HatL Hrole A24 Hcore3 CL H25 H27 K3).
Qed.
End k.

Print Assumptions rl_m02_key_tail.
