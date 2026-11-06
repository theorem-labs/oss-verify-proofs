(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* reac-pw/fuzz_role, image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes). Proves no function
   (kind: segment lemma): rl_m02_key_val, the value dispatch of the key piece, for lib/A/RPgM02Key.v.

   THE CODE: 0x82318 .. 0x82324 the shadow check of ent[v].type (decided by the shadow entry over
   [&ent[v], &ent[v] + 16)); 0x82328 lw a1 = ent[v].type; 0x82330 ld s9,0x28(s1); 0x82334 ld s11,0x80(s1);
   0x82338 beq a1,6 -> the Float arm 0x82398; 0x82340 bne a1,4 -> MAL 0x823fc; Int: 0x82344 .. 0x82354 the size's
   check, 0x82358 lw a1 = size, 0x82360 bltu a1,4 -> MAL; 0x82364 .. 0x82374 the body's check, 0x82378 lw a2 = the
   body's first word, 0x8237c j 0x823e0 (the value tail). No instruction of this range stores.
   THE PROOF: one entry state at 0x82318 (the real frame's cells R+0x28 / R+0x80 and the value entry's three words as
   regions, lib/A/RPgM02KeyBase.v's m2k_rgs / m2k_facts10 / m2k_SH) and runs to each branch; the engine decides each
   branch on the sign-extended word of the loaded field (m2k_U_sext32), and each exit takes the continuation its
   pc names: the Float arm (with the type fact), MAL through m2k_mal (Role.expect_value is (None, -1) for any other
   type and for a size below 4), or the value tail with v the sign-extended body word (Role.expect_value is
   Role.flag_rc of its signed value). m2i_exit rebuilds RPgSeg's cut facts at each exit from RPgM02Tail.ch_cut_T:
   every byte is as at the start, and the registers of ch_L and sp / gp / tp are kept.
   Section hypotheses: MTL : ameter_laws MT and LAWS : AR_laws rsegs B; nothing else is assumed. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02Tail RPgM02KeyBase RPgM02KeyV.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the value dispatch and the Int arm ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* a state reached by a run of this piece (no store: every byte as at the start, the registers of ch_L and sp / gp /
   tp kept, s9 / s11 = F / pp): RPgSeg's T cut's facts at it, from RPgM02Tail.ch_cut_T *)
Lemma m2i_exit : forall (cx : rs_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx) -> rs_role_at rsegs cx rec W2 mem2 ->
getr regs2 (Z_to_bv 5 24) = w64 (snd (rs_PA rsegs cx rec)) ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 -> cs_eq [2; 3; 4]%bv regs2 regs3 -> cs_eq ch_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 (e_F (x_e rsegs cx)) -> getr regs3 (Z_to_bv 5 27) = w64 (e_pp (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_T (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs3 mem3 md3.
Proof using MTL LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hpre Hbase HatL Hrole H24 HJ3 Hio C234 CL H25 H27 KE.
apply (ch_cut_T (fx := fx) B MT LAWS cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 Hpre Hbase
  HatL Hrole H24); [| exact CL | exact H25 | exact H27 | intros a Ha _; exact (KE a Ha)].
apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 (proj1 Hbase) HJ3
  (tl_r234 _ _ C234) eq_refl (Permutation_refl _) Hio (mo_le_refl MT MTL _)).
intros a Ha _ _. exact (KE a Ha).
Qed.

(* the facts of the T cut at the state of a run's last step: what every exit of this piece needs *)
Ltac m2i_exit_at regs2 pc :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _,
  Hpre : rs_pre _ _ ?cx, HCB : rs_chk_base _ _ _ _ ?fx2 ?rec ?lyq ?Sq ?Wq regs2 _ _,
  HatL : rs_at_cx _ _ _ _ regs2 (rs_L_chk _ _), HRA : rs_role_at _ _ _ _ _,
  A24 : getr regs2 (Z_to_bv 5 24) = _, D32 : sv_denot ?E (SOff 32 0) = _, D33 : sv_denot ?E (SOff 33 0) = _ |- _ =>
  let CL := fresh "CL" in let C234 := fresh "C234" in let G25 := fresh "G25" in let G27 := fresh "G27" in
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  m2k_rsv HS (25%bv : bv 5) G25; m2k_rsv HS (27%bv : bv 5) G27;
  let HT3 := fresh "HT3" in
  assert (HT3 : rs_cut_T (fx := fx) rsegs B MT cx fx2 rec lyq Sq Wq (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2i_exit cx fx2 rec _ _ _ regs2 _ _ (ms_regs ms) (ms_mem ms) mdT Hpre HCB HatL HRA A24 HJ);
    [ kio | exact C234 | exact CL
    | etransitivity; [exact G25|]; rewrite D32; apply Z_to_bv_bv_unsigned
    | etransitivity; [exact G27|]; rewrite D33; apply Z_to_bv_bv_unsigned
    | intros a Ha; exact (KE a Ha (fun x => x)) ]
  | ];
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with pc by (vm_compute; reflexivity)
end.

Lemma rl_m02_key_val : forall (cx : rs_scx rsegs) POST rec ent (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 (a0v : Z),
rs_pre rsegs B cx ->
@rs_from_MAL fx rc SK rsegs B MT cx POST ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (v : Z),
   @rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
   rs_role_at rsegs cx rec W3 mem3 ->
   rs_at_cx rsegs cx W3 mem3 regs3
     (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                            (LReg 27, e_pp (x_e rsegs cx))]) ->
   getr regs3 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
   (v < 2 -> snd (rs_PA rsegs cx rec) = 1 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = v) ->
   (2 <= v -> fst (rs_PA rsegs cx rec) = None /\ snd (rs_PA rsegs cx rec) = -1) ->
   SRr rsegs W3 (@cfg_at fx3 rsegs M2K_VAL regs3 mem3 md3) POST) ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
   Model.e_type ent = Model.POD_FLOAT ->
   @rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
   rs_role_at rsegs cx rec W3 mem3 ->
   rs_at_cx rsegs cx W3 mem3 regs3
     (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                            (LReg 25, e_F (x_e rsegs cx)); (LReg 27, e_pp (x_e rsegs cx))]) ->
   val_mem rsegs (mrestrict (w_H W3) mem3) (a0v + 4) 4 (Model.e_size ent) ->
   val_mem rsegs (mrestrict (w_H W3) mem3) (a0v + 8) 4 (Cursor.rd32 (Model.e_body ent)) ->
   range_addressable (aview rsegs (w_H W3) mem3) SHADOW_OFF a0v 16 ->
   SRr rsegs W3 (@cfg_at fx3 rsegs 0x82398 regs3 mem3 md3) POST) ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 ->
Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                         (LCell XR 0x28, e_F (x_e rsegs cx)); (LCell XR 0x80, e_pp (x_e rsegs cx))]) ->
Model.ent_wf ent ->
val_mem rsegs (mrestrict (w_H W2) mem2) a0v 4 (Model.e_type ent) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 (Model.e_size ent) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 (Cursor.rd32 (Model.e_body ent)) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
rs_E0 rec = Role.expect_value ent ->
snd (rs_PA rsegs cx rec) = snd (rs_E0 rec) -> fst (rs_PA rsegs cx rec) = fst (rs_E0 rec) ->
SRr rsegs W2 (@cfg_at fx2 rsegs M2K_KV regs2 mem2 md2) POST.
Proof.
intros cx POST rec ent fx2 ly2 S2 W2 regs2 mem2 md2 a0v
Hpre HMAL HTAIL HFLT HCB HRA Hppl HAT Hentwf Hvt Hvs Hvb Hra Ha0lo Ha0hi Happ HE0 Hsnd Hfst.
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2k_apart B LAWS cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & _ & _ & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil, Hwin.
pose proof HCB as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpodin & Hpodout).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Htr : 0 <= Model.e_type ent < 2 ^ 32) by (destruct Hentwf as (H & _); lia).
assert (Hsr : 0 <= Model.e_size ent <= 45) by (destruct Hentwf as (_ & _ & H); lia).
pose proof (m2k_rd32_range (Model.e_body ent)) as Hbr.
assert (HatL : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx))
by (unfold rs_at_cx, rs_at in HAT |- *; rewrite Forall_app in HAT; exact (proj1 HAT)).
unfold rs_at_cx, rs_at, rs_L_chk in HAT. cbn [app fst snd rl_at rl_xv] in HAT.
rewrite !Forall_cons_iff in HAT.
destruct HAT as (A8 & A9 & A19 & A23 & A18 & A22 & C08 & C30 & A24 & A10 & C28 & C80 & _).
cbn [rl_at rl_xv fst snd] in A24.
pose proof (fun (w : word) => word_range w) as Hwr.
set (extra := [w64 (e_F (x_e rsegs cx)); w64 (e_pp (x_e rsegs cx)); w64 (Model.e_type ent);
               w64 (Model.e_size ent); w64 (Cursor.rd32 (Model.e_body ent))] : list word).
pose (rgs := m2k_rgs (SOff 34 0) (SOff 35 0) (SOff 36 0)).
assert (Hrgs : rgs = m2k_rgs (SOff 34 0) (SOff 35 0) (SOff 36 0)) by reflexivity.
assert (E9 : bv_unsigned (ew (Ereg regs2 extra) 9) = e_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 extra 9 (9%bv : bv 5) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : bv_unsigned (ew (Ereg regs2 extra) 10) = a0v).
{ rewrite (ew_Ereg_nat regs2 extra 10 (10%bv : bv 5) eq_refl), A10. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : bv_unsigned (ew (Ereg regs2 extra) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 extra 23 (23%bv : bv 5) eq_refl), A23. unfold w64, SHADOW_OFF.
  apply unsigned_lit_small. lia. }
pose proof (den_extra (Ereg regs2 extra) regs2 extra 0 (w64 (e_F (x_e rsegs cx))) eq_refl eq_refl) as D32.
pose proof (den_extra (Ereg regs2 extra) regs2 extra 1 (w64 (e_pp (x_e rsegs cx))) eq_refl eq_refl) as D33.
pose proof (den_extra (Ereg regs2 extra) regs2 extra 2 (w64 (Model.e_type ent)) eq_refl eq_refl) as D34.
pose proof (den_extra (Ereg regs2 extra) regs2 extra 3 (w64 (Model.e_size ent)) eq_refl eq_refl) as D35.
pose proof (den_extra (Ereg regs2 extra) regs2 extra 4 (w64 (Cursor.rd32 (Model.e_body ent))) eq_refl eq_refl)
  as D36.
cbn [Nat.add] in D32, D33, D34, D35, D36.
assert (Hrs : Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W2) mem2)) rgs).
{ rewrite Hrgs. unfold m2k_rgs. apply Forall_cons.
  - apply (m2_frame_ok _ W2 mem2 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx) 0 0x138 0 0);
    [exact E9 | lia | lia | exact Hpres | intros Hc; lia |].
    apply Forall_cons;
    [eapply (chunk_ok_val rsegs _ _ _ 0x28 8 (SOff 32 0)); [exact D32 | cbn; apply Hwr | cbn; lia | exact C28]|].
    apply Forall_cons;
    [eapply (chunk_ok_val rsegs _ _ _ 0x80 8 (SOff 33 0)); [exact D33 | cbn; apply Hwr | cbn; lia | exact C80]|].
    apply Forall_nil.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rm_ro_region rsegs _ (w_H W2) mem2 10 a0v 0 16); [exact E10 | lia | lia |].
    apply Forall_cons;
    [eapply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 34 0));
     [exact D34 | unfold w64; cbn [Z.of_N Z.mul]; rewrite Z_to_bv_unsigned;
      change (bv_wrap 64 (Model.e_type ent)) with (Model.e_type ent mod 2 ^ 64);
      rewrite (Z.mod_small (Model.e_type ent) (2 ^ 64)) by lia; lia
     | cbn; lia
     | unfold w64; rewrite Z_to_bv_unsigned;
       change (bv_wrap 64 (Model.e_type ent)) with (Model.e_type ent mod 2 ^ 64);
       rewrite (Z.mod_small (Model.e_type ent) (2 ^ 64)) by lia; rewrite Z.add_0_r; exact Hvt]|].
    apply Forall_cons;
    [eapply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 35 0));
     [exact D35 | unfold w64; cbn [Z.of_N Z.mul]; rewrite Z_to_bv_unsigned;
      change (bv_wrap 64 (Model.e_size ent)) with (Model.e_size ent mod 2 ^ 64);
      rewrite (Z.mod_small (Model.e_size ent) (2 ^ 64)) by lia; lia
     | cbn; lia
     | unfold w64; rewrite Z_to_bv_unsigned;
       change (bv_wrap 64 (Model.e_size ent)) with (Model.e_size ent mod 2 ^ 64);
       rewrite (Z.mod_small (Model.e_size ent) (2 ^ 64)) by lia; exact Hvs]|].
    apply Forall_cons;
    [eapply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 36 0));
     [exact D36 | unfold w64; cbn [Z.of_N Z.mul]; rewrite Z_to_bv_unsigned;
      change (bv_wrap 64 (Cursor.rd32 (Model.e_body ent)))
        with (Cursor.rd32 (Model.e_body ent) mod 2 ^ 64);
      rewrite (Z.mod_small (Cursor.rd32 (Model.e_body ent)) (2 ^ 64)) by lia; lia
     | cbn; lia
     | unfold w64; rewrite Z_to_bv_unsigned;
       change (bv_wrap 64 (Cursor.rd32 (Model.e_body ent)))
         with (Cursor.rd32 (Model.e_body ent) mod 2 ^ 64);
       rewrite (Z.mod_small (Cursor.rd32 (Model.e_body ent)) (2 ^ 64)) by lia; exact Hvb]|].
    apply Forall_nil. }
assert (Hpd : pairwise_disjoint (Ereg regs2 extra) rgs).
{ rewrite Hrgs. unfold m2k_rgs, m2_frame, m2k_ent.
  repeat split; try exact I.
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E10. right. lia. }
assert (HG : facts_ok (Ereg regs2 extra) m2k_facts10)
  by (apply (m2k_facts10_ok _ (e_R (x_e rsegs cx)) a0v E9 ltac:(lia) HR16 E23 E10 ltac:(lia))).
pose proof (m2_entry (fx := fx2) M2K_KV [] rgs m2k_facts10 W2 regs2 extra mem2 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd HG) as HS.
remember (Ereg regs2 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH E (mrestrict (w_H W2) mem2)).
{ apply (m2k_sh_ok W2 mem2 E a0v);
  [ unfold M2_Bx; apply (m2k_U_atom E 23 SHADOW_OFF);
    [subst E; apply bv_eq; rewrite E23; symmetry; apply unsigned_lit_small; unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; lia]
  | apply (m2k_U_atom E 10 a0v);
    [subst E; apply bv_eq; rewrite E10; symmetry; apply unsigned_lit_small; lia | lia]
  | exact Hra | exact Happ ]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
unfold cfg_at. change (w64 M2K_KV) with (Z_to_bv 64 M2K_KV).
(* 0x82318 .. 0x82334, stop at 0x82338 `beq a1,a2` with a1 the type *)
m2_run m2_awr. ck_keep kwr_stk.
assert (E34 : ew E 34 = Z_to_bv 64 (Model.e_type ent))
by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (Model.e_size ent))
by (subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (Cursor.rd32 (Model.e_body ent)))
by (subst E; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
m2_branch Hb.
all: rewrite branch_eq_U, (m2k_U_sext32 E 34 (Model.e_type ent) E34 Htr), U_lit in Hb by lia.
- (* 0x82338 beq taken: the type is 6, the Float arm at 0x82398 *)
  assert (Ht6 : Model.e_type ent = Model.POD_FLOAT).
  { apply Z.eqb_eq in Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)) in Hb. exact Hb. }
  m2_run_to m2_awr 0x82398. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [10]%bv HS HAE ltac:(vm_compute; reflexivity)) as C10 end.
  m2i_exit_at regs2 0x82398.
  destruct HT3 as (Hb3 & Ha3 & Hr3).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  apply (HFLT fx2 ly2 S2 W2 r m d Ht6 Hb3 Hr3) end.
  + unfold rs_at_cx, rs_at in Ha3 |- *. rewrite Forall_app in Ha3 |- *. destruct Ha3 as (HL & HR).
    split; [exact HL|]. rewrite !Forall_cons_iff in HR. destruct HR as (X24 & X25 & X27 & _).
    apply Forall_cons; [exact X24|].
    apply Forall_cons; [|apply Forall_cons; [exact X25 | apply Forall_cons; [exact X27 | apply Forall_nil]]].
    cbn [rl_at fst snd]. etransitivity; [exact (C10 (10%bv : bv 5) ltac:(left; reflexivity))|]. exact A10.
  + eapply (val_mem_kept rsegs); [|exact Hvs]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
    apply KE; [lia | exact (fun x => x)].
  + eapply (val_mem_kept rsegs); [|exact Hvb]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
    apply KE; [lia | exact (fun x => x)].
  + eapply (rm_ra_kept rsegs); [exact Hra|]. intros x Hx.
    assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    apply KE; [unfold shadow_of_addr, SHADOW_OFF; lia | exact (fun z => z)].
- (* not taken: the type is not 6 *)
  assert (Ht6 : Model.e_type ent <> 6).
  { intros Hc. apply Z.eqb_neq in Hb. apply Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)). exact Hc. }
  m2_run m2_awr. ck_keep kwr_stk.
  m2_branch Hb2.
  all: rewrite branch_ne_U, (m2k_U_sext32 E 34 (Model.e_type ent) E34 Htr), U_lit in Hb2 by lia.
  + (* 0x82340 bne taken: the type is neither 4 nor 6, MAL *)
    assert (Ht4 : Model.e_type ent <> 4).
    { intros Hc. apply negb_true_iff in Hb2. apply Z.eqb_neq in Hb2. apply Hb2.
      apply (m2k_sx_eq _ 4 Htr ltac:(lia)). exact Hc. }
    m2_run_to m2_awr 0x823fc. ck_keep kwr_stk.
    m2i_exit_at regs2 0x823fc.
    destruct HT3 as (Hb3 & Ha3 & Hr3).
    assert (Hxv : Role.expect_value ent = (None, -1))
    by (apply (m2k_expect_none ent Hentwf); left; unfold POD_INT, POD_FLOAT; split; assumption).
    assert (Hm : snd (rs_PA rsegs cx rec) = -1) by (rewrite Hsnd, HE0, Hxv; reflexivity).
    assert (Hn : fst (rs_PA rsegs cx rec) = None) by (rewrite Hfst, HE0, Hxv; reflexivity).
    rewrite Hm in Ha3.
    exact (m2k_mal B MT cx POST rec fx2 _ _ _ _ _ _ HMAL Hb3 Hr3 Ha3 Hn Hm).
  + (* not taken: the type is 4, the Int arm *)
    assert (Ht4 : Model.e_type ent = 4).
    { apply negb_false_iff in Hb2. apply Z.eqb_eq in Hb2. apply (m2k_sx_eq _ 4 Htr ltac:(lia)) in Hb2. exact Hb2. }
    m2_run m2_awr. ck_keep kwr_stk.
    m2_branch Hb3.
    all: rewrite branch_ltu_U, (m2k_U_sext32 E 35 (Model.e_size ent) E35 ltac:(lia)), U_lit in Hb3 by lia.
    all: rewrite (m2k_sx_id (Model.e_size ent)) in Hb3 by lia.
    * (* 0x82360 bltu taken: the size is below 4, MAL *)
      apply Z.ltb_lt in Hb3.
      m2_run_to m2_awr 0x823fc. ck_keep kwr_stk.
      m2i_exit_at regs2 0x823fc.
      destruct HT3 as (Hb4 & Ha4 & Hr4).
      assert (Hxv : Role.expect_value ent = (None, -1)) by (apply (m2k_expect_none ent Hentwf); right; exact Hb3).
      assert (Hm : snd (rs_PA rsegs cx rec) = -1) by (rewrite Hsnd, HE0, Hxv; reflexivity).
      assert (Hn : fst (rs_PA rsegs cx rec) = None) by (rewrite Hfst, HE0, Hxv; reflexivity).
      rewrite Hm in Ha4.
      exact (m2k_mal B MT cx POST rec fx2 _ _ _ _ _ _ HMAL Hb4 Hr4 Ha4 Hn Hm).
    * (* not taken: the size is at least 4; the body word to the value tail at 0x823e0 *)
      apply Z.ltb_ge in Hb3.
      m2_run_to m2_awr 0x823e0. ck_keep kwr_stk.
      m2k_rsv HS (12%bv : bv 5) G12.
      m2i_exit_at regs2 0x823e0.
      destruct HT3 as (Hb4 & Ha4 & Hr4).
      assert (Hxv : Role.expect_value ent = Role.flag_rc (Accessors.s32 (Cursor.rd32 (Model.e_body ent))))
      by (apply (m2k_expect_int ent Hentwf); [unfold POD_INT; exact Ht4 | exact Hb3]).
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
      apply (HTAIL fx2 ly2 S2 W2 r m d (m2k_sx (Cursor.rd32 (Model.e_body ent))) Hb4 Hr4 Ha4) end.
      -- etransitivity; [exact G12|]. rewrite denot_lit_U, (m2k_U_sext32 E 36 _ E36 Hbr). reflexivity.
      -- exact (m2k_sx_range _ Hbr).
      -- intros Hlt.
         pose proof (proj1 (m2k_sx_small _ Hbr) Hlt) as H01.
         assert (Hs32 : Accessors.s32 (Cursor.rd32 (Model.e_body ent)) = Cursor.rd32 (Model.e_body ent)).
         { pose proof (m2k_s32_small _ Hbr) as ((_ & S0) & (_ & S1)).
           destruct H01 as [Z0|Z1]; [rewrite (S0 Z0), Z0 | rewrite (S1 Z1), Z1]; reflexivity. }
         rewrite Hs32 in Hxv.
         destruct (m2k_flag_small (Cursor.rd32 (Model.e_body ent)) ltac:(lia)) as (Hs1 & w & Hw & Hz).
         split; [rewrite Hsnd, HE0, Hxv; exact Hs1|].
         rewrite Hfst, HE0, Hxv, Hw. cbn [rs_rcell]. rewrite Hz. symmetry. apply m2k_sx_id. lia.
      -- intros Hge.
         assert (Hn01 : ~ (Cursor.rd32 (Model.e_body ent) = 0 \/ Cursor.rd32 (Model.e_body ent) = 1))
         by (intros Hc; apply (m2k_sx_small _ Hbr) in Hc; lia).
         assert (Hbig : Accessors.s32 (Cursor.rd32 (Model.e_body ent)) < 0 \/
           2 <= Accessors.s32 (Cursor.rd32 (Model.e_body ent))).
         { pose proof (m2k_s32_small _ Hbr) as ((S0 & _) & (S1 & _)).
           assert (Accessors.s32 (Cursor.rd32 (Model.e_body ent)) <> 0) by (intros Hc; apply Hn01; left; exact (S0 Hc)).
           assert (Accessors.s32 (Cursor.rd32 (Model.e_body ent)) <> 1) by (intros Hc; apply Hn01; right; exact (S1 Hc)).
           lia. }
         rewrite (m2k_flag_big _ Hbig) in Hxv.
         split; [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity].
Qed.

End c.

Print Assumptions rl_m02_key_val.
