(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition A_RAR_MAP : Z := 0x6ff80.
Definition A_MMAPFIXED : Z := 0x67ec0.      (* [comment removed for export] *)
Definition A_RAR_MAP_RET : Z := 0x6ffac.    (* [comment removed for export] *)
Definition MAPFIX_STACK : Z := 368.   (* [comment removed for export] *)
Definition MAPTOL_STACK : Z := 400.   (* [comment removed for export] *)

Definition maptol_frame (j1 j2 j3 j4 j5 j6 j7 : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C4 (Z_to_bv 64 50); CB 4 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 4 j6; CB 4 j7; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition maptol_pre_post (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32)
    (mv : word -> option byte) (A sz nm lo : Z) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x16 x28 x29 x30 x31 : word) (m1 : word -> option byte) (j1 j2 j3 j4 j5 j6 j7 : list byte),
    ms1 = MSsvc (mkR (wz 0x67df4) (wz (bv_unsigned sp - 96)) gp tp x5 x6 x7 (wz sz) (wz 1) (wz A) (wz sz) (wz 3) (wz 50) (wz (-1)) (wz 0) x16 (wz 222)
                     (wz A) (wz nm) (wz 0x139d20) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (wz 0x66034) (wz 222) fc None m1 (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)] mv m1 /\ wmono asegs mv m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp - 96)
    /\ rw_cells asegs m1 (bv_unsigned sp - 96) (maptol_frame j1 j2 j3 j4 j5 j6 j7 s4 s3 s2 s1 s0 ra).

Lemma map_tol_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mv : word -> option byte) (A sz nm lo : Z),
  mmap_consts mv -> mem_inv asegs mv -> stk asegs mv lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + MAPFIX_STACK <= bv_unsigned sp ->
  0 < sz -> sz mod 4096 = 0 -> sz + 4096 <= 2^63 -> A mod 4096 = 0 -> AIMG_HI <= A -> A + sz <= alloc_ceiling -> 0 <= nm < 2^64 ->
  evt asegs (maptol_pre_post ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc mv A sz nm lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz sz) (wz nm) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_MMAPFIXED) fc None mv (seg_rom asegs)).
Proof.
  intros until lo. intros HC MI ST CEIL LO SZ0 SZA SZB AAL AHI AHN NM.
  (nelimp HC 7%nat; intros GOTP PSC GOTC CF260 CF144 GOTS DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
  pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
  unfold A_MMAPFIXED, MAPFIX_STACK, AIMG_HI in *. leaf_prep. idtac.
  (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 7 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep; try if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  rewrite (land_align12 A) by lia. replace (A / 4096 * 4096) with A by (Z.div_mod_to_equations; lia).
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  pose proof GOTC as GOTC1. recell GOTC1 MU. pose proof CF260 as CF1. recell CF1 MU.
  call_sp getnamedfd_any_ok; [exact MI| lia| exact GOTC1| exact CF1| exact ST| idtac; lia| lia|].
  clear GOTC1 CF1. restk. fixMI.
  lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  step_ecall. cbv beta. unfold maptol_pre_post.
  nexists 9%nat. exists (firstn 4 (skipn 4 junk)). nexists 6%nat.
  split. { cbv delta [mkR wz]. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia; exact ST|].
  replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia. exact FR.
Qed.

(* [comment removed for export] *)
Definition maptol_node (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 x5 x6 x7 x16 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (A sz nm : Z) : machine_state :=
  MSsvc (mkR (wz 0x67df4) (wz (bv_unsigned sp - 96)) gp tp x5 x6 x7 (wz sz) (wz 1) (wz A) (wz sz) (wz 3) (wz 50) (wz (-1)) (wz 0) x16 (wz 222)
             (wz A) (wz nm) (wz 0x139d20) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x66034) (wz 222) fc None m1 (seg_rom asegs).

Definition maptol_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (W : list (Z * Z)) (lo : Z) (m1 : word -> option byte) (X : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms2 => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : word -> option byte),
    ms2 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs)
    /\ munch W m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp) /\ X m2.

(* [comment removed for export] *)
Lemma map_tol_ref : forall (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 x5 x6 x7 x16 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (A sz nm lo : Z) (j1 j2 j3 j4 j5 j6 j7 : list byte),
  mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp - 96) -> alloc_ceiling <= lo -> lo + MAPFIX_STACK <= bv_unsigned sp ->
  rw_cells asegs m1 (bv_unsigned sp - 96) (maptol_frame j1 j2 j3 j4 j5 j6 j7 s4 s3 s2 s1 s0 ra) ->
  evt asegs (maptol_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(lo, bv_unsigned sp)] lo m1 (fun _ => True))
      (nret (maptol_node ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 x5 x6 x7 x16 x28 x29 x30 x31 F fc m1 A sz nm) (efferr ENOMEM)).
Proof.
  intros until j7. intros MI ST CEIL LO FR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof aceil as CEILlo. unfold MAPFIX_STACK in LO.
  unfold maptol_node, maptol_frame in *. cbv delta [wz] in *.
  replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in * by lia.
  unfold efferr, eff0. sys_nret. unfold errno_ret, ENOMEM.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. lstep; try if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. do 6 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold maptol_ret_post. nexists 15%nat. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact I].
Qed.

(* [comment removed for export] *)
Lemma map_tol_grant : forall (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 x5 x6 x7 x16 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : word -> option byte) (A sz nm lo : Z) (j1 j2 j3 j4 j5 j6 j7 : list byte),
  mmap_consts m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp - 96) -> alloc_ceiling <= lo -> lo + MAPFIX_STACK <= bv_unsigned sp ->
  rw_cells asegs m1 (bv_unsigned sp - 96) (maptol_frame j1 j2 j3 j4 j5 j6 j7 s4 s3 s2 s1 s0 ra) ->
  0 < sz -> AIMG_HI <= A -> A + sz <= alloc_ceiling ->
  evt asegs (maptol_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A [(lo, bv_unsigned sp); (A, A + sz)] lo m1
               (fun m2 => rw_cells asegs m2 A [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))]))
      (nret (maptol_node ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 x5 x6 x7 x16 x28 x29 x30 x31 F fc m1 A sz nm)
            (mkEffect (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 sz)])).
Proof.
  intros until j7. intros HC MI ST CEIL LO FR SZ0 AHI AHN.
  (nelimp HC 7%nat; intros GOTP PSC GOTC CF260 CF144 GOTS DY). hide GOTC. hide CF144. clear GOTP PSC CF260 GOTS DY.
  pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + sz)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold MAPFIX_STACK in LO. unfold AIMG_HI in AHI.
  unfold maptol_node, maptol_frame in *. cbv delta [wz] in *.
  replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in * by lia.
  assert (ROF : forall y : word, (A <= bv_unsigned y < A + sz)%Z -> ro_addr asegs y = false).
  { intros y Hy. apply (ro_addr_noseg asegs). apply asegs_noseg_high. unfold AIMG_HI. lia. }
  sys_nret. fixMI.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
  replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
  replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  recell GOTC MU. lstep. lstep. fl. clear GOTC. (* [comment removed for export] *)
  recell CF144 MU. lstep. fl. clear CF144. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. do 6 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold maptol_ret_post. nexists 15%nat. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact ZNEW].
  Unshelve. all: try exact ROF.
Qed.

Section MAPFIX.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (A sz nm lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + MAPFIX_STACK <= bv_unsigned sp.
  Hypothesis SZ : 0 < sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis AAL : A mod 4096 = 0.
  Hypothesis AHI : AIMG_HI <= A.
  Hypothesis NM : 0 <= nm < 2^64.
  Hypothesis SITE : mmap_fixed_site mo A sz.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz sz) (wz nm) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_MMAPFIXED) fc None mv (seg_rom asegs).
  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs).

  Lemma AHN_fix : A + sz <= alloc_ceiling.
  Proof. (nelimp SITE 4%nat; intros S1 S2 S3 _). exact S3. Qed.

  (* [comment removed for export] *)
  Lemma mapfix_tol_spec : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop),
    sz <= R ->
    (* [comment removed for export] *)
    True ->
    (forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (A, A + sz)] mv m' -> wmono asegs mv m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' A [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (RET A x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') (mm_commit (Z_to_bv 64 A) (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P ENTRY mo (mkG G R).
  Proof.
    intros spin P HRsz _ KG. pose proof AHN_fix as AHN'.
    eapply lscps_evt_then.
    { eapply map_tol_pre; [exact HC| exact MI0| exact ST0| | | | | | exact AAL| exact AHI| exact AHN'| exact NM]; lia. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 22%nat; intros x5 x6 x7 x16 x28 x29 x30 x31 m1 j1 j2 j3 j4 j5 j6 j7 -> MU1 WM1 MI1 ST1 FR1).
    assert (HC1 : mmap_consts m1).
    { eapply mmap_consts_munch; [exact HC| exact MU1| ..]; cbn; pose proof (bv_unsigned_in_range 64 sp); idtac; lia. }
    eapply (lscps_mmap_fixed_rw_grant asegs) with (A := A) (len := sz); unfold mm_prot_rw, mm_flags_fixed; rewrite ?pru_id by lia.
    { unfold maptol_node. at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { exact SITE. } { exact HRsz. }
    { eapply lscps_evt_then. { eapply (map_tol_grant ra sp); [exact HC1| exact MI1| exact ST1| | | exact FR1| | exact AHI| exact AHN']; lia. }
      cbv beta. intros ms2 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 -> MU2 WM2 MI2 ST2 ZN).
      apply KG; [exact MI2| | eapply wmono_trans; [exact WM1| exact WM2]| exact ST2| exact ZN].
      eapply munch_trans; [| exact MU2]. eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn; intros; tauto. }
  Qed.

  (* [comment removed for export] *)
End MAPFIX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition map_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma map_enter : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mv : word -> option byte) (A sz nm lo : Z),
  mem_inv asegs mv -> stk asegs mv lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt asegs (fun ms1 => exists (m1 : word -> option byte),
      ms1 = MS (mkR (wz A_RAR_MAP_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz sz) (wz A) (wz A) (wz sz) (wz nm) (wz nm) a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_MMAPFIXED) fc None m1 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] mv m1 /\ wmono asegs mv m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) (map_frame s2 s1 s0 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz sz) (wz nm) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_RAR_MAP) fc None mv (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO.
  pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
  unfold A_RAR_MAP, A_RAR_MAP_RET, A_MMAPFIXED in *. leaf_prep. idtac.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold map_frame. cbv delta [wz].
  eexists. split. { cbv delta [mkR]. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma map_leave : forall (ra sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> 0 < A < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -32) (map_frame s2 s1 s0 ra) ->
  evt asegs (fun ms2 => ms2 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz A) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                F (ret_pc ra) fc None m (seg_rom asegs) /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (wz A_RAR_MAP_RET) (wz (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 (wz A) x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz A_RAR_MAP_RET) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO HA FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof aceil as CEILlo.
  unfold A_RAR_MAP_RET, map_frame in *. cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  do 4 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Section MAPTOL.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (A sz nm lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + MAPTOL_STACK <= bv_unsigned sp.
  Hypothesis SZ : 0 < sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis AAL : A mod 4096 = 0.
  Hypothesis AHI : AIMG_HI <= A.
  Hypothesis NM : 0 <= nm < 2^64.
  Hypothesis SITE : mmap_fixed_site mo A sz.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz sz) (wz nm) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_RAR_MAP) fc None mv (seg_rom asegs).
  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs).

  Lemma AHN : A + sz <= alloc_ceiling.
  Proof. (nelimp SITE 4%nat; intros S1 S2 S3 _). exact S3. Qed.

  (* [comment removed for export] *)
  Lemma map_tol_spec : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop),
    sz <= R ->
    (* [comment removed for export] *)
    True ->
    (forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (A, A + sz)] mv m' -> wmono asegs mv m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' A [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (RET A x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') (mm_commit (Z_to_bv 64 A) (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P ENTRY mo (mkG G R).
  Proof.
    intros spin P HRsz _ KG. pose proof AHN as AHN'. pose proof aceil as CEILlo.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LO as [CEIL LO']. unfold MAPTOL_STACK in LO'. pose proof AHI as AHI'. unfold AIMG_HI in AHI'.
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (unfold wz; apply unsigned_lit; lia).
    eapply lscps_evt_then.
    { eapply (map_enter ra sp) with (lo := lo); [exact MI0| exact ST0| exact CEIL| lia]. }
    cbv beta. intros ms1 [m1 (-> & MU1 & WM1 & MI1 & ST1 & FR1)].
    assert (HC1 : mmap_consts m1).
    { eapply mmap_consts_munch; [exact HC| exact MU1| ..]; cbn; lia. }
    eapply (mapfix_tol_spec (wz A_RAR_MAP_RET) (wz (bv_unsigned sp + -32))) with (lo := lo) (spin := spin);
      [exact HC1| exact MI1| rewrite E32; exact ST1| rewrite E32; split; [exact CEIL| unfold MAPFIX_STACK; lia]
      | exact SZ| exact AAL| unfold AIMG_HI; lia| exact NM| exact SITE| exact HRsz| exact I|].
    intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 ZN. rewrite E32 in MU2, ST2.
    pose proof FR1 as FR2. eapply (rw_cells_transport asegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia].
    replace (ret_pc (wz A_RAR_MAP_RET)) with (wz A_RAR_MAP_RET) by (unfold wz, A_RAR_MAP_RET; symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_evt_then.
    { eapply (map_leave ra sp) with (lo := lo) (A := A); [exact MI2| exact ST2| exact CEIL| lia| lia| exact FR2]. }
    cbv beta. intros ms3 [-> ST3].
    apply KG; [exact MI2| | eapply wmono_trans; [exact WM1| exact WM2]| exact ST3| exact ZN].
    eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn in Hx |- *; lia| eapply munch_weaken; [| exact MU2]; intros x Hx; cbn in Hx |- *; lia].
  Qed.

  (* [comment removed for export] *)
End MAPTOL.



End CeilWrap.
