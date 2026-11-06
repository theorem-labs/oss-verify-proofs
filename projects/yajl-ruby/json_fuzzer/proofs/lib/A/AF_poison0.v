(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow NodesA_mm BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed X_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanRepFrame AsanFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base AF_place AF_lkit AF_kit AF_unwind AF_poison AF_premap1 AF_premap2 AM_memset AF_mmfix0
  A_policy5 A_bundle A_benv5 A_mmchk5 A_balloc5 A_bpolicy5 A_bevents5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import CompatE2 LiaA NodesA_mmW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition p0_statics (m : mem) (cnr : word) : Prop := poison_globals m /\ statics m /\ rsmr_statics m cnr.
Definition p0_static_addr (x : Z) : Prop :=
  (0xa4000 <= x < 0xaa500) \/ (0xaa800 <= x < 0x13fdd0) \/ (0x600b50 <= x < 0x600b58) \/ (0x600dd0 <= x < 0x600dd8).
Lemma p0_statics_agree : forall m m' cn,
  p0_statics m cn -> (forall x, p0_static_addr x -> m' (wa x) = m (wa x)) -> p0_statics m' cn.
Proof. aceil.
  intros m m' cn (PG & ST & RS) AG. unfold p0_static_addr in AG.
  unfold p0_statics, poison_globals, statics, rsmr_statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in *.
  unfold kShadowBase, kHighMemEnd, kClearShadowMmapThreshold in *.
  destruct PG as (?&?&?&?&?&?&?). destruct ST as (?&?&?&?&?&?&?). destruct RS as (?&?&?&?&?).
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with H : rw_cells asegs ?m0 ?A ?cs |- rw_cells asegs ?m1 ?A ?cs =>
      eapply (rw_cells_agree asegs m0 m1); [| exact H]; cbn; intros x Hx; apply AG; clear -CEILB Hx; lia end.
Qed.


(* [comment removed for export] *)
Lemma is_err_small : forall z, 0 <= z < 2^47 -> is_err (Z_to_bv 64 z) = false.
Proof. intros z Hz. unfold is_err. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). apply Z.ltb_ge. lia. Qed.

Lemma rw_cells_CB_merge3 : forall m X n1 n2 n3 (l1 l2 l3 : list byte),
  rw_cells asegs m X [CB n1 l1] -> rw_cells asegs m (X + Z.of_nat n1) [CB n2 l2] -> rw_cells asegs m (X + Z.of_nat n1 + Z.of_nat n2) [CB n3 l3] ->
  rw_cells asegs m X [CB (n1 + n2 + n3)%nat (l1 ++ l2 ++ l3)].
Proof.
  intros m X n1 n2 n3 l1 l2 l3 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)] [[W3 B3] (Ua & Ub & Ur)].
  cbn in W1, W2, W3. destruct W1 as [L1 _], W2 as [L2 _], W3 as [L3 _].
  cbn [cells_bytes cbytes] in B1, B2, B3. rewrite app_nil_r in B1, B2, B3.
  cbn [cells_size csize Nat.add] in Wr, Vr, Ur, Wb, Vb, Ub. rewrite Nat.add_0_r in Wr, Vr, Ur, Wb, Vb, Ub.
  split; [split|].
  - cbn. split; [| exact I]. rewrite !length_app. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|]. rewrite L1.
    apply bytes_at_app. split; [exact B2|]. rewrite L2. exact B3.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact Wa|]. split; [lia|].
    intros k Hk. destruct (Z_lt_le_dec k (Z.of_nat n1)); [apply Wr; lia|].
    destruct (Z_lt_le_dec k (Z.of_nat n1 + Z.of_nat n2)).
    + replace (X + k) with (X + Z.of_nat n1 + (k - Z.of_nat n1)) by lia. apply Vr. lia.
    + replace (X + k) with (X + Z.of_nat n1 + Z.of_nat n2 + (k - Z.of_nat n1 - Z.of_nat n2)) by lia. apply Ur. lia.
Qed.

Definition p0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (mo : Model) (SH len : Z) (cnr : word) (R R' : Z) (s : aps) (E0 : aenv) (FSB0 : Z) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z)
    : machine_state -> Model -> Prop :=
  fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m'
    /\ munch [(bv_unsigned sp - 592, bv_unsigned sp); (SH, SH + len)] m m'
    /\ rw_cells asegs m' SH [CB (Z.to_nat len) (repeat (Z_to_bv 8 0) (Z.to_nat len))]
    /\ p0_statics m' cnr
    /\ ATOK E0 FSB0 HR0 L0 RES0 EB0 R R' s mo' /\ AKern E0 (aps_alloc s) mo'
    /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo.

Section P0.
(* [comment removed for export] *)
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0.
Hypothesis HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0.
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).

(* [comment removed for export] *)
Variables (s : aps) (Pq : list Z) (Dq : list batch).
#[local] Notation a := (aps_alloc s).
Hypothesis WF : AWf E0 Pq Dq a.

(* [comment removed for export] *)
Theorem poison0_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (usp lo R R' A L : Z) (cnr : word) (shj : list byte) (K : TSet),
  K [] ->
  ATOKc R R' s mo -> AKern E0 a mo ->
  usp mod 16 = 0 -> stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 592 -> usp <= 2^47 -> mem_inv asegs m ->
  p0_statics m cnr ->
  A mod 8 = 0 -> L mod 8 = 0 -> 0 <= L -> 0x603000 <= A -> A + L <= alloc_ceiling ->
  (A + L <= 0x7fff7000 \/ (kHighMemBeg <= A /\ (kHighMemBeg + 8 <= A \/ 8 <= L))) ->     (* [comment removed for export] *)
  (forall moX, AKern E0 a moX -> forall x n, kShadowBase + A / 8 <= x -> x + Z.of_nat n <= kShadowBase + A / 8 + L / 8 ->
      acc_ok (m_vm_lazy moX) (aSc s) (Z_to_bv 64 x, n)) ->
  rw_cells asegs m (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) shj] ->
  (forall ms' mo', p0_post ra (wz usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m mo (kShadowBase + A / 8) (L / 8) cnr R R' s E0 FSB0 HR0 L0 RES0 EB0 ms' mo' ->
     realizes_cfg acfg asegs (mkCfg ms' mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz A) (wz L) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz 0x55284) fc None m (seg_rom asegs)) mo) K.
Proof using All. (* [comment removed for export] *)
  aceil.
  intros until K. intros HK TOK AK U16 SK LOC LO SPH MI STA AM8 LM8 L0p AI ALC APL PSH SHJ CONT.
  pose proof LOC as LOC0. pose proof alloc_ceiling_range as CR. pose proof APL as APLk. rewrite kHighMemBeg_val in APL.
  assert (HA8 : A = 8 * (A / 8)) by (clear -CEILB AM8; Z.div_mod_to_equations; lia).
  assert (HL8 : L = 8 * (L / 8)) by (clear -CEILB LM8; Z.div_mod_to_equations; lia).
  assert (KSB : kShadowBase = 2147450880) by reflexivity.
  set (SH := kShadowBase + A / 8) in *.
  assert (HSH : SH = 2147450880 + A / 8) by (subst SH; rewrite KSB; reflexivity). clearbody SH.
  assert (USP : bv_unsigned (wz usp) = usp).
  { apply Z_to_bv_small. change (bv_modulus 64) with (2^64). pose proof (stk_lo_nonneg _ _ _ _ SK). clear -CEILB H LOC LO SPH. lia. }
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK).
  pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK) as KIA0.
  pose proof STA as (PG & ST & RS).
  Ltac sdj := cbn; repeat split; try exact I.
  (* [comment removed for export] *)
  assert (PolS : forall moX, AKern E0 a moX -> forall x n, lo <= x -> x + Z.of_nat n <= usp -> acc_ok (m_vm_lazy moX) (aSc s) (Z_to_bv 64 x, n)).
  { intros moX AKX x n H1 H2. apply (pol_stack E0 FSB0 HR0 s moX Pq Dq AKX WF ENV0); clear -CEILB CR H1 H2 LOC SPH; lia. }
  assert (PolI : forall moX, AKern E0 a moX -> forall x n, 0x10000 <= x -> x + Z.of_nat n <= 0x603000 -> acc_ok (m_vm_lazy moX) (aSc s) (Z_to_bv 64 x, n)).
  { intros moX AKX x n H1 H2. apply (pol_img E0 FSB0 HR0 s moX Pq Dq AKX WF ENV ENV0); clear -CEILB H1 H2; lia. }
  destruct (Z.lt_ge_cases (L / 8) kClearShadowMmapThreshold) as [SMALL|BIGM].
  - (* [comment removed for export] *)
    set (P2 := fun x : acc => acc_ok (m_vm_lazy mo) (aSc s) x).
    assert (PSTK2 : forall x n, lo <= x -> x + Z.of_nat n <= usp -> P2 (Z_to_bv 64 x, n)) by (intros; unfold P2; apply (PolS mo AK); assumption).
    assert (PDAT2 : forall x n, 0xa4000 <= x -> x + Z.of_nat n <= 0x603000 -> P2 (Z_to_bv 64 x, n)) by (intros; unfold P2; apply (PolI mo AK); lia).
    assert (PSH2 : forall x n, SH <= x -> x + Z.of_nat n <= SH + L / 8 -> P2 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P2. apply (PSH mo AK); clear -CEILB H1 H2 HSH KSB; lia. }
    eapply (srzA_evt asegs (aSc s) (aNc s) (aEBc s) (m_vm_lazy mo)).
    + rewrite HSH in SHJ.
      eapply (poison_walk P2); rewrite ?USP;
        [ exact SK | exact LOC0 | clear -CEILB LO; lia | exact SPH | exact MI | exact PG | exact AM8 | exact LM8 | exact L0p
        | exact AI | exact ALC | exact APLk | clear; lia | right; exact SMALL
        | unfold kShadowBase; exact SHJ | exact PSTK2 | exact PDAT2 | unfold kShadowBase; rewrite <- HSH; exact PSH2 ].
    + exact (proj2 (proj2 KIA0)).
    + exact (proj1 KIA0).
    + reflexivity.
    + intros ms3 mo3 HQ3 AG3 HLI3 Hh3.
      destruct HQ3 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & SK3 & ZSH & PG3).
      rewrite USP in MU3, SK3. unfold kShadowBase in MU3, ZSH. rewrite <- HSH in MU3, ZSH.
      assert (KIA3 : KIA (aSc s) (aNc s) (aEBc s) mo3) by (split; [exact HLI3| split; [eapply minvA_magree; [exact AG3| exact (proj1 (proj2 KIA0))]| exact Hh3]]).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG3 KIA3) as TOK3.
      pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
      pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK) as AK3.
      apply CONT. unfold p0_post. rewrite USP. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact SK3|]. split; [exact WM3|].
      split. { eapply munch_weaken; [| exact MU3]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      split. { replace (Z_to_bv 8 0) with (Z_to_bv 8 (0 mod 256)) by reflexivity. exact ZSH. }
      split. { apply (p0_statics_agree m m3 cnr STA). intros x Hx. unfold p0_static_addr in Hx. apply MU3.
               rewrite wa_unsigned by (clear -CEILB Hx; lia). clear -CEILB CR Hx LOC LO AI HSH. sdj; lia. }
      split; [exact TOK3|]. split; [exact AK3|]. rewrite Ffs3, Ffds3, Ftid3. repeat split; reflexivity.
  - (* [comment removed for export] *)
    exfalso. unfold kClearShadowMmapThreshold in BIGM. clear -CEILB CR BIGM AI ALC L0p HL8. lia.
Qed.
End P0.
End RC__1.
