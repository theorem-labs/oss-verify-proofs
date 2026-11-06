(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells Step.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_free_kit BF_poison BF_popdefs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cstep := stepA; try first [if_true | if_false].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
(* [comment removed for export] *)
Ltac sub_fp_fast :=
  let xq := fresh "xq" in let Hq := fresh "Hq" in
  intros xq Hq; cbn [outside] in Hq |- *; decompose [and] Hq; clear Hq;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end.
Ltac munch_fold mc m' MUc :=
  match goal with H : munch ?W ?ma mc |- _ =>
    let H2 := fresh in
    assert (H2 : munch W ma m') by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc]; sub_fp_fast]);
    clear H; rename H2 into H end.
Ltac after_callF mc m' MUc WMc := munch_fold mc m' MUc; after_call mc m' MUc WMc.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_EFA : Z := 0x358c8.
Definition A_EFA_MMRET : Z := 0x35968.    (* [comment removed for export] *)
Definition A_EFA_NAME : Z := 0x18a20.     (* [comment removed for export] *)

Section EFA.
Variable P : acc -> Prop.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo : Z) (SB c RI : Z).
Notation INST := 0xaaf58.
Notation RIc := (BF_popdefs.RIc c RI).
Notation RB := (SB + c * 4294967296).                 (* [comment removed for export] *)
Notation FA := (SB + c * 4294967296 + 3758096384).    (* [comment removed for export] *)

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition efa_frame_gen (m : mem) (sp : Z) (j : list byte) (ra s0 s1 s2 s3 : word) : Prop :=
  rw_cells bsegs m (sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma efa_pre_gen : forall mx (ra : word) (sp : Z) (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (tf nf mfa au mu na nfr mtx : Z) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo sp -> lo <= sp - 48 -> sp <= 2^47 -> sp mod 16 = 0 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  rw_cells bsegs mx 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs mx RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= tf -> 4 * tf <= mfa + 262144 -> 0 <= mfa -> mfa mod 262144 = 0 -> mfa <= 2^29 ->
  (mfa < 4 * tf -> mfa + 262144 <= 2^29) ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall m', 4 * tf <= mfa ->
     mem_inv bsegs m' -> stk bsegs m' lo sp -> munch [(sp + -48, sp)] mx m' -> wmono bsegs mx m' ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 RIc) (Z_to_bv 64 RB) (Z_to_bv 64 1) (Z_to_bv 64 mfa) (Z_to_bv 64 (4 * tf)) a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall m' j, mfa < 4 * tf ->
     mem_inv bsegs m' -> stk bsegs m' lo (sp + -48) -> munch [(sp + -48, sp)] mx m' -> wmono bsegs mx m' ->
     efa_frame_gen m' sp j ra s0 s1 s2 s3 ->
     evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_EFA_MMRET) (Z_to_bv 64 (sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (mfa + 262144)) (Z_to_bv 64 (FA + mfa))
                             (Z_to_bv 64 INST) (Z_to_bv 64 (FA + mfa)) (Z_to_bv 64 262144) (Z_to_bv 64 A_EFA_NAME) (Z_to_bv 64 mfa) (Z_to_bv 64 3758096384) a6 a7
                             (Z_to_bv 64 262144) (Z_to_bv 64 RIc) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x6f978) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 RIc) (Z_to_bv 64 RB) (Z_to_bv 64 tf) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_EFA) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK LO SPH SPA PSTK INS RIC TF0 TF1 MF0 MFM MFS MFRc KNO KGR.
  assert (MFR : mfa + 262144 <= 2^29 + 262144) by (clear -MFS; lia).
  unfold A_EFA, A_EFA_MMRET, A_EFA_NAME, efa_frame_gen, ri_cells in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(sp + -48, sp)] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  carve_frame 48%nat SK.
  do 6 cstep.                     (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  replace (tf ≪ 2) with (4 * tf) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  rewrite ?(Z.mod_small (4 * tf)) by (clear -CEILB TF0 TF1 MFR; lia).
  zstepA; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -CEILB TF0 TF1 MF0 MFR; lia).
  - (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    do 6 cstep.                   (* [comment removed for export] *)
    release_frame FR SK sp.
    cstep.                        (* [comment removed for export] *)
    eapply KNO; [clear -CEILB K0; lia| exact MI| exact SK| exact MU| exact WM].
  - (* [comment removed for export] *)
    do 3 zstepA.                  (* [comment removed for export] *)
    do 2 zstepA.                  (* [comment removed for export] *)
    rewrite land_roundup18 by (clear -CEILB TF0 TF1 MFR; lia).
    rewrite (roundup18_next mfa (4 * tf)) by (clear -CEILB K0 TF1 MF0 MFM; lia).
    do 2 zstepA.                  (* [comment removed for export] *)
    specialize (MFRc ltac:(clear -CEILB K0; lia)).
    zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB MFRc MF0; intros K1; lia|].  (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    do 4 zstepA.                  (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    do 2 zstepA.                  (* [comment removed for export] *)
    replace (mfa + 262144 - mfa) with 262144 by (clear; lia).
    do 4 zstepA.                  (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (mfa + (SB + c * 4294967296 + 3758096384)) with (SB + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
    subst RIv.
    eapply KGR; [clear -CEILB K0; lia| exact MI| exact SK| exact MU| exact WM| eexact FR].
Qed.

(* [comment removed for export] *)
Lemma efa_grow_ok_gen : forall mx (ra : word) (sp : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (nf mfa au mu na nfr mtx : Z) (j shj : list byte) (TSD CTX T nmaps nmapped : Z) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo (sp + -48) -> lo <= sp - 112 -> sp <= 2^47 -> sp mod 16 = 0 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  efa_frame_gen mx sp j ra s0 s1 s2 s3 ->
  rw_cells bsegs mx RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= mfa -> mfa mod 262144 = 0 -> mfa + 262144 <= 2^29 ->
  poison_globals mx ->
  rw_cells bsegs mx (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) shj] ->
  (forall a k, kShadowBase + (FA + mfa) / 8 <= a -> a + Z.of_nat k <= kShadowBase + (FA + mfa) / 8 + 32768 -> P (Z_to_bv 64 a, k)) ->
  thread_cells mx tp TSD CTX T -> 0xa5000 <= TSD -> TSD + 8 <= 0x603000 ->
  placed CTX 4096 -> placed_s T 4096 ->      (* [comment removed for export] *)
  0xa5000 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 160 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  rw_cells bsegs mx (T + 2872) [C8 (Z_to_bv 64 nmaps); C8 (Z_to_bv 64 nmapped)] -> 0 <= nmaps -> 0 <= nmapped ->
  (forall m' (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv bsegs m' -> stk bsegs m' lo sp ->
     munch [(sp - 112, sp); (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888); (RIc + 24, RIc + 32)] mx m' ->
     wmono bsegs mx m' ->
     rw_cells bsegs m' RIc (ri_cells mtx nf (mfa + 262144) au mu na nfr) ->
     poison_globals m' ->
     rw_cells bsegs m' (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] ->
     thread_cells m' tp TSD CTX T ->
     rw_cells bsegs m' (T + 2872) [C8 (Z_to_bv 64 (nmaps + 1)); C8 (Z_to_bv 64 (nmapped + 262144))] ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_EFA_MMRET) (Z_to_bv 64 (sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (mfa + 262144)) (Z_to_bv 64 (FA + mfa))
                          (Z_to_bv 64 (FA + mfa)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 262144) (Z_to_bv 64 RIc) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_EFA_MMRET) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK LO SPH SPA PSTK FR RIC MF0 MFM MFR PG SHJ PSH TC HT1 HT2 HCP HTPL HTP HTC HTSB HCSB PCTX PT TST HNM HNMD CONT.
  unfold ri_cells in RIC, CONT. unfold A_EFA_MMRET, efa_frame_gen in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HRI0, HTSB, HCSB. pose proof HC as HC0. unfold kLargestClassID in HC. pose proof HSBH as HSBH0. rewrite kHighMemBeg_val in HSBH0.
  pose proof HCP as HCP0. plopen HCP. rename HCPi into HC1. rename HCPc into HC2. rename HCPs into HC3.
  pose proof HTPL as HTPL0. plopen HTPL. rename HTPLi into HT0. rename HTPLc into HT4. rename HTPLg into HT3. rename HTPLs into HT5.
  assert (MU : munch [(sp - 112, sp); (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888); (RIc + 24, RIc + 32)] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  unfold kShadowBase in *.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  set (A := SB + c * 4294967296 + 3758096384 + mfa) in *. assert (HA : A = SB + c * 4294967296 + 3758096384 + mfa) by reflexivity. clearbody A.
  assert (A8 : A mod 8 = 0) by (rewrite HA; clear -CEILB HSB MFM; Z.div_mod_to_equations; lia).
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HA HSB HC MF0; intros K0; lia|].   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; clear -CEILB K1; lia|].     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply evtA_cut;
    [ eapply (poison_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A 262144 250 shj);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
      | exact A8| reflexivity| clear; lia| clear -CEILB HA HSB HSBH0 HC MF0 MFR; lia| clear -CEILB HA HSB HC MF0 MFR; lia| right; rewrite kHighMemBeg_val; clear -CEILB HA HSB HSBH0 HC MF0 MFR; lia| clear; lia| left; clear; lia
      | change (262144 / 8) with 32768; exact SHJ
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT
      | change (262144 / 8) with 32768; unfold kShadowBase; exact PSH ]
    |].
  clear G1 G2 G3 G4 G5 G6 G7 SHJ.
  cbv beta. intros ms' POST. unfold poison_post in POST. destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MI' & SK' & SH' & PG').
  unfold kShadowBase in MUc, SH'. rewrite !unsigned_lit in MUc, SK' by lia. change (262144 / 8) with 32768 in MUc, SH'.
  clear MI SK. lazymatch type of MUc with munch _ ?mc _ => after_callF mc m' MUc WMc end. ret_pc_lit.
  rename MI' into MI. rename SK' into SK.
  destruct PG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  eapply evtA_cut;
    [ eapply (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| clear -CEILB HT1; lia| exact HT2| clear -CEILB HC1; lia| exact HC2| clear -CEILB HT0 HT4; lia| clear -CEILB HTP; lia
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PCTX ]
    |].
  cbv beta. intros ms2 POST. unfold gcts_post in POST. destruct POST as (a1x & m2 & -> & MU2 & WM2 & MI2 & SK2).
  rewrite !unsigned_lit in MU2, SK2 by lia.
  clear MI SK. lazymatch type of MU2 with munch _ ?mc _ => after_callF mc m2 MU2 WM2 end. ret_pc_lit.
  rename MI2 into MI. rename SK2 into SK.
  clear HSBH HRI PSH HC3 HNM HNMD K0 K1 MFM.   (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  cstep. cstep.                   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 6 cstep.                     (* [comment removed for export] *)
  release_frame FR SK sp.
  cstep.                          (* [comment removed for export] *)
  subst RIv A.
  eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact RIC| exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
               | exact SH'| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact TST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End EFA.
End RC__1.
