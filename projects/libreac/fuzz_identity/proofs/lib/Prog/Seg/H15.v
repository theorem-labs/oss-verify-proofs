From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H15.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma s_out_img : forall m, Mem.mem_inv rsegs m -> bytes_at rsegs m OUT_PAREN (s_out ++ [z8]).
Proof.
  intros m H. apply (ro_bytes_at rsegs m); [exact H | unfold OUT_PAREN; lia | cbn; unfold OUT_PAREN; lia |].
  apply ro_chk_sound. vm_compute. reflexivity.
Qed.

Lemma s_out_nth : forall k, (k < 5)%nat ->
  nth k (s_out ++ [z8]) (Z_to_bv 8 0) = RcIdentModel.nthb s_out k.
Proof. intros k Hk. do 5 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma s_out_len : length s_out = 5%nat.
Proof. reflexivity. Qed.

Lemma step15 : forall t, 0 <= t <= 4 ->
  Hcut B APIf ra (Inv_K13aac B APIf ra empty) ->
  Hcut B APIf ra (fun g c => Inv_K13a94_at B APIf ra empty g (t + 1) c) ->
  Hcut B APIf ra (fun g c => Inv_K13a94_at B APIf ra empty g t c).
Proof.
  intros t Ht Hac HX g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact HX | exact Hac | | | exact HC | ].
  { intros c' HC'. cbv beta. unfold Inv_K13a94_at. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K13aac. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HBB & _ & HDP & E8 & E13 & E27 & E10 & E12 & E11).
  pose proof HBB as (HNC & E9 & E18 & HLD).
  pose proof HNC as ((HID & HW & _ & _ & _ & _ & _ & _ & _ & HOU) & _).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HDP) as HDPn. unfold spk, fsp, SLOT_FRAME in HDPn.
  set (bs := dp2 (g_in g) ++ firstn (Z.to_nat t) s_out) in HDPn.
  assert (Lbs : Z.of_nat (length bs) = ld2 (g_in g) + t).
  { unfold bs. rewrite length_app, length_firstn, s_out_len. unfold ld2, zlen. lia. }
  set (a := g_S g - 368 + 48 + ld2 (g_in g) + t).
  assert (Ea : a = g_S g - 368 + 48 + Z.of_nat (length bs)) by (unfold a; lia).
  unfold rmk, Frame.mkR. rewrite E2, E8, E13, E10', E12, E11.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  change (RcIdentModel.bz (RcIdentModel.nthb s_out (Z.to_nat t)))
    with (bv_unsigned (RcIdentModel.nthb s_out (Z.to_nat t))).
  rewrite le1_byte.
  pose proof (Mem.mem_inv_store rsegs (normalize rsegs mem) (wa a) [RcIdentModel.nthb s_out (Z.to_nat t)] HMI0 HSO)
    as HMI1.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a
    [RcIdentModel.nthb s_out (Z.to_nat t)] (Frame.munch_refl _ _) ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a
    [RcIdentModel.nthb s_out (Z.to_nat t)] (Frame.munch_refl _ _) ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a)
    [RcIdentModel.nthb s_out (Z.to_nat t)] (Frame.wmono_refl _ _)) as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a
    [RcIdentModel.nthb s_out (Z.to_nat t)] HSTK0 ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 368 + 48) bs (RcIdentModel.nthb s_out (Z.to_nat t))
    HDPn ltac:(lia)) as HDP1.
  rewrite <- Ea in HDP1.
  change (Z_to_bv 64 a) with (wa a).
  remember (write_to_mem (normalize rsegs mem) (wa a) [RcIdentModel.nthb s_out (Z.to_nat t)]) as m1 eqn:Em1.
  pose proof (bytes_at_one m1 OUT_PAREN _ (Z.to_nat (t + 1)) (s_out_img m1 HMI1)
    ltac:(rewrite length_app, s_out_len; cbn [length]; lia)) as HB1.
  rewrite Z2Nat.id in HB1 by lia. pose proof (rd1 _ _ _ HB1) as RD1.
  replace (OUT_PAREN + (t + 1)) with (OUT_PAREN + 1 + t) in RD1 by lia.
  step. step. step. step. step.
  rewrite bv_eqb_small by lia.
  assert (KMm : forall m', mem_rel rsegs m' m1 -> KM [(a, a + 1)] mem m').
  { intros m' HREL. exact (KM_of _ mem m1 m' HRO MU1 HREL). }
  assert (HOk : forall m', mem_rel rsegs m' m1 -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU). }
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 32) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (spk g 226) (n_ln (g_in g) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D5 : disjoint_from [(a, a + 1)] (spk g 168) (Z.of_nat (length (le8 (Z_to_bv 64 (ld2 (g_in g)))))))
    by (rewrite length_le8; cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) as [T5|T5] end; cbn [negb].
  - assert (Et : t = 4) by lia. subst t.
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + unfold HBb. split; [|split; [|split]].
      * apply (NC_keep g nm tk dp regs mem R' m' _ HNC (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4);
          rewrite HG; reflexivity.
      * rewrite HG. exact E9.
      * rewrite HG. exact E18.
      * exact (KMm m' HREL _ _ D5 HLD).
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME. rewrite EXPDP_eq.
      change (Z.to_nat 4) with 4%nat in HDP1. unfold bs in HDP1. rewrite <- app_assoc in HDP1. exact HDP1.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. exact E27.
    + rewrite HG. greg2. f_equal; unfold spk, fsp, SLOT_FRAME; lia.
  - apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + unfold HBb. split; [|split; [|split]].
      * apply (NC_keep g nm tk dp regs mem R' m' _ HNC (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4);
          rewrite HG; reflexivity.
      * rewrite HG. exact E9.
      * rewrite HG. exact E18.
      * exact (KMm m' HREL _ _ D5 HLD).
    + lia.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
      rewrite (firstn_snoc s_out (Z.to_nat t) (RcIdentModel.zb 0)) by (rewrite s_out_len; lia).
      rewrite app_assoc. exact HDP1.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. reflexivity.
    + rewrite HG. exact E27.
    + rewrite HG. greg2. f_equal; unfold spk, fsp, SLOT_FRAME; lia.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. rewrite s_out_nth by lia. reflexivity.
Qed.

Lemma seg_H15 : Hcut B APIf ra (Inv_K13aac B APIf ra empty) -> Hcut B APIf ra (Inv_K13a94 B APIf ra empty).
Proof.
  intros Hac.
  assert (IND : forall n : nat, Hcut B APIf ra (fun g c => Inv_K13a94_at B APIf ra empty g (5 - Z.of_nat n) c)).
  { induction n as [|n IH].
    - intros g c (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & HT & _). lia.
    - intros g c HC. destruct (Z_le_dec 0 (5 - Z.of_nat (S n))) as [Hp|Hn].
      + apply (step15 (5 - Z.of_nat (S n))); [| exact Hac | | exact HC].
        * destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & HT & _). lia.
        * intros g' c' HC'. apply IH. replace (5 - Z.of_nat n) with (5 - Z.of_nat (S n) + 1) by lia. exact HC'.
      + destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & HT & _). lia. }
  intros g c (t & HC).
  assert (Ht : 0 <= t <= 4) by (destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & HT & _); lia).
  apply (IND (Z.to_nat (5 - t))). replace (5 - Z.of_nat (Z.to_nat (5 - t))) with t by lia. exact HC.
Qed.

End H15.
