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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Definition sx40 (c : Z) : Z := if c <? 128 then c else c + 1099511627776 - 256.

Lemma sx40_range : forall c, 0 <= c < 256 -> 0 <= sx40 c < 1099511627776.
Proof. intros c H. unfold sx40. destruct (Z.ltb_spec c 128); lia. Qed.

Lemma sx40_inj : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> sx40 a = sx40 b -> a = b.
Proof. intros a b Ha Hb. unfold sx40. destruct (Z.ltb_spec a 128), (Z.ltb_spec b 128); lia. Qed.

Lemma byte_lit : forall b : byte, b = Z_to_bv 8 (bv_unsigned b).
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

Lemma sxb_shift : forall b : byte,
  (bv_unsigned (sxb b) * 16777216) mod 18446744073709551616 = 16777216 * sx40 (bv_unsigned b).
Proof.
  intros b. rewrite (byte_lit b) at 1. pose proof (byte_range b) as R. revert R.
  generalize (bv_unsigned b) as c. intros c Hc.
  pose proof (z_all_spec (fun c => (bv_unsigned (sxb (Z_to_bv 8 c)) * 16777216) mod 18446744073709551616 =?
    16777216 * sx40 c) (Z.to_nat 256) 0 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma w4_val : forall b0 b1 b2 b3 : byte,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb b3) ≪ 24)))
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b2) ≪ 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b1) ≪ 8)))
      (bv_unsigned (zxb b0))))))) =
  16777216 * sx40 (bv_unsigned b3) + 65536 * bv_unsigned b2 + 256 * bv_unsigned b1 + bv_unsigned b0.
Proof.
  intros b0 b1 b2 b3.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  pose proof (sx40_range _ (byte_range b3)) as R3.
  pose proof (sxb_shift b3) as S3.
  unfold zxb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 24) with 16777216 in *. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  rewrite S3.
  rewrite (Z.mod_small (bv_unsigned b0)), (Z.mod_small (bv_unsigned b1)), (Z.mod_small (bv_unsigned b2)) by lia.
  rewrite (Z.mod_small (bv_unsigned b1 * 256)), (Z.mod_small (bv_unsigned b2 * 65536)) by lia.
  rewrite (KindBGlue.kb_lor_low (bv_unsigned b1 * 256) (bv_unsigned b0) 8)
    by (first [lia | change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; Z.div_mod_to_equations; lia]).
  rewrite (Z.mod_small (bv_unsigned b1 * 256 + bv_unsigned b0)) by lia.
  rewrite (KindBGlue.kb_lor_low (16777216 * sx40 (bv_unsigned b3)) (bv_unsigned b2 * 65536) 24)
    by (first [lia | change (2 ^ 24) with 16777216; lia | change (2 ^ 24) with 16777216; Z.div_mod_to_equations; lia]).
  rewrite (Z.mod_small (16777216 * sx40 (bv_unsigned b3) + bv_unsigned b2 * 65536)) by lia.
  rewrite (KindBGlue.kb_lor_low (16777216 * sx40 (bv_unsigned b3) + bv_unsigned b2 * 65536)
    (bv_unsigned b1 * 256 + bv_unsigned b0) 16)
    by (first [lia | change (2 ^ 16) with 65536; lia | change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma w4_eqb : forall a0 a1 a2 a3 b0 b1 b2 b3 : byte,
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb a3) ≪ 24)))
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb a2) ≪ 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb a1) ≪ 8)))
      (bv_unsigned (zxb a0)))))))
  (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb b3) ≪ 24)))
      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b2) ≪ 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b1) ≪ 8)))
      (bv_unsigned (zxb b0)))))))
  = bytes_eqb [a0; a1; a2; a3] [b0; b1; b2; b3].
Proof.
  intros. unfold bv_eqb. rewrite !w4_val. cbn [bytes_eqb].
  pose proof (byte_range a0). pose proof (byte_range a1). pose proof (byte_range a2). pose proof (byte_range a3).
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  pose proof (sx40_range _ (byte_range a3)). pose proof (sx40_range _ (byte_range b3)).
  destruct (Z.eqb_spec (bv_unsigned a0) (bv_unsigned b0)); destruct (Z.eqb_spec (bv_unsigned a1) (bv_unsigned b1));
    destruct (Z.eqb_spec (bv_unsigned a2) (bv_unsigned b2)); destruct (Z.eqb_spec (bv_unsigned a3) (bv_unsigned b3));
    cbn [andb]; try (apply Z.eqb_neq; lia).
  apply Z.eqb_eq. match goal with H : bv_unsigned a3 = bv_unsigned b3 |- _ => rewrite H end. lia.
  all: apply Z.eqb_neq; intros E;
    match goal with HN : bv_unsigned ?x <> bv_unsigned ?y |- _ =>
      apply HN; apply sx40_inj; [apply byte_range | apply byte_range | lia] end.
Qed.

Lemma skipn4 : forall l : list byte, (4 <= length l)%nat ->
  skipn (length l - 4) l = [nth (length l - 4) l (Z_to_bv 8 0); nth (length l - 3) l (Z_to_bv 8 0);
    nth (length l - 2) l (Z_to_bv 8 0); nth (length l - 1) l (Z_to_bv 8 0)].
Proof.
  intros l H. remember (length l) as n eqn:En.
  rewrite (Tac_si.skipn_nth l (n - 4)) by lia. replace (S (n - 4)) with (n - 3)%nat by lia.
  rewrite (Tac_si.skipn_nth l (n - 3)) by lia. replace (S (n - 3)) with (n - 2)%nat by lia.
  rewrite (Tac_si.skipn_nth l (n - 2)) by lia. replace (S (n - 2)) with (n - 1)%nat by lia.
  rewrite (Tac_si.skipn_nth l (n - 1)) by lia. replace (S (n - 1)) with n by lia.
  rewrite En, skipn_all. reflexivity.
Qed.

Lemma firstn4 : forall l : list byte, length l = 4%nat ->
  firstn 4 l = [RcIdentModel.nthb l 0; RcIdentModel.nthb l 1; RcIdentModel.nthb l 2; RcIdentModel.nthb l 3].
Proof. intros [|a [|b [|c [|d [|e l]]]]] H; cbn in H; try lia. reflexivity. Qed.

Section H05.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_H05 : Hcut B APIf ra (Inv_K13968 B APIf ra empty) -> Hcut B APIf ra (Inv_K139a4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1390c B APIf ra empty).
Proof.
  intros H68 Ha4 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H68 | exact Ha4 | | | exact HC | ].
  { intros c' HC'. unfold Inv_K13968. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K139a4. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E19 & E26 & E10 & HB).
  pose proof HN1 as (HN0 & E8 & HW4 & HQ200 & HQ168).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HSC).
  pose proof (n_stem_len (g_in g)) as L16.
  destruct (nzb_W4 _ HW) as [NZW LW].
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME, zlen in E10'. unfold zlen in E26.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold cstr, spk, fsp, SLOT_FRAME in HW4n.
  assert (KMm : forall m', mem_rel rsegs m' (normalize rsegs mem) -> KM [] mem m').
  { intros m' HREL. exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL). }
  assert (HOk : forall m', mem_rel rsegs m' (normalize rsegs mem) -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HOU). }
  unfold rmk, Frame.mkR. rewrite E2, E26, E10'.
  step. step.
  rewrite bv_ltu_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (n_stem (g_in g)))) 4) as [HL|HL]; cbn [negb].
  - apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I;
        rewrite HG; reflexivity.
    + rewrite HG. exact E19.
    + rewrite HG. reflexivity.
    + apply (fin_bytes m' (normalize rsegs mem) _ _ HREL). exact (bytes_at_normalize rsegs mem _ _ HRO HB).
    + unfold n_ends_w4. replace (4 <=? length (n_stem (g_in g)))%nat with false
        by (symmetry; apply Nat.leb_gt; lia). reflexivity.
  - pose proof (fun k (Hk : (k < length (n_stem (g_in g)))%nat) => rd1 _ _ _ (bytes_at_one _ _ _ k HBn Hk)) as RS.
    pose proof (RS (length (n_stem (g_in g)) - 4)%nat ltac:(lia)) as RS0.
    pose proof (RS (length (n_stem (g_in g)) - 3)%nat ltac:(lia)) as RS1.
    pose proof (RS (length (n_stem (g_in g)) - 2)%nat ltac:(lia)) as RS2.
    pose proof (RS (length (n_stem (g_in g)) - 1)%nat ltac:(lia)) as RS3.
    clear RS.
    pose proof (Tac_si.cstr_byte _ _ _ 0 HW4n ltac:(lia)) as RW0.
    pose proof (Tac_si.cstr_byte _ _ _ 1 HW4n ltac:(lia)) as RW1.
    pose proof (Tac_si.cstr_byte _ _ _ 2 HW4n ltac:(lia)) as RW2.
    pose proof (Tac_si.cstr_byte _ _ _ 3 HW4n ltac:(lia)) as RW3.
    rewrite Tac_si.nthb_snoc_lt in RW0, RW1, RW2, RW3 by lia.
    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    step. step. step.
    rewrite w4_eqb.
    assert (EW : n_ends_w4 (g_in g) = bytes_eqb
      [nth (length (n_stem (g_in g)) - 4) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 3) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 2) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 1) (n_stem (g_in g)) (Z_to_bv 8 0)]
      [RcIdentModel.nthb (n_W4 (g_in g)) 0; RcIdentModel.nthb (n_W4 (g_in g)) 1;
       RcIdentModel.nthb (n_W4 (g_in g)) 2; RcIdentModel.nthb (n_W4 (g_in g)) 3]).
    { unfold n_ends_w4. replace (4 <=? length (n_stem (g_in g)))%nat with true
        by (symmetry; apply Nat.leb_le; lia).
      rewrite skipn4 by lia. rewrite firstn4 by exact LW. reflexivity. }
    rewrite <- EW.
    destruct (n_ends_w4 (g_in g)) eqn:EE; br_if.
    + apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. cbv beta.
      split; [|split; [|split]].
      * apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I;
          rewrite HG; reflexivity.
      * rewrite HG. exact E19.
      * rewrite HG. unfold n_ln, n_EXP_NM. rewrite EE. reflexivity.
      * unfold n_EXP_NM. rewrite EE. apply (fin_bytes m' (normalize rsegs mem) _ _ HREL).
        exact (bytes_at_normalize rsegs mem _ _ HRO HB).
    + apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. cbv beta.
      split; [|split; [|split; [|split]]].
      * apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I;
          rewrite HG; reflexivity.
      * rewrite HG. exact E19.
      * rewrite HG. reflexivity.
      * apply (fin_bytes m' (normalize rsegs mem) _ _ HREL). exact (bytes_at_normalize rsegs mem _ _ HRO HB).
      * reflexivity.
Qed.

End H05.
