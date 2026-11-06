From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma n28_fz_nth : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
  induction l as [|b l IH]; cbn [length first_zero]; intros H; [lia|].
  destruct (Z.eqb_spec (bz b) 0) as [E|E]; [exact E|].
  cbn [nth]. apply IH. lia.
Qed.

Lemma n28_name0 : forall p, (name_len p < Nat.min (length p - 1) 16)%nat ->
  bz (nthb p (S (name_len p))) = 0.
Proof.
  intros p H.
  set (n' := Nat.min (length p - 1) (NAME_CAP - 1)).
  assert (Ln : length (firstn n' (skipn 1 p)) = n') by (rewrite length_firstn, length_skipn; unfold n', NAME_CAP; lia).
  pose proof (n_name_len_fz p) as E. fold n' in E.
  assert (Hn : (first_zero (firstn n' (skipn 1 p)) < length (firstn n' (skipn 1 p)))%nat)
    by (rewrite Ln, <- E; unfold n', NAME_CAP; lia).
  pose proof (n28_fz_nth _ Hn) as Z0. rewrite <- E in Z0.
  rewrite nth_first in Z0 by (unfold n', NAME_CAP in *; lia).
  clear -Z0 H. unfold nthb. destruct p as [|x r]; [cbn in H; lia|]. cbn [skipn] in Z0. cbn [nth]. exact Z0.
Qed.

Lemma n28_hw : forall inp i, rec_addr inp i = ADDR_MODEL_NAME -> rec_hw inp (S i) = rec_hw inp i.
Proof. intros inp i H. cbn [rec_hw]. rewrite H. reflexivity. Qed.

Ltac n28_cmp := rewrite ?tb_eqb_lit, ?tb_ltu_lit
  by first [ lia | match goal with |- context [@bv_unsigned 8 ?b] => pose proof (tb_byte_range b); lia end ].

Ltac n28_fin :=
  apply Exec.evt_done; eexists _, _; split; [reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|];
  split; [apply munch_refl|]; split; [apply wmono_refl|]; apply Forall_nil.

Ltac ubr := let H := fresh "HU" in if_cases H; zify_cond H; try (exfalso; lia);
  try (exfalso; rewrite Z.mod_small in H by lia; lia).

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_B28 : forall i,
  Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13604_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x13604 0x13660 _ _ _
    (fun regs m => Z.of_nat i < NR g /\ getr regs 9 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G24 g m /\
       HWb g (S i) 0 m /\ EVb g m /\ IDb g (S i) m /\
       getr regs 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)) /\
       getr regs 20 = Z_to_bv 64 (rec_k (g_in g) i) /\ LPm g i m /\ getr regs 21 = Z_to_bv 64 pl) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & (E23 & E18 & E25 & E19 & E27) &
    E24 & HNMA & E22 & E8 & E10).
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEVb).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HM Hin) as [Hpl1 Hpl2].
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  pose proof HNMA as (HR1 & HA).
  destruct (n_nma (g_in g) i HR1 HA) as (_ & HW & HW1 & HWk & _).
  change (rec_id (g_in g) (S i)) with (idS g i) in HW.
  pose proof (name_len_le (rec_pl (g_in g) i)) as (HW16 & _).
  pose proof (rec_pl_length (g_in g) i) as Hpl.
  pose proof (rec_k_range (g_in g) i) as Hkr.
  exists [], ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)));
    (20%bv, Z_to_bv 64 (rec_k (g_in g) i)); (21%bv, Z_to_bv 64 pl)] : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold PLB in HPL. pose proof (bytes_at_bound rsegs _ _ _ HPL) as Hplb. rewrite Hpl in Hplb.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HPL) as HPLn.
    unfold rmk. rewrite E2, E3, E4, E9, E20, E26, E21, E22, E8, E10.
    unfold fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    step. n28_cmp. cbn [Z.eqb negb].
    step. step. n28_cmp.
    destruct (Z.ltb_spec 15 (wn (idS g i))) as [H15|H15]; cbn [negb]; [n28_fin|].
    step. n28_cmp.
    destruct (Z.ltb_spec (wn (idS g i) + 1) (rec_k (g_in g) i)) as [Hlt|Hge]; cbn [negb]; [|n28_fin].
    assert (HZ : bv_unsigned (nthb (rec_pl (g_in g) i) (Z.to_nat (wn (idS g i) + 1))) = 0).
    { replace (Z.to_nat (wn (idS g i) + 1)) with (S (name_len (rec_pl (g_in g) i))) by lia.
      apply n28_name0. lia. }
    pose proof (tb_rd1 _ _ _ (wn (idS g i) + 1) HPLn ltac:(lia) ltac:(lia)) as RD.
    step. ubr. step. step. ubr. step. ubr.
    step. step. unfold zxb. n28_cmp. rewrite HZ. cbn [Z.eqb negb].
    step. n28_fin.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold NRb, G24, HWb, EVb, IDb, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1' & HW2' & HW3').
    unfold rec_have, rec_hwb. rewrite (n28_hw _ _ HA).
    fold (rec_have (g_in g) i). fold (rec_hwb (g_in g) i).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
