From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb3.
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

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B28 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13480_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x13480 0x134c8 _ _ _
    (fun regs m => Z.of_nat i < NR g /\ getr regs 19 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G16 g m /\
       HWb g (S i) m /\ IDb g (S i) m /\
       getr regs 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\ getr regs 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
       getr regs 18 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 22 = Z_to_bv 64 pl) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E21 & E20 & E22 & HPL & HID & HAG & HBF & HLP) & E27 & E24 & E25 & E26 &
    HNMA & E23 & E18 & E9 & E8 & E10).
  pose proof HREC as (Hi & E19 & HNR & HG16 & HHW).
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
  exists [], ([(19%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (g_p g + rec_body (g_in g) i));
    (21%bv, Z_to_bv 64 (rec_k (g_in g) i)); (18%bv, Z_to_bv 64 (rec_Lp (g_in g) i)); (22%bv, Z_to_bv 64 pl)]
    : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold PLB in HPL. pose proof (bytes_at_bound rsegs _ _ _ HPL) as Hplb. rewrite Hpl in Hplb.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HPL) as HPLn.
    unfold rmk. rewrite E2, E3, E4, E19, E21, E20, E22, E18, E9, E8, E10.
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
    step. step. step. unfold zxb. n28_cmp. rewrite HZ. cbn [Z.eqb negb].
    step. n28_fin.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold NRb, G16, HWb, IDb in *. unfold q64, u32 in *.
    destruct HHW as (HW1' & HW2' & HW3').
    unfold rec_have, rec_hwb. rewrite (n28_hw _ _ HA).
    fold (rec_have (g_in g) i). fold (rec_hwb (g_in g) i).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
