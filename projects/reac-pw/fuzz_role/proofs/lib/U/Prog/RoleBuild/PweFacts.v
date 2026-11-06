(** A call of pod_write_ent(pp, e) from the UBSan builder (0x131b4, 0x13c60, 0x13d6c): the premises of
    U/Prog/pod_write_ent_c.v built from the block image [MBr] carries, and its post turned back into [MBr] of the
    image with the pod appended (Pod/Layout.v [pp_image_put]).

    pod_write_ent writes the pod's bytes at pp + len, the len cell at pp + 16384 and its frame below sp; the block's
    other bytes, the input, the frame's locals and the tables stay. Stated over any image [pp_image b ...]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Alignment: pp and sp are 16-aligned, so pp is 8-aligned and e = sp + 0xb8 is 4-aligned *)
Lemma mod_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma mod_16_add4 : forall x c, x mod 16 = 0 -> c mod 4 = 0 -> (x + c) mod 4 = 0.
Proof. intros x c H1 H2. Z.div_mod_to_equations. lia. Qed.

(** ** Bytes at A after a call that wrote two ranges of them (and memory elsewhere) *)
Lemma bytes_at_two_patches : forall W m1 m2 A Ib (o1 : nat) x (o2 : nat) y,
  bytes_at rsegs m1 A Ib -> munch W m1 m2 ->
  bytes_at rsegs m2 (A + Z.of_nat o1) x -> bytes_at rsegs m2 (A + Z.of_nat o2) y ->
  (o1 + length x <= length Ib)%nat -> (o2 + length y <= length Ib)%nat ->
  (forall j, (j < length Ib)%nat -> ~ (o1 <= j < o1 + length x)%nat -> ~ (o2 <= j < o2 + length y)%nat ->
     outside W (A + Z.of_nat j)) ->
  bytes_at rsegs m2 A (overwrite (overwrite Ib o1 x) o2 y).
Proof.
  intros W m1 m2 A Ib o1 x o2 y (H0 & H1 & HI) MU (_ & _ & HX) (_ & _ & HY) L1 L2 HO.
  rewrite <- (upd_overwrite Ib o1 x), <- (upd_overwrite (upd_bytes Ib o1 x) o2 y).
  assert (L1' : length (upd_bytes Ib o1 x) = length Ib) by (apply upd_bytes_length; exact L1).
  assert (LO : length (upd_bytes (upd_bytes Ib o1 x) o2 y) = length Ib) by (rewrite upd_bytes_length; lia).
  split; [exact H0|]. split; [rewrite LO; exact H1|].
  intros j Hj. rewrite LO in Hj.
  rewrite (upd_bytes_nth (upd_bytes Ib o1 x) o2 y j) by lia.
  destruct (Nat.leb o2 j && Nat.ltb j (o2 + length y))%bool eqn:E2.
  - apply andb_true_iff in E2 as [E2a E2b]. apply Nat.leb_le in E2a. apply Nat.ltb_lt in E2b.
    rewrite <- (HY (j - o2)%nat ltac:(lia)). f_equal. unfold wa. f_equal. lia.
  - rewrite (upd_bytes_nth Ib o1 x j) by lia.
    destruct (Nat.leb o1 j && Nat.ltb j (o1 + length x))%bool eqn:E1.
    + apply andb_true_iff in E1 as [E1a E1b]. apply Nat.leb_le in E1a. apply Nat.ltb_lt in E1b.
      rewrite <- (HX (j - o1)%nat ltac:(lia)). f_equal. unfold wa. f_equal. lia.
    + rewrite <- (HI j Hj). unfold mrd. rewrite (MU (wa (A + Z.of_nat j))); [reflexivity|].
      rewrite wa_unsigned by lia. apply HO; [exact Hj | |].
      * intros [Ha Hb]. rewrite (proj2 (Nat.leb_le _ _) Ha), (proj2 (Nat.ltb_lt _ _) Hb) in E1. discriminate E1.
      * intros [Ha Hb]. rewrite (proj2 (Nat.leb_le _ _) Ha), (proj2 (Nat.ltb_lt _ _) Hb) in E2. discriminate E2.
Qed.

Section PWE.
Variables (sp : word) (m : word -> option byte) (rest : list byte) (src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.

(** ** pod_write_ent's post as [MBr] *)
Lemma MBr_call_pwe : forall Ib m1 m2 (L : Z) X Y,
  MBr sp m rest src pp lo Ib m1 ->
  munch [(bv_unsigned sp - 32, bv_unsigned sp); (pp + L, pp + L + Z.of_nat (length X));
         (pp + 16384, pp + 16384 + 8)] m1 m2 ->
  wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp) ->
  bytes_at rsegs m2 (pp + L) X -> bytes_at rsegs m2 (pp + 16384) Y -> length Y = 8%nat ->
  0 <= L -> L + Z.of_nat (length X) <= 16384 ->
  MBr sp m rest src pp lo (overwrite (overwrite Ib (Z.to_nat L) X) (Z.to_nat 16384) Y) m2.
Proof.
  intros Ib m1 m2 L X Y MB MU WM MI ST HX HY LY HL0 HL1.
  pose proof MB as (HI & HLn & HW & HR & MU0 & WM0 & MI0 & HS & HT).
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HLo & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HLn, HP1, HDJ, HM1, HSP.
  set (W := [(bv_unsigned sp - 32, bv_unsigned sp); (pp + L, pp + L + Z.of_nat (length X));
             (pp + 16384, pp + 16384 + 8)]) in MU.
  assert (SUB : sub_fp W (W0 sp pp)).
  { unfold sub_fp, W0, W. cbn [outside]. unfold MID_STACK, FRAME_LOCALS, POD_PROPS.
    intros x (H1 & H2 & _). split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (LX : length (overwrite Ib (Z.to_nat L) X) = length Ib) by (apply overwrite_len; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply (bytes_at_two_patches W m1 m2 pp Ib (Z.to_nat L) X (Z.to_nat 16384) Y HI MU).
    + rewrite Z2Nat.id by lia. exact HX.
    + exact HY.
    + lia.
    + lia.
    + intros j Hj N1 N2. unfold W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - rewrite overwrite_len by (rewrite LX; lia). rewrite LX. exact HLn.
  - exact (wr_at_transport rsegs m1 m2 _ _ HW WM).
  - apply (bytes_at_transport rsegs W m1 m2 _ _ HR MU). unfold W. cbn [disjoint_from].
    destruct HDJ as [D|D]; (split; [lia|]); (split; [lia|]); (split; [lia | exact I]).
  - apply (munch_trans _ m m1 m2 MU0). exact (munch_weaken W _ m1 m2 SUB MU).
  - exact (wmono_trans rsegs m m1 m2 WM0 WM).
  - exact MI.
  - unfold FRAME_LOCALS in *.
    destruct (stk_split rsegs m1 lo (bv_unsigned sp) _ HS ltac:(lia)) as [_ HS2].
    apply (stk_merge rsegs m2 lo (bv_unsigned sp)); [exact ST | | lia].
    apply (stk_transport_disjoint rsegs W m1 m2 _ _ HS2 MU WM). unfold W. cbn [disjoint_from].
    split; [lia|]. split; [lia|]. split; [lia | exact I].
  - intros a Ha. unfold mrd. rewrite (MU (wa a)).
    + exact (HT a Ha).
    + rewrite (wa_unsigned a) by (unfold RELRO_TBL, RELRO_TBL_END in *; lia).
      apply SUB. eapply relro_out_W0; eauto.
Qed.

(** The same over a block image: the image with x (= enc_pod e) appended to buf, len moved (pod.h:200-206). *)
Lemma MBr_pwe_post : forall b isp hasp pst es corr x m1 m2,
  MBr sp m rest src pp lo (pp_image b isp hasp pst es corr) m1 ->
  munch [(bv_unsigned sp - 32, bv_unsigned sp);
         (pp + Z.of_nat (length b), pp + Z.of_nat (length b) + Z.of_nat (length x));
         (pp + 16384, pp + 16384 + 8)] m1 m2 ->
  wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp) ->
  bytes_at rsegs m2 (pp + Z.of_nat (length b)) x ->
  bytes_at rsegs m2 (pp + 16384) (le8 (Z_to_bv 64 (Z.of_nat (length b) + Z.of_nat (length x)))) ->
  Z.of_nat (length b) + Z.of_nat (length x) <= POD_BUF_MAX ->
  MBr sp m rest src pp lo (pp_image (b ++ x) isp hasp pst es corr) m2.
Proof.
  intros b isp hasp pst es corr x m1 m2 MB MU WM MI ST HX HY Hb. unfold POD_BUF_MAX in Hb.
  pose proof (MBr_call_pwe _ m1 m2 (Z.of_nat (length b)) x _ MB MU WM MI ST HX HY (length_le8 _)
                ltac:(lia) ltac:(lia)) as H.
  rewrite Nat2Z.id, le8_lit64 in H.
  rewrite pp_image_put by (unfold POD_BUF_MAX; lia). rewrite Nat2Z.inj_add. exact H.
Qed.

(** ** The premises from the block image *)
(** The len cell at pp + 16384 holds |b|. *)
Lemma MBr_len_cell : forall b isp hasp pst es corr m1,
  MBr sp m rest src pp lo (pp_image b isp hasp pst es corr) m1 -> Z.of_nat (length b) <= POD_BUF_MAX ->
  rw_cells rsegs m1 (pp + 16384) [C8 (Z_to_bv 64 (Z.of_nat (length b)))].
Proof.
  intros b isp hasp pst es corr m1 MB Hb.
  pose proof MB as (_ & HL & _).
  pose proof (MBr_pp_cells sp m rest src pp lo _ m1 16384 8 MB ltac:(lia) ltac:(unfold POD_PROPS in HL; lia)) as H.
  change (Z.to_nat 16384) with (Z.to_nat OFF_LEN) in H.
  rewrite pp_image_slice_len in H by exact Hb. rewrite <- le8_lit64 in H.
  destruct H as [[_ HB] HW]. split; [split; [exact (conj I I) | exact HB] | exact HW].
Qed.

(** The same cell as the builder's `ld a0,0(s7)` reads it (s7 = pp + 0x4000). *)
Lemma MBr_len_load : forall b isp hasp pst es corr m1,
  MBr sp m rest src pp lo (pp_image b isp hasp pst es corr) m1 -> Z.of_nat (length b) <= POD_BUF_MAX ->
  ov_read_bytes rsegs m1 (wa (pp + POD_LEN_OFF)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length b)))).
Proof.
  intros b isp hasp pst es corr m1 MB Hb.
  pose proof MB as (_ & HL & _).
  erewrite MBr_read; [ | exact MB | unfold POD_LEN_OFF; lia | unfold POD_LEN_OFF, POD_PROPS in *; lia ].
  unfold POD_LEN_OFF. change (Z.to_nat 16384) with (Z.to_nat OFF_LEN).
  rewrite pp_image_slice_len by exact Hb. rewrite le8_lit64. reflexivity.
Qed.

(** The n bytes past buf[0..len) are the memset's zeros, writable. *)
Lemma MBr_buf_cells : forall b isp hasp pst es corr m1 (n : nat),
  MBr sp m rest src pp lo (pp_image b isp hasp pst es corr) m1 ->
  Z.of_nat (length b) + Z.of_nat n <= POD_BUF_MAX ->
  rw_cells rsegs m1 (pp + Z.of_nat (length b)) [CB n (zeros n)].
Proof.
  intros b isp hasp pst es corr m1 n MB Hb. unfold POD_BUF_MAX in Hb.
  pose proof MB as (_ & HL & _). unfold POD_PROPS in HL.
  pose proof (MBr_pp_cells sp m rest src pp lo _ m1 (Z.of_nat (length b)) n MB ltac:(lia) ltac:(lia)) as H.
  replace (firstn n (skipn (Z.to_nat (Z.of_nat (length b))) (pp_image b isp hasp pst es corr))) with (zeros n) in H;
    [exact H|].
  rewrite Nat2Z.id, pp_image_tail, (skipn_app_eq b _ (length b) eq_refl).
  rewrite firstn_app_le by (rewrite length_zeros; unfold POD_BUF_MAX; lia).
  replace (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) with (n + (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)) - n))%nat
    by (unfold POD_BUF_MAX; lia).
  rewrite zeros_app. first [apply firstn_app_eq | symmetry; apply firstn_app_eq]. rewrite length_zeros. reflexivity.
Qed.

(** pod_write_ent's frame [sp - 32, sp) lies in the walk's stack window. *)
Lemma MBr_stk_sp : forall Ib m1, MBr sp m rest src pp lo Ib m1 -> stk rsegs m1 lo (bv_unsigned sp).
Proof.
  intros Ib m1 (_ & _ & _ & _ & _ & _ & _ & HS & _).
  pose proof HOK as (_ & _ & _ & _ & HM1 & _ & _ & _ & _ & _). unfold MID_STACK, FRAME_LOCALS in *.
  exact (proj1 (stk_split rsegs m1 lo (bv_unsigned sp) _ HS ltac:(lia))).
Qed.

Lemma MBr_mem_inv : forall Ib m1, MBr sp m rest src pp lo Ib m1 -> mem_inv rsegs m1.
Proof. intros Ib m1 (_ & _ & _ & _ & _ & _ & MI & _). exact MI. Qed.

End PWE.
