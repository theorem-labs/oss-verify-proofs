(* Helpers of batch b7 (E04, Q01-Q06) of fuzz_ctrl LLVMFuzzerTestOneInput (plain): the frame-turn model facts the
   segments read (t_g = the first 50 bytes of Φ, the lengths of ID_j and FG_j, struct P5.4), the ports facts of
   C5.3-C5.8, the transport of the is_8819 / check_ports bundles across a run, and branch-condition tactics. *)
(* libreac v1.9.0 (SlotInv.v header): the footprints follow the v1.9.0 frame (DJE: [sp+8, sp+192) and the parse
   result [sp+1752, sp+1788); DJP: the ports slots [sp+1688, sp+1700); DJQ: check_ports `first` at sp+1792); EQR
   follows EQ's v1.9.0 registers (FT / FC: j s10, left - h s11, len s4, Φ s5; V7 s7; V2m s2; VCm s6; IFS's nb s3),
   so s1 (V0, not in EQ) left it; b7_EQ reads FSb's v1.9.0 `first` (have [sp+16], nb in s3, the body at sp+40,
   b7_nb_range) and FC's body pointer at sp+32.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcIdentModel RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- The frame-turn model: Φ's length, t_g = the first 50 bytes of Φ ---- *)

Lemma b7_bat_nonneg : forall bs i, 0 <= RcFrag.bat bs i.
Proof.
  intros bs i. unfold RcFrag.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia.
Qed.

Lemma b7_inb_nonneg : forall inp k, 0 <= inb inp k.
Proof.
  intros inp k. unfold inb, RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb inp (Z.to_nat k))).
  lia.
Qed.

Lemma b7_len_nonneg : forall inp c, 0 <= f_len inp c.
Proof.
  intros inp c. unfold f_len, f_L, f_h. pose proof (b7_inb_nonneg inp c). pose proof (b7_inb_nonneg inp (c + 1)).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma b7_fc_nonneg : forall inp j, 0 <= fc inp j.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - unfold f_next, f_body, f_h, f_left. pose proof (b7_len_nonneg inp (fc inp j)). unfold nlen in *. lia.
Qed.

Lemma b7_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. unfold t_phi, t_len, f_phi.
  pose proof (b7_fc_nonneg inp j) as Hc. pose proof (b7_len_nonneg inp (fc inp j)) as Hl.
  set (c := fc inp j) in *.
  assert (Hle : f_len inp c <= f_left inp c - f_h inp c) by (unfold f_len; lia).
  unfold f_body, f_h, f_left, nlen in *.
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma b7_len_phi : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof.
  intros inp j. rewrite b7_phi_length. pose proof (b7_len_nonneg inp (fc inp j)). unfold t_len. lia.
Qed.

Lemma b7_g_firstn : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. unfold t_g, fr50. rewrite firstn_app.
  replace (50 - length (t_phi inp j))%nat with 0%nat by (rewrite b7_phi_length; lia).
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma b7_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply (proj1 (bytes_at_app rsegs m a _ _)) in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply (proj1 (bytes_at_app rsegs m _ _ _)) in H as [H _].
  exact H.
Qed.

Lemma b7_g_bytes : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H Hl. rewrite (b7_g_firstn inp j Hl).
  pose proof (b7_bytes_sub m phi (t_phi inp j) 0 50 H ltac:(rewrite b7_phi_length; lia)) as H'.
  rewrite Z.add_0_r in H'. exact H'.
Qed.

Lemma b7_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

Lemma b7_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* One byte of a bytes_at as the read the step tactic consumes. *)
Lemma b7_rd1 : forall m a bs k d, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [nth k bs d].
Proof.
  intros m a bs k d H Hk. pose proof (bytes_at_read rsegs m a bs (Z.of_nat k) 1 H ltac:(lia) ltac:(lia)) as R.
  rewrite Nat2Z.id in R. rewrite (b7_firstn1 bs k d Hk) in R. exact R.
Qed.

Lemma b7_rdn : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

(* The n bytes from index k of a list, one nth each (default 0). *)
Fixpoint b7_nths (bs : list byte) (k n : nat) : list byte :=
  match n with
  | O => []
  | S n' => nth k bs (Z_to_bv 8 0) :: b7_nths bs (S k) n'
  end.

Lemma b7_skipn_cons : forall (bs : list byte) k d, (k < length bs)%nat -> skipn k bs = nth k bs d :: skipn (S k) bs.
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma b7_firstn_nths : forall n bs k, (k + n <= length bs)%nat -> firstn n (skipn k bs) = b7_nths bs k n.
Proof.
  induction n as [|n IH]; intros bs k H; [reflexivity|].
  rewrite (b7_skipn_cons bs k (Z_to_bv 8 0)) by lia. cbn [firstn b7_nths]. f_equal. apply IH. lia.
Qed.

Lemma b7_bytes_nths : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (b7_nths bs k n).
Proof. intros m a bs k n H Hk. rewrite <- b7_firstn_nths by exact Hk. exact (b7_bytes_sub m a bs k n H Hk). Qed.

Lemma b7_bsl_nths : forall bs k n, 0 <= k -> 0 <= n -> (Z.to_nat k + Z.to_nat n <= length bs)%nat ->
  RcFrag.bsl bs k n = b7_nths bs (Z.to_nat k) (Z.to_nat n).
Proof. intros bs k n Hk Hn H. unfold RcFrag.bsl. apply b7_firstn_nths. exact H. Qed.

(* ID_j has 38 bytes and FG_j 72 at every turn. *)
Lemma b7_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn.
    assert (E : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                  (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
    { unfold fg_id, rp_id.
      assert (E1 : length (if RcReply.ir (t_len inp j) (t_g inp j)
                           then snd (RcIdentModel.ING (fs_id (fst_at inp j)) (r_addr (t_g inp j)) (r_pl (t_g inp j)))
                           else fs_id (fst_at inp j)) = 38%nat).
      { destruct (RcReply.ir (t_len inp j) (t_g inp j)); [apply RcIdentModel.ING_length; exact IH | exact IH]. }
      match goal with |- context [if ?c then _ else ?x] => destruct c end; [|exact E1].
      apply RcIdentModel.ING_length. exact E1. }
    destruct (f_opens (t_len inp j) (t_g inp j)); exact E.
Qed.

Lemma b7_bsl_length : forall bs k n, length (RcFrag.bsl bs k n) = Nat.min (Z.to_nat n) (length bs - Z.to_nat k).
Proof. intros bs k n. unfold RcFrag.bsl. rewrite length_firstn, length_skipn. reflexivity. Qed.

Lemma b7_fg_st_length : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  pose proof (b7_bat_nonneg st 7) as Hlf.
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|cbn [fg_next]; exact Hs].
  unfold RcFrag.fg_fr in Efr. rewrite !andb_true_iff in Efr.
  destruct Efr as (((((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & N1) & N22) & _).
  apply Z.leb_le in N1. apply Z.leb_le in N22.
  assert (Lb : length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g)).
  { unfold RcFrag.fg_body. rewrite b7_bsl_length. lia. }
  assert (Lc : forall s, length s = 72%nat -> length (RcFrag.fg_clear s) = 72%nat).
  { intros s Hs'. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first. rewrite !length_app, length_skipn, b7_bsl_length, Lb. cbn [length].
    lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + unfold RcFrag.fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as (_ & HT). apply Z.leb_le in HT.
      unfold RcFrag.fg_T, RcFrag.fg_lf in HT.
      assert (Lj : length (RcFrag.fg_join st g) = 72%nat).
      { unfold RcFrag.fg_join, RcFrag.fg_T, RcFrag.fg_lf.
        rewrite !length_app, length_firstn, length_skipn, Lb, Hs. lia. }
      destruct (negb (RcFrag.fg_close st g)); cbn [fg_next]; apply Lc; exact Lj.
    + cbn [fg_next]. apply Lc. exact Hs.
Qed.

Lemma b7_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    assert (E : length (fg_st (t_len inp j) (fs_fg (fst_at inp j)) (t_g inp j)) = 72%nat)
      by (apply b7_fg_st_length; [exact IH | apply b7_g_length]).
    destruct (f_opens (t_len inp j) (t_g inp j)); exact E.
Qed.

(* v1.9.0 `first`: nb (= the length of its body, FSb) is 0 or fg_n of an opening fragment, 1 .. 22 (fg_fr). *)
Lemma b7_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 22.
Proof.
  intros inp j. induction j as [|j IH]; [cbn [fst_at fs0 fs_nb]; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo; cbn [fs_nb]; [|exact IH].
  unfold f_opens in Eo. apply andb_true_iff in Eo as [Efr _].
  unfold RcFrag.fg_fr in Efr. rewrite !andb_true_iff in Efr.
  destruct Efr as (((((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & N1) & N22) & _).
  apply Z.leb_le in N1. apply Z.leb_le in N22. unfold RcFrag.fg_n in N1, N22. lia.
Qed.

Lemma b7_big_8819 : forall inp j, t_8819 inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_8819, t_big in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Z.leb_le. exact H.
Qed.

(* struct P5.4: kind 6 needs Φ[18] = 4 and Φ[19] = 3. *)
Lemma b7_k6 : forall inp j, t_k inp j = 6 ->
  RcParse.cp_v (t_g inp j) 18 = 4 /\ RcParse.cp_v (t_g inp j) 19 = 3.
Proof.
  intros inp j H. unfold t_k in H. apply RcParse.ctrlparse_headamp in H as (_ & R & _).
  unfold RcParse.cp_rec in R. rewrite !andb_true_iff in R. destruct R as ((_ & R18) & R19).
  apply Z.eqb_eq in R18. apply Z.eqb_eq in R19. split; assumption.
Qed.

Lemma b7_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof. intros inp j. apply RcParse.ctrlparse_kind_range. Qed.

(* ---- The ports facts of C5.3-C5.8 (block = Φ + 18, pbs = its first 20 bytes) ---- *)

(* C5.3: reac_ports_parse and reac_ports_unknown accept the same blocks. *)
Lemma b7_decl_same : forall bs, RcLeaf.decl bs = RcPorts.pu_decl bs.
Proof. intros bs. reflexivity. Qed.

Lemma b7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_nunk_le : forall bs k, RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_cnt_range : forall f bs k, 0 <= RcLeaf.cnt f bs k <= Z.of_nat k.
Proof. intros f bs k. induction k as [|k IH]; cbn [RcLeaf.cnt]; [lia|]. destruct (f _); lia. Qed.

Lemma b7_rp_unk : forall inp j, t_rp inp j = 0 <-> 0 <= t_unk inp j.
Proof.
  intros inp j. unfold t_rp, t_unk. rewrite b7_decl_same.
  pose proof (b7_nunk_nonneg (t_pbs inp j) 12).
  destruct (RcPorts.pu_decl (t_pbs inp j)); split; intros; lia.
Qed.

Lemma b7_rp_cases : forall inp j, t_rp inp j = 0 \/ t_rp inp j = -1.
Proof. intros inp j. unfold t_rp. destruct (RcLeaf.decl _); [left|right]; reflexivity. Qed.

(* C5.6: every code is in exactly one of {00, 02}, {01}, {03}, >= 4. *)
Lemma b7_codes_sum : forall bs k,
  RcLeaf.cnt RcLeaf.is_in bs k + RcLeaf.cnt RcLeaf.is_out bs k + RcLeaf.cnt is_empty bs k +
  RcPorts.pu_nunk bs k = Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcLeaf.cnt RcPorts.pu_nunk]; [reflexivity|].
  unfold RcPorts.rc_u8. fold (RcLeaf.bt bs (8 + k)).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcLeaf.bt.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  assert (E : (if RcLeaf.is_in c then 1 else 0) + (if RcLeaf.is_out c then 1 else 0) +
              (if is_empty c then 1 else 0) + (if 4 <=? c then 1 else 0) = 1).
  { unfold RcLeaf.is_in, RcLeaf.is_out, is_empty.
    destruct (Z.eqb_spec c 0); destruct (Z.eqb_spec c 1); destruct (Z.eqb_spec c 2); destruct (Z.eqb_spec c 3);
      destruct (Z.leb_spec 4 c); cbn [orb]; lia. }
  lia.
Qed.

Lemma b7_unk_rp0 : forall inp j, t_rp inp j = 0 -> 0 <= t_unk inp j <= 48 /\ RcPorts.pu_decl (t_pbs inp j) = true.
Proof.
  intros inp j H. unfold t_rp, t_unk in *. rewrite <- b7_decl_same.
  destruct (RcLeaf.decl (t_pbs inp j)); [|discriminate H].
  pose proof (b7_nunk_nonneg (t_pbs inp j) 12). pose proof (b7_nunk_le (t_pbs inp j) 12).
  change (Z.of_nat 12) with 12 in *. split; [lia | reflexivity].
Qed.

Lemma b7_unk_rpm : forall inp j, t_rp inp j <> 0 -> t_rp inp j = -1 /\ t_unk inp j = -1.
Proof.
  intros inp j H. unfold t_rp, t_unk in *.
  change (RcPorts.pu_decl (t_pbs inp j)) with (RcLeaf.decl (t_pbs inp j)).
  destruct (RcLeaf.decl (t_pbs inp j)); [exfalso; apply H; reflexivity | split; reflexivity].
Qed.

(* C5.5 / C5.7: the first unknown code is 0 exactly when there is none, and is a byte. *)
Lemma b7_first_spec : forall bs k,
  (RcPorts.pu_first bs k = 0 <-> RcPorts.pu_nunk bs k = 0) /\ 0 <= RcPorts.pu_first bs k < 256.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_first RcPorts.pu_nunk]; [lia|].
  pose proof (b7_nunk_nonneg bs k).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcPorts.rc_u8.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  destruct IH as [IH1 IH2].
  destruct (Z.eqb_spec (RcPorts.pu_nunk bs k) 0); destruct (Z.leb_spec 4 c); cbn [andb]; lia.
Qed.

(* C5.8: headamp_base reads blk[7] = Φ[25]. *)
Lemma b7_pbs_bt : forall inp j k, (k < 20)%nat ->
  nth k (t_pbs inp j) (Z_to_bv 8 0) = nth (18 + k) (t_g inp j) (Z_to_bv 8 0).
Proof.
  intros inp j k Hk. unfold t_pbs, RcFrag.bsl. change (Z.to_nat 20) with 20%nat. change (Z.to_nat 18) with 18%nat.
  rewrite nth_firstn. replace (k <? 20)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. reflexivity.
Qed.

Lemma b7_pbs_length : forall inp j, length (t_pbs inp j) = 20%nat.
Proof. intros inp j. unfold t_pbs. rewrite b7_bsl_length, b7_g_length. reflexivity. Qed.

Lemma b7_pbs_bytes : forall m phi inp j, bytes_at rsegs m phi (t_g inp j) ->
  bytes_at rsegs m (phi + 18) (t_pbs inp j).
Proof.
  intros m phi inp j H. unfold t_pbs, RcFrag.bsl.
  exact (b7_bytes_sub m phi (t_g inp j) 18 20 H ltac:(rewrite b7_g_length; lia)).
Qed.

(* ---- Memory transport across a segment's run ---- *)

(* MT W m m': every byte fact of m apart from the window W holds in m'. *)
Definition MT (W : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a bs, bytes_at rsegs m a bs -> disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.

Lemma b7_mt : forall W mem m0' m', ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0' ->
  mem_rel rsegs m' m0' -> MT W mem m'.
Proof.
  intros W mem m0' m' HMI MU Hrel a bs H D.
  apply (proj2 (bytes_at_rel rsegs m' m0' a bs Hrel)).
  eapply Frame.bytes_at_transport; [|exact MU|exact D].
  exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H).
Qed.

(* A byte fact of the final memory of the evt run, read back in m'. *)
Lemma b7_back : forall m' m0' a bs, mem_rel rsegs m' m0' -> bytes_at rsegs m0' a bs -> bytes_at rsegs m' a bs.
Proof. intros m' m0' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0' a bs Hrel) H). Qed.

Lemma b7_norm : forall mem a bs, ro_agree rsegs mem -> bytes_at rsegs mem a bs ->
  bytes_at rsegs (normalize rsegs mem) a bs.
Proof.
  intros mem a bs HMI H. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H).
Qed.

Lemma b7_mt_q64 : forall W m m' a v, MT W m m' -> q64 m a v -> disjoint_from W a 8 -> q64 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. rewrite length_le8. exact D. Qed.

Lemma b7_mt_u32 : forall W m m' a v, MT W m m' -> u32 m a v -> disjoint_from W a 4 -> u32 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. rewrite length_le4. exact D. Qed.

Lemma b7_mt_b8 : forall W m m' a v, MT W m m' -> b8 m a v -> disjoint_from W a 1 -> b8 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. exact D. Qed.

(* The footprint of EQ's byte facts: Φ (heap), [sp+8, sp+192) (M7, have, type_filler, the body pointer at sp+32,
   first's body at sp+40, our, frag, id) and the parse result [sp+1752, sp+1788). *)
Definition DJE (g : ghost) (j : nat) (phi : Z) (W : list (Z * Z)) : Prop :=
  forall a n, 0 <= n ->
    (phi <= a /\ a + n <= phi + t_len (g_in g) j) \/ (spk g 8 <= a /\ a + n <= spk g 192) \/
    (spk g 1752 <= a /\ a + n <= spk g 1788) -> disjoint_from W a n.

(* The ports slots [sp+1688, sp+1700) (DJP), and with them the byte first at sp+1792 (DJQ). *)
Definition DJP (g : ghost) (W : list (Z * Z)) : Prop :=
  disjoint_from W (spk g 1688) 4 /\ disjoint_from W (spk g 1692) 4 /\ disjoint_from W (spk g 1696) 4.
Definition DJQ (g : ghost) (W : list (Z * Z)) : Prop := DJP g W /\ disjoint_from W (spk g 1792) 1.

Definition EQR (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
  getr regs' 23 = getr regs 23 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma b7_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. intros regs regs' r v E H. unfold rg in *. rewrite E. exact H. Qed.

Lemma b7_EQ : forall g j phi regs m regs' m' W,
  EQ g j phi regs m -> MT W m m' -> DJE g j phi W -> EQR regs regs' -> EQ g j phi regs' m'.
Proof.
  intros g j phi regs m regs' m' W (HFT & H7 & H2 & HVC & HIFS & H88) HM DJ
    (E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27).
  destruct HFT as (Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7).
  destruct HVC as (H22 & H24 & HB).
  destruct HIFS as ((HID & Hidok) & (HFG & Hfok) & (F16 & F19 & F40 & FL & HFI)).
  pose proof (b7_len_nonneg (g_in g) (fc (g_in g) j)) as Hl. fold (t_len (g_in g) j) in Hl.
  pose proof (b7_nb_range (g_in g) (S j)) as Hnb.
  unfold spk in DJ.
  split; [split; [exact Hj|]; split; [exact (b7_rg _ _ _ _ E26 H26)|]; split|].
  { split; [exact (b7_rg _ _ _ _ E27 H27)|].
    split; [apply (b7_mt_q64 W m m'); [exact HM | exact H32 | apply DJ; unfold spk; lia]|].
    exact (b7_rg _ _ _ _ E20 H20). }
  { split; [exact (b7_rg _ _ _ _ E21 H21)|]. split.
    - apply HM; [exact Hphi|]. rewrite b7_len_phi. apply DJ; lia.
    - split.
      + apply HM; [exact HOUR|]. rewrite OUR_length. apply DJ; unfold spk; lia.
      + apply (b7_mt_q64 W m m'); [exact HM | exact HM7 | apply DJ; unfold spk; lia]. }
  split; [exact (b7_rg _ _ _ _ E23 H7)|]. split; [exact (b7_rg _ _ _ _ E18 H2)|].
  split.
  { split; [exact (b7_rg _ _ _ _ E22 H22)|].
    split; [apply (b7_mt_q64 W m m'); [exact HM | exact H24 | apply DJ; unfold spk; lia]|].
    apply HM; [exact HB|]. unfold t_B. rewrite RcParse.ctrlparse_length. apply DJ; unfold spk; lia. }
  split; [|exact H88].
  split; [split; [|exact Hidok]|split; [split; [|exact Hfok]|]].
  - apply HM; [exact HID|]. rewrite b7_ID_length. apply DJ; unfold spk; lia.
  - apply HM; [exact HFG|]. rewrite b7_FG_length. apply DJ; unfold spk; lia.
  - split; [apply (b7_mt_q64 W m m'); [exact HM | exact F16 | apply DJ; unfold spk; lia]|].
    split; [exact (b7_rg _ _ _ _ E19 F19)|].
    split; [apply HM; [exact F40 | apply DJ; unfold spk; lia]|].
    split; [exact FL | exact HFI].
Qed.

Lemma b7_PORTS : forall g j m m' W, PORTS g j m -> MT W m m' -> DJP g W -> PORTS g j m'.
Proof.
  intros g j m m' W (P0 & P1) HM (D0 & D1 & D2).
  split.
  - intros E. destruct (P0 E) as (A0 & A1 & A2).
    split; [exact (b7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (b7_mt_u32 W m m' _ _ HM A1 D1) | exact (b7_mt_u32 W m m' _ _ HM A2 D2)].
  - intros E. destruct (P1 E) as (A0 & A1 & A2).
    split; [exact (b7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (b7_mt_u32 W m m' _ _ HM A1 D1) | exact (b7_mt_u32 W m m' _ _ HM A2 D2)].
Qed.

Lemma b7_QB : forall g j phi regs m regs' m' W,
  QB g j phi regs m -> MT W m m' -> DJE g j phi W -> DJQ g W -> EQR regs regs' ->
  getr regs' 25 = getr regs 25 -> QB g j phi regs' m'.
Proof.
  intros g j phi regs m regs' m' W (HEQ & H25 & HP & H1792) HM DJ (DP & D) ER E25.
  split; [exact (b7_EQ g j phi regs m regs' m' W HEQ HM DJ ER)|].
  split; [exact (b7_rg _ _ _ _ E25 H25)|].
  split; [exact (b7_PORTS g j m m' W HP HM DP)|].
  exact (b7_mt_b8 W m m' _ _ HM H1792 D).
Qed.

Lemma b7_DJE_nil : forall g j phi, DJE g j phi [].
Proof. intros g j phi a n _ _. exact I. Qed.

Lemma b7_DJQ_nil : forall g, DJQ g [].
Proof. intros g. repeat split. Qed.

(* ---- Φ's block: below alloc_ceiling ---- *)

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma b7_phi_bnd : forall g hb L A regs mem md phi len,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb1 phi len ++ blocks (g_L g) (g_A g)) -> 0 < len ->
  4096 <= phi /\ phi + len <= alloc_ceiling.
Proof.
  intros g hb L A regs mem md phi len HFR HP Hlen.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (phi, len) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity. }
  apply blocks_In in Hin as (p & Hp & Hpin). subst phi.
  destruct (mr_blocks B (aa_MR (APIf rc)) (aa_laws (APIf rc)) L A mem md p len 0 HM Hpin ltac:(lia))
    as (_ & H1 & H2 & _).
  lia.
Qed.

Lemma b7_S_bnd : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  alloc_ceiling + 65536 <= g_S g /\ g_S g <= 2 ^ 47 /\ g_S g mod 16 = 0 /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ ro_agree rsegs mem.
Proof.
  intros g hb L A regs mem md HFR.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  destruct (sl_fr_bnd B APIf ra empty FF g hb L A regs mem md HFR) as (E2 & _ & _ & _ & HMI).
  unfold SLOT_K, SLOT_STACK in HSK.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact E2 | exact HMI].
Qed.

End S.

(* The register map, pc and memory of an MS equation, without injection's normalization of the terms. *)
Lemma b7_MS_inj : forall R F pc fc rv m ro R' F' pc' fc' rv' m' ro',
  MState.MS R F pc fc rv m ro = MState.MS R' F' pc' fc' rv' m' ro' -> R = R' /\ pc = pc' /\ m = m'.
Proof. intros R F pc fc rv m ro R' F' pc' fc' rv' m' ro' H. unfold MState.MS in H. inversion H. auto. Qed.

(* A boolean fact checked for every byte value. *)
Lemma b7_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall u, 0 <= u < 256 -> P u = true.
Proof.
  intros P H u Hu. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat u).
  split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma b7_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite MState.unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity | change (bv_half_modulus 32) with (2 ^ 31); lia].
Qed.

Lemma b7_land4 : forall x, 0 <= x -> Z.land (4 * x) 3 = 0.
Proof.
  intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* ---- Branch conditions ---- *)

Lemma b7_eqb : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 =? y mod 2 ^ 64).
Proof. intros x y. unfold bv_eqb. rewrite !MState.unsigned_lit_wrap. reflexivity. Qed.

Lemma b7_eqb_small : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. rewrite b7_eqb, !Z.mod_small by lia. reflexivity. Qed.

Lemma b7_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma b7_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  exact R.
Qed.

(* Replace the condition of the branch at the head of the goal by its value. *)
Ltac b7_br v pf :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (symmetry; pf); cbv iota
  end.

Ltac b7_zdec :=
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  end; cbn [negb andb orb]; first [reflexivity | exfalso; lia].
