(* Helpers for the segment lemmas of batch u7 (Q01-Q06) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0):
   the frame-turn model (Φ's length, t_g, ID/FG lengths), the check_ports model facts (CNT: the code counts and the
   first unknown code), the transport of the is_8819 / check_ports bundles (EQ, PORTS, QB) across a run, u7_mid
   (sl_mid with a fixed write set whose munch reaches the continuation) and branch-condition tactics. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcIdentModel RcFrag RcLeaf RcPorts RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- The frame-turn model: Φ's length, t_g = the first 50 bytes of Φ ---- *)

Lemma u7_bat_nonneg : forall bs i, 0 <= RcFrag.bat bs i.
Proof.
  intros bs i. unfold RcFrag.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia.
Qed.

Lemma u7_inb_nonneg : forall inp k, 0 <= inb inp k.
Proof.
  intros inp k. unfold inb, RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb inp (Z.to_nat k))).
  lia.
Qed.

Lemma u7_len_nonneg : forall inp c, 0 <= f_len inp c.
Proof.
  intros inp c. unfold f_len, f_L, f_h. pose proof (u7_inb_nonneg inp c). pose proof (u7_inb_nonneg inp (c + 1)).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma u7_fc_nonneg : forall inp j, 0 <= fc inp j.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - unfold f_next, f_body, f_h, f_left. pose proof (u7_len_nonneg inp (fc inp j)). unfold nlen in *. lia.
Qed.

Lemma u7_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. unfold t_phi, t_len, f_phi.
  pose proof (u7_fc_nonneg inp j) as Hc. pose proof (u7_len_nonneg inp (fc inp j)) as Hl.
  set (c := fc inp j) in *.
  assert (Hle : f_len inp c <= f_left inp c - f_h inp c) by (unfold f_len; lia).
  unfold f_body, f_h, f_left, nlen in *.
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma u7_len_phi : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof.
  intros inp j. rewrite u7_phi_length. pose proof (u7_len_nonneg inp (fc inp j)). unfold t_len. lia.
Qed.

Lemma u7_g_firstn : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. unfold t_g, fr50. rewrite firstn_app.
  replace (50 - length (t_phi inp j))%nat with 0%nat by (rewrite u7_phi_length; lia).
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma u7_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply (proj1 (bytes_at_app rsegs m a _ _)) in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply (proj1 (bytes_at_app rsegs m _ _ _)) in H as [H _].
  exact H.
Qed.

Lemma u7_g_bytes : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H Hl. rewrite (u7_g_firstn inp j Hl).
  pose proof (u7_bytes_sub m phi (t_phi inp j) 0 50 H ltac:(rewrite u7_phi_length; lia)) as H'.
  rewrite Z.add_0_r in H'. exact H'.
Qed.

Lemma u7_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

Lemma u7_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* One byte of a bytes_at as the read the step tactic consumes. *)
Lemma u7_rd1 : forall m a bs k d, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [nth k bs d].
Proof.
  intros m a bs k d H Hk. pose proof (bytes_at_read rsegs m a bs (Z.of_nat k) 1 H ltac:(lia) ltac:(lia)) as R.
  rewrite Nat2Z.id in R. rewrite (u7_firstn1 bs k d Hk) in R. exact R.
Qed.

Lemma u7_rdn : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

(* ID_j has 38 bytes and FG_j 72 at every turn. *)
Lemma u7_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
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

Lemma u7_bsl_length : forall bs k n, length (RcFrag.bsl bs k n) = Nat.min (Z.to_nat n) (length bs - Z.to_nat k).
Proof. intros bs k n. unfold RcFrag.bsl. rewrite length_firstn, length_skipn. reflexivity. Qed.

Lemma u7_fg_st_length : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  pose proof (u7_bat_nonneg st 7) as Hlf.
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|cbn [fg_next]; exact Hs].
  unfold RcFrag.fg_fr in Efr. rewrite !andb_true_iff in Efr.
  destruct Efr as (((((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & N1) & N22) & _).
  apply Z.leb_le in N1. apply Z.leb_le in N22.
  assert (Lb : length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g)).
  { unfold RcFrag.fg_body. rewrite u7_bsl_length. lia. }
  assert (Lc : forall s, length s = 72%nat -> length (RcFrag.fg_clear s) = 72%nat).
  { intros s Hs'. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first. rewrite !length_app, length_skipn, u7_bsl_length, Lb. cbn [length].
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

Lemma u7_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    assert (E : length (fg_st (t_len inp j) (fs_fg (fst_at inp j)) (t_g inp j)) = 72%nat)
      by (apply u7_fg_st_length; [exact IH | apply u7_g_length]).
    destruct (f_opens (t_len inp j) (t_g inp j)); exact E.
Qed.

Lemma u7_big_8819 : forall inp j, t_8819 inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_8819, t_big in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Z.leb_le. exact H.
Qed.

Lemma u7_big_true : forall inp j, t_8819 inp j = true -> t_big inp j = true.
Proof. intros inp j H. unfold t_big. apply Z.leb_le. exact (u7_big_8819 inp j H). Qed.

(* ---- The check_ports facts (CNT; C5.3-C5.8: block = Φ + 18, pbs = its first 20 bytes) ---- *)

Lemma u7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma u7_nunk_le : forall bs k, RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma u7_cnt_range : forall f bs k, 0 <= RcLeaf.cnt f bs k <= Z.of_nat k.
Proof. intros f bs k. induction k as [|k IH]; cbn [RcLeaf.cnt]; [lia|]. destruct (f _); lia. Qed.

Lemma u7_rp_unk : forall inp j, t_rp inp j = 0 <-> 0 <= t_unk inp j.
Proof.
  intros inp j. unfold t_rp, t_unk. change (RcLeaf.decl (t_pbs inp j)) with (RcPorts.pu_decl (t_pbs inp j)).
  pose proof (u7_nunk_nonneg (t_pbs inp j) 12).
  destruct (RcPorts.pu_decl (t_pbs inp j)); split; intros; lia.
Qed.

Lemma u7_rp_cases : forall inp j, t_rp inp j = 0 \/ t_rp inp j = -1.
Proof. intros inp j. unfold t_rp. destruct (RcLeaf.decl _); [left|right]; reflexivity. Qed.

Lemma u7_unk_range : forall inp j, t_unk inp j = -1 \/ (0 <= t_unk inp j <= 48 /\ t_unk inp j mod 4 = 0).
Proof.
  intros inp j. unfold t_unk. destruct (RcPorts.pu_decl _); [right|left; reflexivity].
  pose proof (u7_nunk_nonneg (t_pbs inp j) 12). pose proof (u7_nunk_le (t_pbs inp j) 12).
  try change (Z.of_nat 12) with 12 in *.
  split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* rp = 0: the unknown count, as reac_ports_unknown returns it, and the first unknown code. *)
Lemma u7_unk_rp0 : forall inp j, t_rp inp j = 0 ->
  t_unk inp j = 4 * RcPorts.pu_nunk (t_pbs inp j) 12 /\ t_first inp j = RcPorts.pu_first (t_pbs inp j) 12.
Proof.
  intros inp j H. unfold t_rp in H. unfold t_unk, t_first.
  change (RcLeaf.decl (t_pbs inp j)) with (RcPorts.pu_decl (t_pbs inp j)) in H.
  destruct (RcPorts.pu_decl (t_pbs inp j)); [split; reflexivity | discriminate].
Qed.

(* C5.6: every code is in exactly one of {00, 02}, {01}, {03}, >= 4. *)
Lemma u7_codes_sum : forall bs k,
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

(* C5.5 / C5.7: the first unknown code is 0 exactly when there is none, and is a byte. *)
Lemma u7_first_spec : forall bs k,
  (RcPorts.pu_first bs k = 0 <-> RcPorts.pu_nunk bs k = 0) /\ 0 <= RcPorts.pu_first bs k < 256.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_first RcPorts.pu_nunk]; [lia|].
  pose proof (u7_nunk_nonneg bs k).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcPorts.rc_u8.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  destruct IH as [IH1 IH2].
  destruct (Z.eqb_spec (RcPorts.pu_nunk bs k) 0); destruct (Z.leb_spec 4 c); cbn [andb]; lia.
Qed.

Lemma u7_pbs_length : forall inp j, length (t_pbs inp j) = 20%nat.
Proof. intros inp j. unfold t_pbs. rewrite u7_bsl_length, u7_g_length. reflexivity. Qed.

Lemma u7_pbs_bytes : forall m phi inp j, bytes_at rsegs m phi (t_g inp j) ->
  bytes_at rsegs m (phi + 18) (t_pbs inp j).
Proof.
  intros m phi inp j H. unfold t_pbs, RcFrag.bsl.
  exact (u7_bytes_sub m phi (t_g inp j) 18 20 H ltac:(rewrite u7_g_length; lia)).
Qed.

(* n (the FIRST body's length, FSb's `first`) is a byte at every turn. *)
Lemma u7_bat_range : forall bs i, 0 <= RcFrag.bat bs i < 256.
Proof.
  intros bs i. unfold RcFrag.bat.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma u7_fs_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 255.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_nb]. lia.
  - rewrite fst_at_S. unfold turn. destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_nb];
      [pose proof (u7_bat_range (t_g inp j) 26); lia | exact IH].
Qed.

(* ---- Memory transport across a segment's run ---- *)

(* MT W m m': every byte fact of m apart from the window W holds in m'. *)
Definition MT (W : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a bs, bytes_at rsegs m a bs -> disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.

Lemma u7_mt : forall W m m', Frame.munch W m m' -> MT W m m'.
Proof. intros W m m' MU a bs H D. exact (bytes_at_transport rsegs W m m' a bs H MU D). Qed.

Lemma u7_back : forall m' m0' a bs, mem_rel rsegs m' m0' -> bytes_at rsegs m0' a bs -> bytes_at rsegs m' a bs.
Proof. intros m' m0' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0' a bs Hrel) H). Qed.

Lemma u7_norm : forall mem a bs, ro_agree rsegs mem -> bytes_at rsegs mem a bs ->
  bytes_at rsegs (normalize rsegs mem) a bs.
Proof.
  intros mem a bs HMI H.
  exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H).
Qed.

Lemma u7_mt_q64 : forall W m m' a v, MT W m m' -> q64 m a v -> disjoint_from W a 8 -> q64 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. rewrite length_le8. exact D. Qed.

Lemma u7_mt_u32 : forall W m m' a v, MT W m m' -> u32 m a v -> disjoint_from W a 4 -> u32 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. rewrite length_le4. exact D. Qed.

Lemma u7_mt_b8 : forall W m m' a v, MT W m m' -> b8 m a v -> disjoint_from W a 1 -> b8 m' a v.
Proof. intros W m m' a v H Q D. apply H; [exact Q|]. exact D. Qed.

(* The footprint of EQ's byte facts: Φ (heap), [sp+8, sp+297) (M7 sp+8, TF sp+16, left - h sp+24, `first`
   sp+36 .. 41 + n with n <= 255, id sp+76, our sp+114, frag sp+120) and the parse result [sp+1752, sp+1788). *)
Definition DJE (g : ghost) (j : nat) (phi : Z) (W : list (Z * Z)) : Prop :=
  forall a n, 0 <= n ->
    (phi <= a /\ a + n <= phi + t_len (g_in g) j) \/ (spk g 8 <= a /\ a + n <= spk g 297) \/
    (spk g 1752 <= a /\ a + n <= spk g 1788) -> disjoint_from W a n.

(* The ports slots [sp+1688, sp+1700) and the byte first at sp+1792. *)
Definition DJQ (g : ghost) (W : list (Z * Z)) : Prop :=
  disjoint_from W (spk g 1688) 4 /\ disjoint_from W (spk g 1692) 4 /\ disjoint_from W (spk g 1696) 4 /\
  disjoint_from W (spk g 1792) 1.

(* EQ's registers: s0 (8, OVF), s1 (9, j), s2 (18), s4-s9 (20-25). *)
Definition EQR (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
  getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25.

Lemma u7_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. intros regs regs' r v E H. unfold rg in *. rewrite E. exact H. Qed.

Lemma u7_EQ : forall g j phi regs m regs' m' W,
  EQ g j phi regs m -> MT W m m' -> DJE g j phi W -> EQR regs regs' -> EQ g j phi regs' m'.
Proof.
  intros g j phi regs m regs' m' W (HFT & H7 & H2 & HVC & HIFS & H88) HM DJ
    (E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25).
  destruct HFT as ((Hj & H9 & HOUR & HM7 & HOVF & HS2) & (HLH & H21 & H22) & H23 & Hphi & H18).
  destruct HVC as (H24 & H16 & HB).
  destruct HIFS as ((HID & Hidok) & (HFG & Hfok) & (F36 & F40 & FB & FL & HFI)).
  pose proof (u7_len_nonneg (g_in g) (fc (g_in g) j)) as Hl. fold (t_len (g_in g) j) in Hl.
  pose proof (u7_fs_nb_range (g_in g) (S j)) as Hnb.
  assert (Q8 : forall a v, q64 m (spk g a) v -> 8 <= a -> a + 8 <= 297 -> q64 m' (spk g a) v).
  { intros a v Hq Hq1 Hq2. apply (u7_mt_q64 W m m'); [exact HM | exact Hq | apply DJ; unfold spk in *; lia]. }
  assert (U4 : forall a v, u32 m (spk g a) v -> 8 <= a -> a + 4 <= 297 -> u32 m' (spk g a) v).
  { intros a v Hq Hq1 Hq2. apply (u7_mt_u32 W m m'); [exact HM | exact Hq | apply DJ; unfold spk in *; lia]. }
  assert (B1 : forall a v, b8 m (spk g a) v -> 8 <= a -> a + 1 <= 297 -> b8 m' (spk g a) v).
  { intros a v Hq Hq1 Hq2. apply (u7_mt_b8 W m m'); [exact HM | exact Hq | apply DJ; unfold spk in *; lia]. }
  assert (A_body : bytes_at rsegs m' (spk g 41) (fs_body (fst_at (g_in g) (S j)))).
  { apply HM; [exact FB|]. rewrite FL. apply DJ; unfold spk in *; lia. }
  assert (A_OUR : OURb g m').
  { apply HM; [exact HOUR|]. rewrite OUR_length. apply DJ; unfold spk; lia. }
  assert (A_phi : bytes_at rsegs m' phi (t_phi (g_in g) j)).
  { apply HM; [exact Hphi|]. rewrite u7_len_phi. apply DJ; lia. }
  assert (A_B : bytes_at rsegs m' (spk g 1752) (t_B (g_in g) j)).
  { apply HM; [exact HB|]. unfold t_B. rewrite RcParse.ctrlparse_length. apply DJ; unfold spk; lia. }
  assert (A_ID : IDB g m' (t_ID (g_in g) (S j))).
  { apply HM; [exact HID|]. rewrite u7_ID_length. apply DJ; unfold spk; lia. }
  assert (A_FG : FGB g m' (t_FG (g_in g) (S j))).
  { apply HM; [exact HFG|]. rewrite u7_FG_length. apply DJ; unfold spk; lia. }
  exact (conj (conj (conj Hj (conj (u7_rg _ _ _ _ E9 H9) (conj A_OUR (conj (Q8 8 _ HM7 ltac:(lia) ltac:(lia))
                (conj (u7_rg _ _ _ _ E8 HOVF) (u7_rg _ _ _ _ E18 HS2))))))
             (conj (conj (Q8 24 _ HLH ltac:(lia) ltac:(lia)) (conj (u7_rg _ _ _ _ E21 H21) (u7_rg _ _ _ _ E22 H22)))
               (conj (u7_rg _ _ _ _ E23 H23) (conj A_phi (u7_rg _ _ _ _ E18 H18)))))
          (conj (u7_rg _ _ _ _ E25 H7) (conj (u7_rg _ _ _ _ E20 H2)
            (conj (conj (u7_rg _ _ _ _ E24 H24) (conj (Q8 16 _ H16 ltac:(lia) ltac:(lia)) A_B))
              (conj (conj (conj A_ID Hidok) (conj (conj A_FG Hfok)
                       (conj (U4 36 _ F36 ltac:(lia) ltac:(lia))
                         (conj (B1 40 _ F40 ltac:(lia) ltac:(lia)) (conj A_body (conj FL HFI))))))
                    H88))))).
Qed.

Lemma u7_PORTS : forall g j m m' W, PORTS g j m -> MT W m m' -> DJQ g W -> PORTS g j m'.
Proof.
  intros g j m m' W (P0 & P1) HM (D0 & D1 & D2 & _).
  split.
  - intros E. destruct (P0 E) as (A0 & A1 & A2).
    split; [exact (u7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (u7_mt_u32 W m m' _ _ HM A1 D1) | exact (u7_mt_u32 W m m' _ _ HM A2 D2)].
  - intros E. destruct (P1 E) as (A0 & A1 & A2).
    split; [exact (u7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (u7_mt_u32 W m m' _ _ HM A1 D1) | exact (u7_mt_u32 W m m' _ _ HM A2 D2)].
Qed.

Lemma u7_PORTS3 : forall g j m m' W, PORTS g j m -> MT W m m' ->
  disjoint_from W (spk g 1688) 4 -> disjoint_from W (spk g 1692) 4 -> disjoint_from W (spk g 1696) 4 ->
  PORTS g j m'.
Proof.
  intros g j m m' W (P0 & P1) HM D0 D1 D2.
  split.
  - intros E. destruct (P0 E) as (A0 & A1 & A2).
    split; [exact (u7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (u7_mt_u32 W m m' _ _ HM A1 D1) | exact (u7_mt_u32 W m m' _ _ HM A2 D2)].
  - intros E. destruct (P1 E) as (A0 & A1 & A2).
    split; [exact (u7_mt_u32 W m m' _ _ HM A0 D0)|].
    split; [exact (u7_mt_u32 W m m' _ _ HM A1 D1) | exact (u7_mt_u32 W m m' _ _ HM A2 D2)].
Qed.

Lemma u7_QB : forall g j phi regs m regs' m' W,
  QB g j phi regs m -> MT W m m' -> DJE g j phi W -> DJQ g W -> EQR regs regs' ->
  getr regs' 27 = getr regs 27 -> QB g j phi regs' m'.
Proof.
  intros g j phi regs m regs' m' W (HEQ & H27 & HP & H1792) HM DJ DQ ER E27.
  split; [exact (u7_EQ g j phi regs m regs' m' W HEQ HM DJ ER)|].
  split; [exact (u7_rg _ _ _ _ E27 H27)|].
  split; [exact (u7_PORTS g j m m' W HP HM DQ)|].
  destruct DQ as (_ & _ & _ & D). exact (u7_mt_b8 W m m' _ _ HM H1792 D).
Qed.

Lemma u7_EQ_CC : forall g j phi regs m, EQ g j phi regs m -> CC g j phi regs m.
Proof.
  intros g j phi regs m (HFT & H7 & H2 & HVC & HIFS & _).
  exact (conj (conj HFT (conj HVC HIFS)) (conj H2 H7)).
Qed.

Lemma u7_DJE_nil : forall g j phi, DJE g j phi [].
Proof. intros g j phi a n _ _. exact I. Qed.

Lemma u7_DJQ_nil : forall g, DJQ g [].
Proof. intros g. repeat split. Qed.

Lemma u7_munch_join : forall W W' m1 m2 m3, Frame.munch W m1 m2 -> Frame.munch W' m2 m3 ->
  (forall x, Frame.outside W x -> Frame.outside W' x) -> Frame.munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 Hs x Hx. rewrite (H2 x (Hs _ Hx)). exact (H1 x Hx). Qed.

(* A write set inside [S - K, S - 104), interval by interval. *)
Lemma u7_fp : forall g W x, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W x HF Hx. induction HF as [|[lo hi] W' [H1 H2] HF IH]; cbn [Frame.outside]; intros O.
  - exfalso; exact (O I).
  - cbn [fst snd] in *. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi).
    + lia.
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
Qed.

(* ---- Φ's block and the frame's bounds; u7_mid ---- *)

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma u7_phi_bnd : forall g hb L A regs mem md phi len,
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

Lemma u7_S_bnd : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
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

Lemma u7_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP).
    + exact MU'.
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

End S.

(* ---- Branch conditions and word values ---- *)

Lemma u7_eqb : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 =? y mod 2 ^ 64).
Proof. intros x y. unfold bv_eqb. rewrite !MState.unsigned_lit_wrap. reflexivity. Qed.

Lemma u7_eqb_small : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. rewrite u7_eqb, !Z.mod_small by lia. reflexivity. Qed.

Lemma u7_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  exact R.
Qed.

(* Replace the condition of the branch at the head of the goal by its value. *)
Ltac u7_br v pf :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (symmetry; pf); cbv iota
  end.

(* The registers, pc and memory of two equal machine states, without reducing either side. *)
Lemma u7_MS_inj : forall R R' F F' pc pc' fc fc' rv rv' m m' ro ro',
  MState.MS R F pc fc rv m ro = MState.MS R' F' pc' fc' rv' m' ro' -> R = R' /\ pc = pc' /\ m = m'.
Proof.
  intros R R' F F' pc pc' fc fc' rv rv' m m' ro ro' H.
  pose proof (f_equal ms_regs H) as E1. pose proof (f_equal ms_pc_val H) as E2. pose proof (f_equal ms_mem H) as E3.
  cbn in E1, E2, E3. split; [exact E1|]. split; [exact E2 | exact E3].
Qed.

Lemma u7_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma u7_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma u7_if_un : forall (c : bool) (x y : word), bv_unsigned (if c then x else y) = if c then bv_unsigned x else bv_unsigned y.
Proof. intros c x y. destruct c; reflexivity. Qed.

(* Words as Z: every bv_unsigned / bv_signed of a literal word and every 32-bit wrap as mod arithmetic. *)
Ltac u7_unf :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu, PropExec.c_eq, PropExec.c_ltu, PropExec.c_lts, PropExec.v_sltiu,
    PropExec.v_slti, PropExec.v_sltu, PropExec.v_slt, PropExec.zsig, sx32, zx8, zxb, PropExec.v_lw, PropExec.v_lb,
    bv_signed in *;
  rewrite ?u7_if_un in *;
  rewrite ?Z_to_bv_unsigned in *;
  unfold bv_swrap, bv_half_modulus in *; unfold bv_wrap, bv_modulus in *;
  try change (2 ^ Z.of_N 64) with 18446744073709551616 in *; try change (2 ^ Z.of_N 32) with 4294967296 in *;
  try change (2 ^ Z.of_N 8) with 256 in *;
  rewrite ?u7_land3, ?u7_land255 in *.

Ltac u7_noif t := lazymatch t with context [if _ then _ else _] => fail | _ => idtac end.

(* Case on every Z comparison of the goal, innermost first. *)
Ltac u7_split_ifs :=
  repeat (match goal with
          | |- context [?a =? ?b] => u7_noif a; u7_noif b; destruct (Z.eqb_spec a b)
          | |- context [?a <? ?b] => u7_noif a; u7_noif b; destruct (Z.ltb_spec a b)
          | |- context [?a <=? ?b] => u7_noif a; u7_noif b; destruct (Z.leb_spec a b)
          end; cbv beta iota delta [negb andb orb]).

Ltac u7_zdec := u7_split_ifs; first [reflexivity | exfalso; Z.div_mod_to_equations; lia].

(* The range of every word variable read in the goal. *)
Ltac u7_rng :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      is_var x;
      lazymatch goal with
      | _ : 0 <= bv_unsigned x < _ |- _ => fail
      | _ => let R := fresh "R" in pose proof (bv_unsigned_in_range 64 x) as R; unfold bv_modulus in R;
             change (2 ^ Z.of_N 64) with 18446744073709551616 in R
      end
  end.

(* A boolean branch condition, a word equation or a Z equation, from bounds on the Z values involved. *)
Ltac u7_bool := u7_rng; u7_unf; u7_zdec.
Ltac u7_weq := apply bv_eq; u7_rng; u7_unf; u7_split_ifs; Z.div_mod_to_equations; lia.
Ltac u7_zeq := u7_rng; u7_unf; u7_split_ifs; Z.div_mod_to_equations; lia.
