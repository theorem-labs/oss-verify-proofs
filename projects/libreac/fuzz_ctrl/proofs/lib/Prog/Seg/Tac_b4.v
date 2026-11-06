(* Helpers for the segment lemmas of batch b4 (P07-P09, F01-F06) of fuzz_ctrl LLVMFuzzerTestOneInput (plain):
   b4_mid (sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the continuation),
   b4_fp (a write set inside [S - K, S - 104)), the lengths of the P8 bundles and the transport of P0. *)
(* libreac v1.9.0 (SlotInv.v header): the bundles' bytes follow the v1.9.0 frame (M7 [sp+8, sp+16), have [sp+16,
   sp+24), type_filler [sp+24, sp+32), FC's body pointer [sp+32, sp+40), first's body [sp+40, sp+40 + nb) with
   nb <= 22 (b4_nb_range), our [sp+76, sp+82), frag [sp+82, sp+154), id [sp+154, sp+192)) and their registers (CUR
   s5 / s11, j s10, FC s11 / s4, FT's Φ s5, IFS's nb s3). b4_IFS_keep(2) take the registers; b4_LI_keep became
   b4_LIp_keep (K136d4's LIp, the only use: F01). rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* Branch conditions on literals. *)
Lemma b4_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b4_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* A 1-byte load from a byte cell. *)
Lemma b4_ld1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a [b] 0 1 H) by (cbn; lia).
  reflexivity.
Qed.

(* A sub-range of a byte run. *)
Lemma b4_ba_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma b4_firstn1 : forall (l : list byte) k, (k < length l)%nat ->
  firstn 1 (skipn k l) = [RcIdentModel.nthb l k].
Proof.
  intros l k Hk. unfold RcIdentModel.nthb. revert k Hk.
  induction l as [|x l IH]; intros [|k] Hk; cbn [skipn nth firstn length] in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

(* ---- Model facts of the frame loop ---- *)

Lemma b4_byte_nn : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma b4_fL_nn : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb, RcIdentModel.bz.
  pose proof (b4_byte_nn (RcIdentModel.nthb inp (Z.to_nat c))).
  pose proof (b4_byte_nn (RcIdentModel.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma b4_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. assert (Hn : 0 <= nlen inp) by (unfold nlen; lia).
  induction j as [|j IH]; cbn [fc].
  - unfold c0. lia.
  - pose proof (b4_fL_nn inp (fc inp j)). unfold f_next, f_body, f_len, f_h, f_left. lia.
Qed.

Lemma b4_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (b4_fc_range inp j). pose proof (b4_fL_nn inp (fc inp j)).
  unfold t_len, t_body, f_len, f_body, f_h, f_left. lia.
Qed.

Lemma b4_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (b4_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi. fold (t_len inp j). fold (t_body inp j).
  rewrite length_firstn, length_skipn. unfold nlen in H3. lia.
Qed.

Lemma b4_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

Lemma b4_tg_eq : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j Hb. unfold t_g, fr50. rewrite firstn_app, b4_phi_len.
  replace (50 - Z.to_nat (t_len inp j))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma b4_rpid_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id. destruct (RcReply.ir len g); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma b4_fgid_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma b4_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id];
    apply b4_fgid_len; apply b4_rpid_len; exact IH.
Qed.

Lemma b4_fgfr_n : forall len g, RcFrag.fg_fr len g = true -> 1 <= RcFrag.fg_n g <= 22.
Proof.
  intros len g H. unfold RcFrag.fg_fr in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
  end.
  lia.
Qed.

(* v1.9.0 `first`: nb (= the length of its body, FSb) is 0 or fg_n of an opening fragment, 1 .. 22. *)
Lemma b4_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 22.
Proof.
  intros inp j. induction j as [|j IH]; [cbn [fst_at fs0 fs_nb]; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo; cbn [fs_nb]; [|exact IH].
  unfold f_opens in Eo. apply andb_true_iff in Eo as [Efr _].
  pose proof (b4_fgfr_n _ _ Efr) as Hn. unfold RcFrag.fg_n in Hn. lia.
Qed.

Lemma b4_bat_nn : forall bs i, 0 <= RcFrag.bat bs i.
Proof. intros bs i. unfold RcFrag.bat. apply b4_byte_nn. Qed.

Lemma b4_body_len : forall g, length g = 50%nat -> 1 <= RcFrag.fg_n g <= 22 ->
  length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g).
Proof.
  intros g Hg Hn. unfold RcFrag.fg_body, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
Qed.

Lemma b4_clear_len : forall st, length st = 72%nat -> length (RcFrag.fg_clear st) = 72%nat.
Proof.
  intros st H. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn, H. reflexivity.
Qed.

Lemma b4_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fg_next, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  pose proof (b4_fgfr_n len g Efr) as Hn. pose proof (b4_body_len g Hg Hn) as Hb.
  destruct (RcFrag.bat g 19 =? 1); cbn [negb].
  - unfold RcFrag.fg_first, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hb, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb]; [|apply b4_clear_len; exact Hs].
    unfold RcFrag.fg_keep in Ek. apply andb_true_iff in Ek as [_ Ek]. apply Z.leb_le in Ek.
    pose proof (b4_bat_nn st 7) as H7. unfold RcFrag.fg_T, RcFrag.fg_lf in Ek.
    assert (Hj : length (RcFrag.fg_join st g) = 72%nat).
    { unfold RcFrag.fg_join, RcFrag.fg_T, RcFrag.fg_lf.
      rewrite !length_app, length_firstn, Hb, length_skipn, Hs. lia. }
    destruct (RcFrag.fg_close st g); cbn [negb]; apply b4_clear_len; exact Hj.
Qed.

Lemma b4_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg];
    (apply b4_fgst_len; [exact IH | apply b4_tg_len]).
Qed.

Lemma b4_len_OUR : forall inp, length (OUR inp) = 6%nat.
Proof. intros inp. unfold OUR. rewrite length_map, length_seq. reflexivity. Qed.

Lemma b4_len_ID0 : length RcIdentModel.ID0 = 38%nat.
Proof. reflexivity. Qed.

Lemma b4_len_z72 : length z72 = 72%nat.
Proof. reflexivity. Qed.

(* len_j fits the two length bytes. *)
Lemma b4_len_le : forall inp j, 0 <= t_len inp j <= 65535.
Proof.
  intros inp j. pose proof (b4_len_range inp j) as (H0 & _).
  unfold t_len, f_len, f_L, inb, RcIdentModel.bz in *.
  pose proof (b4_byte_nn (RcIdentModel.nthb inp (Z.to_nat (fc inp j)))).
  pose proof (b4_byte_nn (RcIdentModel.nthb inp (Z.to_nat (fc inp j + 1)))).
  destruct (2 <=? f_left inp (fc inp j)); lia.
Qed.

(* ---- Bytes a run leaves alone: b4_keep m m' lo hi ---- *)
Definition b4_keep (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> mbyte rsegs m' a = mbyte rsegs m a.

Lemma b4_ba_keep : forall m m' a bs lo hi, bytes_at rsegs m a bs -> b4_keep m m' lo hi ->
  lo <= a -> a + Z.of_nat (length bs) <= hi -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs lo hi H K H1 H2. apply (b1_ba_mbyte m m' a bs H). intros i Hi. apply K. lia.
Qed.

Lemma b4_keep_sub : forall m m' lo hi lo' hi', b4_keep m m' lo hi -> lo <= lo' -> hi' <= hi ->
  b4_keep m m' lo' hi'.
Proof. intros m m' lo hi lo' hi' K H1 H2 a Ha. apply K. lia. Qed.

Lemma b4_keep_munch : forall W m m' lo hi, Frame.munch W m m' -> Frame.disjoint_from W lo (hi - lo) ->
  0 <= lo -> hi <= 2 ^ 64 -> b4_keep m m' lo hi.
Proof.
  intros W m m' lo hi MU HD H1 H2 a Ha. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  rewrite MState.unsigned_lit by lia.
  clear MU. induction W as [|[l h] W IH]; cbn [Frame.outside disjoint_from] in *; [exact I|].
  destruct HD as [HD1 HD]. split; [lia | exact (IH HD)].
Qed.

Lemma b4_keep_trans : forall m1 m2 m3 lo hi, b4_keep m1 m2 lo hi -> b4_keep m2 m3 lo hi -> b4_keep m1 m3 lo hi.
Proof. intros m1 m2 m3 lo hi K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.

(* The frame-loop bundles across a run that keeps their bytes and s3: have at [sp+16, sp+24), first's body and frag
   and id in [sp+40, sp+192) (the body is at most 22 bytes, b4_nb_range). *)
Lemma b4_IFS_keep2 : forall g j regs regs' m m', b4_keep m m' (spk g 16) (spk g 24) ->
  b4_keep m m' (spk g 40) (spk g 192) -> getr regs' 19 = getr regs 19 -> IFS g j regs m -> IFS g j regs' m'.
Proof.
  intros g j regs regs' m m' K1 K2 E19 ((HID & Hok) & (HFG & Hfok) & (H16 & H19 & H40 & HL & HFI)).
  unfold IFS, IDj, FGj, FSj, IDb, FGb, FSb, IDB, FGB, q64, rg in *.
  pose proof (b4_tID_len (g_in g) j) as L1. pose proof (b4_tFG_len (g_in g) j) as L2.
  pose proof (b4_nb_range (g_in g) j) as L3.
  rewrite E19.
  refine (conj (conj _ Hok) (conj (conj _ Hfok) (conj _ (conj H19 (conj _ (conj HL HFI)))))).
  all: first [ eapply b4_ba_keep; [eassumption | exact K1 | unfold spk; lia
                                   | rewrite ?length_le8, ?L1, ?L2; unfold spk; lia]
             | eapply b4_ba_keep; [eassumption | exact K2 | unfold spk; lia
                                   | rewrite ?length_le8, ?L1, ?L2; unfold spk; lia] ].
Qed.

Lemma b4_IFS_keep : forall g j regs regs' m m', b4_keep m m' (spk g 16) (spk g 192) ->
  getr regs' 19 = getr regs 19 -> IFS g j regs m -> IFS g j regs' m'.
Proof.
  intros g j regs regs' m m' K. apply b4_IFS_keep2; (eapply b4_keep_sub; [exact K | unfold spk; lia | unfold spk; lia]).
Qed.

(* struct P2.1: a frame shorter than 50 bytes parses to kind 0 and 36 zero bytes; nothing of turn j's check
   values holds. *)
Lemma b4_small : forall inp j, t_len inp j < 50 ->
  t_big inp j = false /\ t_sum_ok inp j = false /\ t_8819 inp j = false /\ t_TF inp j = false /\
  t_k inp j = 0 /\ t_B inp j = repeat RcParse.cp_z 36.
Proof.
  intros inp j H.
  unfold t_TF, t_tfill, t_sum_ok, t_8819, t_big, t_k, t_B, RcParse.ctrlparse, RcParse.cp_hdr.
  rewrite (proj2 (Z.leb_gt 50 (t_len inp j)) H).
  repeat split; reflexivity.
Qed.

(* struct P5.1: k_j = 0 exactly when the frame is not is_8819. *)
Lemma b4_P51 : forall inp j, t_k inp j = 0 <-> t_8819 inp j = false.
Proof.
  intros inp j. unfold t_k, t_8819, t_big. rewrite RcParse.ctrlparse_none.
  destruct (Z.leb_spec 50 (t_len inp j)); destruct (Z.eqb_spec (RcParse.cp_v (t_g inp j) 12) 0x88);
    destruct (Z.eqb_spec (RcParse.cp_v (t_g inp j) 13) 0x19); cbn [andb]; split; intros HH;
    first [ reflexivity | discriminate | (exfalso; apply HH; repeat split; assumption)
          | (intros (Ha & Hb & Hc); lia) ].
Qed.


Lemma b4_OUR_keep : forall g m m', b4_keep m m' (spk g 76) (spk g 82) -> OURb g m -> OURb g m'.
Proof.
  intros g m m' K H. unfold OURb in *.
  eapply b4_ba_keep; [exact H | exact K | lia | rewrite b4_len_OUR; unfold spk; lia].
Qed.

Lemma b4_M7_keep : forall g m m', b4_keep m m' (spk g 8) (spk g 16) -> M7 g m -> M7 g m'.
Proof.
  intros g m m' K H. unfold M7, q64 in *.
  eapply b4_ba_keep; [exact H | exact K | lia | rewrite length_le8; unfold spk; lia].
Qed.

(* LI at K13694 to LIp at K136d4 (v1.9.0 overwrites the length register s11 in between): the cursor pointer s5, j in
   s10 and nb in s3 kept, the bytes [sp+8, sp+192) kept. *)
Lemma b4_LIp_keep : forall g j regs regs' m m', b4_keep m m' (spk g 8) (spk g 192) ->
  getr regs' 19 = getr regs 19 -> getr regs' 21 = getr regs 21 -> getr regs' 26 = getr regs 26 ->
  LI g j regs m -> LIp g j regs' m'.
Proof.
  intros g j regs regs' m m' K E19 E21 E26 (Hj & H26 & (Hc & H21 & _) & Hl & HOUR & HIFS & HM7).
  unfold LIp, CURp, rg in *. rewrite E21, E26.
  refine (conj Hj (conj H26 (conj (conj Hc H21) (conj Hl (conj _ (conj _ _)))))).
  - apply (b4_OUR_keep g m m'); [eapply b4_keep_sub; [exact K | unfold spk; lia | unfold spk; lia] | exact HOUR].
  - apply (b4_IFS_keep g j regs regs' m m'); [eapply b4_keep_sub; [exact K | unfold spk; lia | unfold spk; lia]
                                             | exact E19 | exact HIFS].
  - apply (b4_M7_keep g m m'); [eapply b4_keep_sub; [exact K | unfold spk; lia | unfold spk; lia] | exact HM7].
Qed.

(* FT across a run that keeps Φ's bytes, M7 at [sp+8, sp+16), FC's body pointer at [sp+32, sp+40) and OUR at
   [sp+76, sp+82): the second and third ranges leave out type_filler [sp+24, sp+32). *)
Lemma b4_FT_keep2 : forall g j phi regs regs' m m',
  b4_keep m m' phi (phi + t_len (g_in g) j) -> b4_keep m m' (spk g 8) (spk g 24) ->
  b4_keep m m' (spk g 32) (spk g 82) ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  FT g j phi regs m -> FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' K1 K2 K3 E20 E21 E26 E27
    (Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7).
  unfold FT, FC, rg in *. rewrite E20, E21, E26, E27.
  refine (conj Hj (conj H26 (conj (conj H27 (conj _ H20)) (conj H21 (conj _ (conj _ _)))))).
  - unfold q64 in *. eapply b4_ba_keep; [exact H32 | exact K3 | unfold spk; lia | rewrite length_le8; unfold spk; lia].
  - pose proof (b4_len_range (g_in g) j) as (Hl0 & _).
    eapply b4_ba_keep; [exact Hphi | exact K1 | lia | rewrite b4_phi_len; lia].
  - apply (b4_OUR_keep g m m'); [eapply b4_keep_sub; [exact K3 | unfold spk; lia | unfold spk; lia] | exact HOUR].
  - apply (b4_M7_keep g m m'); [eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia] | exact HM7].
Qed.

Lemma b4_FT_keep : forall g j phi regs regs' m m',
  b4_keep m m' phi (phi + t_len (g_in g) j) -> b4_keep m m' (spk g 8) (spk g 82) ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  FT g j phi regs m -> FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' K1 K2. apply b4_FT_keep2; [exact K1 | |];
    (eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia]).
Qed.

(* A write set inside [S - K, S - 104), interval by interval. *)
Lemma b4_fp : forall g W x, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
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

(* P0 (the P8 bundle) across a run that writes W, disjoint from [sp+76, sp+192). *)
Lemma b4_P0_keep : forall g regs regs' m m' W,
  P0 g regs m -> Frame.munch W m m' -> Frame.disjoint_from W (spk g 76) 116 ->
  getr regs' 21 = getr regs 21 -> getr regs' 27 = getr regs 27 -> P0 g regs' m'.
Proof.
  intros g regs regs' m m' W (((Hc & H21 & H27) & HOUR) & HID & HFG) MU HD E21 E27.
  unfold P0, PB, CUR, OURb, IDB, FGB, rg in *. rewrite E21, E27.
  assert (D : forall a n, spk g 76 <= a -> a + n <= spk g 192 -> Frame.disjoint_from W a n).
  { clear -HD. induction W as [|[lo hi] W IH]; cbn [disjoint_from] in *; intros a n H1 H2; [exact I|].
    destruct HD as [H HD]. split; [unfold spk in *; lia | exact (IH HD a n H1 H2)]. }
  refine (conj (conj (conj Hc (conj H21 H27)) _) (conj _ _)).
  - apply (bytes_at_transport rsegs W m m' _ _ HOUR MU). rewrite b4_len_OUR. apply D; unfold spk; lia.
  - apply (bytes_at_transport rsegs W m m' _ _ HID MU). rewrite b4_len_ID0. apply D; unfold spk; lia.
  - apply (bytes_at_transport rsegs W m m' _ _ HFG MU). rewrite b4_len_z72. apply D; unfold spk; lia.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma b4_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
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

(* The input block at a cut: [p, p + n) is a live entry block, so its bytes are those of the entry memory
   (FR's entry-block clause) and the entry memory holds the input there (GV's blk_data). *)
Lemma b4_in_all : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 < g_n g ->
  4096 <= g_p g /\ g_p g + g_n g <= YM05.alloc_ceiling /\ bytes_at rsegs mem (g_p g) (g_in g).
Proof.
  intros g hb L A regs mem md HFR HP Hn.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (_ & Hpn & Hdat & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (b1_blk B APIf ra empty FF L A mem md (g_p g) (g_n g) HM
             (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_intror Hin)))) as (_ & H1 & H2).
  pose proof alloc_ceiling_value as Hac.
  split; [exact H1|]. split; [exact H2|].
  split; [lia|]. split; [unfold g_n, nlen in *; lia|].
  intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < g_n g) by (unfold g_n, nlen; lia).
  pose proof (Hblk (g_p g) (g_n g) (Z.of_nat k) Hin Hk') as E1.
  assert (Hk'' : 0 <= Z.of_nat k < Z.of_nat (length (g_in g))) by lia.
  pose proof (Hdat (Z.of_nat k) Hk'') as E2.
  rewrite E2, Nat2Z.id, SEGS in E1. exact E1.
Qed.

(* The input-byte lemma: the byte at p + i (0 <= i < n) in the memory of a cut is in[i]. *)
Lemma b4_in_byte : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  bytes_at rsegs mem (g_p g + i) [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi.
  destruct (b4_in_all g hb L A regs mem md HFR HP ltac:(lia)) as (H1 & H2 & HB).
  pose proof (b4_ba_sub mem (g_p g) (g_in g) (Z.to_nat i) 1 HB ltac:(unfold g_n, nlen in Hi; lia)) as H.
  rewrite Z2Nat.id in H by lia. rewrite (b4_firstn1 (g_in g) (Z.to_nat i)) in H by (unfold g_n, nlen in Hi; lia).
  exact H.
Qed.

(* The same read in the normalized memory of a run. *)
Lemma b4_in_rd : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  ov_read_bytes rsegs (normalize rsegs mem) (wa (g_p g + i)) 1 = Some [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi. apply b4_ld1.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _). unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  exact (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem HMI)) (b4_in_byte g hb L A regs mem md i HFR HP Hi)).
Qed.

(* The live harness block and an entry block are disjoint (the allocator's blocks are pairwise disjoint). *)
Lemma b4_hb_disj : forall g phi n L A regs mem md a k,
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  In (a, k) (blocks (g_L g) (g_A g)) -> phi + n <= a \/ a + k <= phi.
Proof.
  intros g phi n L A regs mem md a k HFR HP Hin.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws (APIf rc)) _ _ _ _ HM) as PD.
  apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ HP) in PD.
  destruct PD as [PD _]. pose proof (PD (a, k) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
  exact Hd.
Qed.

(* The input block is an entry block when n > 0. *)
Lemma b4_in_blk : forall g, GV B empty g -> 0 < g_n g -> In (g_p g, g_n g) (blocks (g_L g) (g_A g)).
Proof.
  intros g (_ & Hpn & _) Hn. destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

End S.
