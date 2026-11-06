(* Helpers for the segment lemmas of batch b5 (F07-F10, I01, I02, G01-G03) of fuzz_ctrl LLVMFuzzerTestOneInput
   (plain): the frame-loop model facts (Φ's length, ID_j and FG_j lengths, Φ's first 50 bytes, the bound of
   `first`'s length nb), b5_mid (sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the
   continuation), Φ's heap bound, and the transport of the turn-j bundles (FB, IFS and their parts) across a run
   that keeps s0-s11 and writes only in W.
   libreac v1.9.0 (SlotInv.v header): frame objects 16 bytes higher (our sp+76, frag sp+82, id sp+154, the parsed
   block sp+1752, the reply outputs sp+1728 .. sp+1752), type_filler at sp+24 and the record's body pointer at sp+32
   (one 16-byte premise of b5_FB_keep), FSb over `first` (have [sp+16], nb in s3, the nb body bytes at sp+40, so
   b5_FSb_keep / b5_IFS_keep take the registers), rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- Model facts of the frame loop ---- *)

Lemma b5_byte_nn : forall b : byte, 0 <= bv_unsigned b.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. lia. Qed.

Lemma b5_fL_nn : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb, RcIdentModel.bz.
  pose proof (b5_byte_nn (RcIdentModel.nthb inp (Z.to_nat c))).
  pose proof (b5_byte_nn (RcIdentModel.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma b5_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. assert (Hn : 0 <= nlen inp) by (unfold nlen; lia).
  induction j as [|j IH]; cbn [fc].
  - unfold c0. lia.
  - pose proof (b5_fL_nn inp (fc inp j)). unfold f_next, f_body, f_len, f_h, f_left. lia.
Qed.

Lemma b5_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (b5_fc_range inp j). pose proof (b5_fL_nn inp (fc inp j)).
  unfold t_len, t_body, f_len, f_body, f_h, f_left. lia.
Qed.

Lemma b5_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (b5_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi. fold (t_len inp j). fold (t_body inp j).
  rewrite length_firstn, length_skipn. unfold nlen in H3. lia.
Qed.

Lemma b5_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

Lemma b5_tg_eq : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j Hb. unfold t_g, fr50. rewrite firstn_app, b5_phi_len.
  replace (50 - Z.to_nat (t_len inp j))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma b5_ba_prefix : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma b5_phi_g : forall m inp j phi, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof. intros m inp j phi H Hb. rewrite (b5_tg_eq inp j Hb). apply b5_ba_prefix. exact H. Qed.

Lemma b5_rpid_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id. destruct (RcReply.ir len g); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma b5_fgid_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma b5_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id];
    apply b5_fgid_len; apply b5_rpid_len; exact IH.
Qed.

Lemma b5_tIDr_len : forall inp j, length (t_IDr inp j) = 38%nat.
Proof. intros inp j. unfold t_IDr. apply b5_rpid_len. apply b5_tID_len. Qed.

Lemma b5_fgfr_n : forall len g, RcFrag.fg_fr len g = true -> 1 <= RcFrag.fg_n g <= 22.
Proof.
  intros len g H. unfold RcFrag.fg_fr in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
  end.
  lia.
Qed.

Lemma b5_bat_nn : forall bs i, 0 <= RcFrag.bat bs i.
Proof. intros bs i. unfold RcFrag.bat. apply b5_byte_nn. Qed.

Lemma b5_body_len : forall g, length g = 50%nat -> 1 <= RcFrag.fg_n g <= 22 ->
  length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g).
Proof.
  intros g Hg Hn. unfold RcFrag.fg_body, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
Qed.

Lemma b5_clear_len : forall st, length st = 72%nat -> length (RcFrag.fg_clear st) = 72%nat.
Proof.
  intros st H. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn, H. reflexivity.
Qed.

Lemma b5_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fg_next, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  pose proof (b5_fgfr_n len g Efr) as Hn. pose proof (b5_body_len g Hg Hn) as Hb.
  destruct (RcFrag.bat g 19 =? 1); cbn [negb].
  - unfold RcFrag.fg_first, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hb, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb]; [|apply b5_clear_len; exact Hs].
    unfold RcFrag.fg_keep in Ek. apply andb_true_iff in Ek as [_ Ek]. apply Z.leb_le in Ek.
    pose proof (b5_bat_nn st 7) as H7. unfold RcFrag.fg_T, RcFrag.fg_lf in Ek.
    assert (Hj : length (RcFrag.fg_join st g) = 72%nat).
    { unfold RcFrag.fg_join, RcFrag.fg_T, RcFrag.fg_lf.
      rewrite !length_app, length_firstn, Hb, length_skipn, Hs. lia. }
    destruct (RcFrag.fg_close st g); cbn [negb]; apply b5_clear_len; exact Hj.
Qed.

Lemma b5_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg];
    (apply b5_fgst_len; [exact IH | apply b5_tg_len]).
Qed.

Lemma b5_tFGf_len : forall inp j, length (t_FGf inp j) = 72%nat.
Proof. intros inp j. unfold t_FGf. apply b5_fgst_len; [apply b5_tFG_len | apply b5_tg_len]. Qed.

(* `first`'s length nb is 0 before the first FIRST and Φ[26] in 1 .. 22 after one (fuzz/fuzz_ctrl.c v1.9.0:407-411). *)
Lemma b5_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 22.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:E; cbn [fs_nb]; [|exact IH].
  unfold f_opens in E. apply andb_true_iff in E as [E _].
  pose proof (b5_fgfr_n _ _ E) as Hn. unfold RcFrag.fg_n in Hn. lia.
Qed.

Lemma b5_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof. intros inp j. apply RcParse.ctrlparse_kind_range. Qed.

(* A small case split: a fact checked by computation at each of 0 .. 13. *)
Ltac b5_cases13 k :=
  let E := fresh "E" in
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
              k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia;
  repeat match type of E with
  | _ \/ _ => destruct E as [E|E]; [subst k; vm_compute; reflexivity|]
  | _ => subst k; vm_compute; reflexivity
  end.

Lemma b5_le4_small : forall k, 0 <= k <= 13 ->
  [Z_to_bv 8 k; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] = le4 (Z_to_bv 64 k).
Proof. intros k Hk. b5_cases13 k. Qed.

Lemma b5_tB_read : forall m a inp j, bytes_at rsegs m a (t_B inp j) ->
  ov_read_bytes rsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 (t_k inp j))).
Proof.
  intros m a inp j H.
  assert (L : (0 + 4 <= length (t_B inp j))%nat) by (unfold t_B; rewrite RcParse.ctrlparse_length; lia).
  pose proof (bytes_at_ov_read rsegs m a _ 0 4 H L) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r in R. rewrite R. f_equal.
  unfold t_B, t_k. cbv [skipn].
  rewrite RcParse.ctrlparse_kind_bytes. apply b5_le4_small. apply RcParse.ctrlparse_kind_range.
Qed.

(* ---- Memory and registers ---- *)

Lemma b5_stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi ->
  Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H3) H4 H5. split; [lia|]. split; [lia|]. intros a Ha. apply H3. lia. Qed.

Lemma b5_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia | exact (IH a n a' n' H4 H1 H2)].
Qed.

Lemma b5_ba : forall W mem m' a bs, bytes_at rsegs mem a bs -> Frame.munch W mem m' ->
  disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof. intros W mem m' a bs H MU D. exact (bytes_at_transport rsegs W mem m' a bs H MU D). Qed.

Lemma b5_q64 : forall W mem m' a v, q64 mem a v -> Frame.munch W mem m' -> disjoint_from W a 8 -> q64 m' a v.
Proof. unfold q64. intros W mem m' a v H MU D. apply (b5_ba W mem); [exact H | exact MU|]. rewrite length_le8. exact D. Qed.

(* s0, s1, s2-s11 kept. *)
Definition SKP (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma b5_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. unfold rg. intros regs regs' r v E H. rewrite E. exact H. Qed.

Lemma b5_phi_keep : forall g j phi mem m' W, bytes_at rsegs mem phi (t_phi (g_in g) j) -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> bytes_at rsegs m' phi (t_phi (g_in g) j).
Proof.
  intros g j phi mem m' W H MU D. pose proof (b5_len_range (g_in g) j) as (R1 & _).
  apply (b5_ba W mem); [exact H | exact MU|]. rewrite b5_phi_len, Z2Nat.id by lia. exact D.
Qed.

Lemma b5_FB_keep : forall g j phi regs regs' mem m' W,
  FB g j phi regs mem -> SKP regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 8 -> disjoint_from W (spk g 24) 16 ->
  disjoint_from W (spk g 76) 6 -> disjoint_from W (spk g 1752) 36 ->
  FB g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W
    ((Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7) & (H23 & H25 & H9 & H18 & (H8 & H22 & H24 & HB)))
    (E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) MU Dp D8 D24 D76 DB.
  split.
  - split; [exact Hj|]. split; [exact (b5_rg _ _ _ _ E26 H26)|].
    split; [split; [exact (b5_rg _ _ _ _ E27 H27)|]; split; [|exact (b5_rg _ _ _ _ E20 H20)]|].
    { apply (b5_q64 W mem m' _ _ H32 MU). apply (b5_dj_sub W _ _ _ _ D24); unfold spk; lia. }
    split; [exact (b5_rg _ _ _ _ E21 H21)|].
    split; [exact (b5_phi_keep g j phi mem m' W Hphi MU Dp)|].
    split.
    + unfold OURb in *. apply (b5_ba W mem); [exact HOUR | exact MU|]. rewrite OUR_length. exact D76.
    + unfold M7 in *. exact (b5_q64 W mem m' _ _ HM7 MU D8).
  - split; [exact (b5_rg _ _ _ _ E23 H23)|]. split; [exact (b5_rg _ _ _ _ E25 H25)|].
    split; [exact (b5_rg _ _ _ _ E9 H9)|]. split; [exact (b5_rg _ _ _ _ E18 H18)|].
    split; [exact (b5_rg _ _ _ _ E8 H8)|]. split; [exact (b5_rg _ _ _ _ E22 H22)|].
    split; [apply (b5_q64 W mem m' _ _ H24 MU); apply (b5_dj_sub W _ _ _ _ D24); unfold spk; lia|].
    apply (b5_ba W mem); [exact HB | exact MU|]. unfold t_B. rewrite RcParse.ctrlparse_length. exact DB.
Qed.

Lemma b5_IDb_keep : forall g idb mem m' W, length idb = 38%nat -> IDb g idb mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 154) 38 -> IDb g idb m'.
Proof.
  intros g idb mem m' W L (H & Hok) MU D. split; [|exact Hok]. unfold IDB in *.
  apply (b5_ba W mem); [exact H | exact MU|]. rewrite L. exact D.
Qed.

Lemma b5_FGb_keep : forall g st mem m' W, length st = 72%nat -> FGb g st mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 82) 72 -> FGb g st m'.
Proof.
  intros g st mem m' W L (H & Hok) MU D. split; [|exact Hok]. unfold FGB in *.
  apply (b5_ba W mem); [exact H | exact MU|]. rewrite L. exact D.
Qed.

(* `first`: have [sp+16], nb in s3, the nb body bytes at sp+40. *)
Lemma b5_FSb_keep : forall g s st regs regs' mem m' W, FSb g s st regs mem -> getr regs' 19 = getr regs 19 ->
  Frame.munch W mem m' -> disjoint_from W (spk g 16) 8 -> disjoint_from W (spk g 40) (fs_nb s) ->
  FSb g s st regs' m'.
Proof.
  intros g s st regs regs' mem m' W (H16 & H19 & HB & HL & HFI) E19 MU D16 D40.
  split; [exact (b5_q64 W mem m' _ _ H16 MU D16)|].
  split; [exact (b5_rg _ _ _ _ E19 H19)|].
  split; [apply (b5_ba W mem); [exact HB | exact MU | rewrite HL; exact D40]|].
  split; [exact HL | exact HFI].
Qed.

(* The 35-byte body buffer sp+40 .. sp+75 holds the nb <= 22 body bytes. *)
Lemma b5_IFS_keep : forall g j regs regs' mem m' W, IFS g j regs mem -> SKP regs regs' -> Frame.munch W mem m' ->
  disjoint_from W (spk g 16) 8 -> disjoint_from W (spk g 40) 35 -> disjoint_from W (spk g 82) 72 ->
  disjoint_from W (spk g 154) 38 -> IFS g j regs' m'.
Proof.
  intros g j regs regs' mem m' W (HI & HG & HS) (_ & _ & _ & E19 & _) MU D16 D40 D82 D154.
  pose proof (b5_nb_range (g_in g) j) as Hnb.
  split; [exact (b5_IDb_keep g _ mem m' W (b5_tID_len _ _) HI MU D154)|].
  split; [exact (b5_FGb_keep g _ mem m' W (b5_tFG_len _ _) HG MU D82)|].
  apply (b5_FSb_keep g _ _ regs regs' mem m' W HS E19 MU D16).
  apply (b5_dj_sub W _ _ _ _ D40); lia.
Qed.

(* A disjointness goal over a literal W: every bound is linear in g_S g, phi and the model lengths. *)
Ltac b5_dj := cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME in *; repeat split; try exact I; lia.

(* Every interval of W lies in [S - K, S - 104): so does every address a run writes. *)
Lemma b5_fp : forall g W, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W HW. induction HW as [|[lo hi] W Hh HW IH]; intros x Hx O; cbn [Frame.outside] in O.
  - exfalso. apply O. exact I.
  - cbn [fst snd] in Hh.
    destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
      [lia | | |]; apply IH; try exact Hx; intros O'; apply O; split; try exact O'; lia.
Qed.

Lemma b5_c_bytes : forall m A c, Step.rw_cells rsegs m A [c] -> bytes_at rsegs m A (Cells.cbytes c).
Proof. intros m A c H. pose proof (sl_cells_bytes m A [c] H) as Hb. cbn [Cells.cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Ltac b5_fp_tac := apply b5_fp; repeat constructor; cbn [fst snd]; unfold SLOT_K, SLOT_STACK in *; lia.

Lemma b5_q64_read : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  unfold q64. intros m a v H.
  assert (L : (0 + 8 <= length (le8 (Z_to_bv 64 v)))%nat) by (rewrite length_le8; lia).
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H L) as R.
  cbn [Z.of_nat] in R. rewrite Z.add_0_r in R. rewrite R. cbv [skipn].
  rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma b5_first1 : forall (l : list byte) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d H; [cbn in H; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in H. lia.
Qed.

Lemma b5_byte_read : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  rewrite (bytes_at_read rsegs m a bs (Z.of_nat i) 1 H ltac:(lia) ltac:(rewrite Nat2Z.id; lia)).
  rewrite Nat2Z.id. f_equal. apply b5_first1. exact Hi.
Qed.

Lemma b5_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma b5_psum_bnd : forall bs k, 0 <= RcModel.psum bs k <= 255 * Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcModel.psum]; [lia|].
  pose proof (b5_byte_rng (nth k bs (Z_to_bv 8 0))). lia.
Qed.

Lemma b5_RPS_keep : forall g j phi mem m' W, RPS g j phi mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 1728) 24 -> RPS g j phi m'.
Proof.
  intros g j phi mem m' W HR MU D. unfold RPS, u16, q64, spk in *. destruct HR as (H1 & H0). split.
  - intros Hi. destruct (H1 Hi) as (A1 & A2 & A3). split; [|split].
    + apply (b5_ba W mem); [exact A1 | exact MU|]. apply (b5_dj_sub W _ _ _ _ D);
        unfold RcReply.reply_addr; cbn [length]; lia.
    + apply (b5_ba W mem); [exact A2 | exact MU|]. rewrite length_le8. apply (b5_dj_sub W _ _ _ _ D); lia.
    + apply (b5_ba W mem); [exact A3 | exact MU|]. rewrite length_le8. apply (b5_dj_sub W _ _ _ _ D); lia.
  - intros Hi. destruct (H0 Hi) as (A1 & A2 & A3). split; [|split].
    + apply (b5_ba W mem); [exact A1 | exact MU|]. rewrite length_le2. apply (b5_dj_sub W _ _ _ _ D); lia.
    + apply (b5_ba W mem); [exact A2 | exact MU|]. rewrite length_le8. apply (b5_dj_sub W _ _ _ _ D); lia.
    + apply (b5_ba W mem); [exact A3 | exact MU|]. rewrite length_le8. apply (b5_dj_sub W _ _ _ _ D); lia.
Qed.

(* The reply arm when IR(Φ, len): len >= 50, sum_ok, pll in 1 .. 10, r = 1; and when not: r = 0, ID kept. *)
Lemma b5_ir_facts : forall inp j, t_ir inp j = true ->
  50 <= t_len inp j /\ t_big inp j = true /\ t_sum_ok inp j = true /\ 1 <= r_pll (t_g inp j) <= 10 /\
  t_r inp j = 1.
Proof.
  intros inp j H. unfold t_ir in H.
  destruct (RcReply.ir_bytes _ _ H) as (H50 & _).
  destruct (RcReply.ir_true _ _ H) as (_ & _ & _ & _ & Hs & _ & _ & Hbs & _).
  assert (Hbig : t_big inp j = true) by (unfold t_big; apply Z.leb_le; exact H50).
  split; [exact H50|]. split; [exact Hbig|]. split.
  - unfold t_sum_ok. rewrite Hbig. unfold RcReply.ir_blk in Hbs. rewrite Hbs. reflexivity.
  - split; [unfold r_pll; lia|]. unfold t_r, rp_r. rewrite H. reflexivity.
Qed.

Lemma b5_ir_false : forall inp j, t_ir inp j = false -> t_r inp j = 0 /\ t_IDr inp j = t_ID inp j.
Proof. intros inp j H. unfold t_ir in H. unfold t_r, rp_r, t_IDr, rp_id. rewrite H. split; reflexivity. Qed.

(* Branch conditions over literals and linear Z terms. *)
Ltac b5_ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) by lia end.
Ltac b5_cond := first
  [ reflexivity
  | apply negb_false_iff; unfold bv_eqb, zxb; b5_ul; apply Z.eqb_eq; lia
  | apply negb_true_iff; unfold bv_eqb, zxb; b5_ul; apply Z.eqb_neq; lia
  | unfold bv_ltu, zxb; b5_ul; apply Z.ltb_ge; lia
  | unfold bv_ltu, zxb; b5_ul; apply Z.ltb_lt; lia
  | unfold bv_eqb, zxb; b5_ul; apply Z.eqb_neq; lia
  | unfold bv_eqb, zxb; b5_ul; apply Z.eqb_eq; lia ].
Ltac b5_br b :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; b5_cond); cbv iota
  end.

(* A word equation Z_to_bv 64 x = Z_to_bv 64 y with x, y linear in the context's bounded terms. *)
Ltac b5_weq := f_equal; unfold zxb; b5_ul; cbn [RcModel.psum]; lia.

(* ---- Slices, cells and the stack (I02, G01-G03) ---- *)

Lemma b5_ba_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  apply b5_ba_prefix. exact H.
Qed.

Lemma b5_rw_ba : forall m a n junk bs, Step.rw_cells rsegs m a [Cells.CB n junk] -> bytes_at rsegs m a bs ->
  length bs = n -> Step.rw_cells rsegs m a [Cells.CB n bs].
Proof.
  intros m a n junk bs (_ & Hw) Hb L. split; [|exact Hw].
  split; [cbn; split; [exact L | exact I]|]. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma b5_wr_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + n <= hi ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H3) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H3 (a + i) ltac:(lia))).
Qed.

Lemma b5_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* The frame loop's fragment class has nonzero pointers: never a refusal. *)
Lemma b5_nref : forall len st g, fcls len st g <> RcFrag.FgRefuse.
Proof.
  intros len st g. unfold fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (negb (RcFrag.fg_fr len g)); [discriminate|].
  destruct (RcFrag.bat g 19 =? 1); [discriminate|].
  destruct (negb (RcFrag.fg_keep st g)); [discriminate|].
  destruct (negb (RcFrag.fg_close st g)); discriminate.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Φ, a block of the allocator (hb1 Φ n), lies in [4096, S - K). *)
Lemma b5_phi_bnd : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  4096 <= phi /\ phi + n <= g_S g - SLOT_K.
Proof.
  intros g phi n L A regs mem md HFR HP.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  assert (Hin : In (phi, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. left. reflexivity. }
  apply blocks_In in Hin as (p & Hp & Hpin).
  destruct (mr_blocks_range B (aa_MR (APIf rc)) (aa_laws (APIf rc)) L A mem md p n HM Hpin) as (H1 & H2).
  lia.
Qed.

Lemma b5_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
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
