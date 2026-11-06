(** reac_declared_vlan_add: the pure facts its two walks share (plain lib/Prog/reac_declared_vlan_add.v, UBSan
    lib/U/Prog/reac_declared_vlan_add.v). No image: the memory facts hold over any segment list. Written new.
    - [rw_cells_cons], [zero18_split]: the cells of the appended entry tab[*n] between memset and strncpy (15 bytes
      for strncpy, then the byte 15 and the two vid bytes).
    - [vmatch], [existsb_skipn_S], [vlan_add_dup], [vlan_add_full], [vlan_add_app]: the search loop's model (the
      first entry with this vid and an equal parent) and the three answers of SegModel.vlan_add.
    - [new_entry_enc], [rtab_enc_snoc]: the 18 new bytes (strncpy's 15 bytes, stpncpy_c.stpn_result unfolded, over
      memset's zeros, byte 15 still 0, then le2 vid) encode (firstn 15 (cut_nul p), vid), and the old table's bytes
      with them encode t ++ [that entry].
    - [lts_small]: a signed compare of two words below 2^63 is the compare of their values. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ZBridge Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** Cells *)
Section Cells.
Variable segs : list Segment.

Lemma rw_cells_cons : forall m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[Hwf Hb] Hw]. cbn [cells_wf cells_bytes cells_size] in Hwf, Hb, Hw.
  destruct Hwf as [Hc Hcs]. destruct Hw as (Hw0 & Hw1 & Hw).
  apply bytes_at_app in Hb as [Hb1 Hb2]. rewrite (cbytes_length c Hc) in Hb2.
  split.
  - split; [split|].
    + cbn [cells_wf]. split; [exact Hc | exact I].
    + cbn [cells_bytes]. rewrite app_nil_r. exact Hb1.
    + cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact Hcs | exact Hb2]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

(** memset's 18 bytes at tab[*n]: strncpy's 15-byte destination, then bytes 15 .. 17. *)
Lemma zero18_split : forall m A (x : byte),
  rw_cells segs m A [CB 18 (repeat x 18)] ->
  rw_cells segs m A [CB 15 (repeat x 15)] /\ rw_cells segs m (A + 15) [CB 1 [x]; CB 2 [x; x]].
Proof.
  intros m A x H.
  pose proof (rw_cells_split_CB segs m A [] 18 (repeat x 18) [] [15%nat; 1%nat; 2%nat] H eq_refl) as H3.
  cbn [app mk_CB_cells firstn skipn repeat] in H3.
  destruct (rw_cells_cons m A _ _ H3) as [H15 Hr].
  split; [exact H15 | exact Hr].
Qed.
End Cells.

(** ** The model *)
(** The search loop's test on one entry (reac_declared_vlan.c:71), as SegModel.vlan_add states it. *)
Definition vmatch (vid : Z) (p : list Z) (e : list Z * Z) : bool := (snd e =? vid) && (strcmp (fst e) p =? 0).

Lemma existsb_skipn_S : forall {A} (f : A -> bool) (l : list A) i d, (i < length l)%nat ->
  existsb f (skipn i l) = f (nth i l d) || existsb f (skipn (S i) l).
Proof.
  intros A f l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma vlan_add_dup : forall t max p vid, existsb (vmatch vid p) t = true -> vlan_add t max p vid = (0, t).
Proof. intros t max p vid H. cbv beta delta [vlan_add vmatch] in *. rewrite H. reflexivity. Qed.

Lemma vlan_add_full : forall t max p vid, existsb (vmatch vid p) t = false -> max <= Z.of_nat (length t) ->
  vlan_add t max p vid = (-1, t).
Proof.
  intros t max p vid H Hm. cbv beta delta [vlan_add vmatch] in *. rewrite H.
  rewrite (proj2 (Z.leb_le _ _) Hm). reflexivity.
Qed.

Lemma vlan_add_app : forall t max p vid, existsb (vmatch vid p) t = false -> Z.of_nat (length t) < max ->
  vlan_add t max p vid = (1, t ++ [(firstn 15 (cut_nul p), vid)]).
Proof.
  intros t max p vid H Hm. cbv beta delta [vlan_add vmatch] in *. rewrite H.
  rewrite (proj2 (Z.leb_gt _ _) Hm). reflexivity.
Qed.

(** ** The appended entry *)
Lemma firstn_min_len : forall {A} (l : list A) n, firstn (Nat.min (length l) n) l = firstn n l.
Proof.
  intros A l n. destruct (Nat.le_ge_cases (length l) n) as [H|H].
  - rewrite Nat.min_l by exact H. rewrite firstn_all, firstn_all2 by exact H. reflexivity.
  - rewrite Nat.min_r by exact H. reflexivity.
Qed.

(** strncpy(dst, parent, 15) over memset's zeros (stpncpy_c.stpn_result pb 15 unfolded), byte 15 left 0, then the
    vid's two bytes: seg_spec.rvlan_enc of (firstn 15 (cut_nul p), vid). *)
Lemma new_entry_enc : forall (pb : list byte) p vid,
  zs pb = p -> ~ In 0 p -> 0 <= vid < 65536 ->
  rvlan_enc (firstn 15 (cut_nul p), vid)
    ((firstn (Nat.min (length pb) 15) pb ++ repeat (Z_to_bv 8 0) (15 - Nat.min (length pb) 15)) ++
     [Z_to_bv 8 0] ++ le2 (Z_to_bv 64 vid)).
Proof.
  intros pb p vid Hz Hn Hv.
  rewrite (cut_nul_id p Hn).
  assert (Lp : length pb = length p) by (rewrite <- Hz; unfold zs; symmetry; apply length_map).
  remember (Nat.min (length pb) 15) as k eqn:Ek.
  remember (firstn k pb) as q eqn:Eq.
  assert (Lq : length q = k) by (subst q k; rewrite length_firstn; lia).
  assert (Hk : (k <= 15)%nat) by (subst k; lia).
  assert (Zq : zs q = firstn 15 p).
  { subst q k. unfold zs. rewrite <- firstn_map. fold (zs pb). rewrite Hz, Lp. apply firstn_min_len. }
  remember (q ++ repeat (Z_to_bv 8 0) (15 - k) ++ [Z_to_bv 8 0]) as f16 eqn:Ef16.
  replace ((q ++ repeat (Z_to_bv 8 0) (15 - k)) ++ [Z_to_bv 8 0] ++ le2 (Z_to_bv 64 vid))
    with (f16 ++ le2 (Z_to_bv 64 vid)) by (subst f16; rewrite <- !app_assoc; reflexivity).
  assert (L16 : length f16 = 16%nat) by (subst f16; rewrite !length_app, repeat_length, Lq; cbn [length]; lia).
  assert (F16 : firstn 16 (f16 ++ le2 (Z_to_bv 64 vid)) = f16) by (rewrite <- L16; apply firstn_app_exact).
  assert (S16 : skipn 16 (f16 ++ le2 (Z_to_bv 64 vid)) = le2 (Z_to_bv 64 vid))
    by (rewrite <- L16; apply skipn_app_exact).
  unfold rvlan_enc, fld. cbn [fst snd].
  change (skipn 0 (f16 ++ le2 (Z_to_bv 64 vid))) with (f16 ++ le2 (Z_to_bv 64 vid)).
  rewrite F16, S16.
  split; [rewrite length_app, L16, length_le2; reflexivity|].
  split; [|split; [exact Hv|]].
  - split; [exact L16|].
    split; [rewrite length_firstn; lia|].
    split; [intros H; apply Hn; rewrite <- (firstn_skipn 15 p); apply in_or_app; left; exact H|].
    rewrite <- Zq, Ef16. unfold zs. rewrite !map_app, length_map.
    rewrite firstn_app, firstn_all2 by (rewrite length_map; lia). rewrite length_map.
    replace (S (length q) - length q)%nat with 1%nat by lia.
    f_equal. destruct (15 - k)%nat; reflexivity.
  - apply firstn_all2. rewrite length_le2. lia.
Qed.

(** The table t at bt with one more entry's bytes after it. *)
Lemma rtab_enc_snoc : forall t bt e f, rtab_enc t bt -> rvlan_enc e f -> rtab_enc (t ++ [e]) (bt ++ f).
Proof.
  intros t bt e f [HL HE] HF. pose proof HF as (Lf & _).
  split.
  - rewrite !length_app, HL, Lf. cbn [length]. lia.
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length t)) as [Hlt|Hge].
    + rewrite app_nth1 by exact Hlt. unfold fld. rewrite skipn_app.
      replace (18 * i - length bt)%nat with 0%nat by lia. cbn [skipn].
      rewrite firstn_app, length_skipn.
      replace (18 - (length bt - 18 * i))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
      exact (HE i Hlt).
    + assert (Ei : i = length t) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      unfold fld. replace (18 * length t)%nat with (length bt) by lia.
      rewrite skipn_app_exact, firstn_all2 by lia. exact HF.
Qed.

(** ** Words *)
Lemma lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  destruct (Z.ltb_spec x (2 ^ 63)); [|lia]. destruct (Z.ltb_spec y (2 ^ 63)); [|lia]. reflexivity.
Qed.
