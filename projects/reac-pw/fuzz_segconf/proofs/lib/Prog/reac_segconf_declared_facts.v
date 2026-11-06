(** reac-pw/fuzz_segconf: facts the two walks of reac_segconf_declared share (plain lib/Prog/reac_segconf_declared.v,
    UBSan lib/U/Prog/reac_segconf_declared.v). Written new. No image: the memory lemmas take the
    build's segment list.
    - The model: the steps of SegModel.r_decl_go that the loop takes, the answers of vlan_add and vlan_split.
    - The memory: rw_cells and wr_at of adjacent ranges; a writable byte at an address no loaded segment covers is
      present in the overlay (RiscvSemantics.wview), so every writable range above the image holds some bytes (the
      frame's parent buffer after split, the slack after its C string, the free entries of the table); a byte range
      that a callee's footprint W covers only through a cell the callee leaves as it found it keeps its bytes (the
      errno cell, which split's W holds and which keeps its value ev, against the stack-protector GOT cell, which no
      premise states apart from it). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
Import ListNotations.
Open Scope Z_scope.

(** ** The model *)
(** One pass of the loop over c->seg: entry i ignored, entry i not split, entry i split and added. *)
Lemma dc_go_ignore : forall segs i t max added, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = true ->
  r_decl_go (skipn i segs) t max added = r_decl_go (skipn (S i) segs) t max added.
Proof.
  intros segs i t max added Hi Hg. rewrite (sq_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg.
  reflexivity.
Qed.

Lemma dc_go_nosplit : forall segs i t max added, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = false ->
  vlan_split (rs_name (nth i segs rseg_d)) = None ->
  r_decl_go (skipn i segs) t max added = r_decl_go (skipn (S i) segs) t max added.
Proof.
  intros segs i t max added Hi Hg Hs. rewrite (sq_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg, Hs.
  reflexivity.
Qed.

Lemma dc_go_split : forall segs i t max added p v, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = false ->
  vlan_split (rs_name (nth i segs rseg_d)) = Some (p, v) ->
  r_decl_go (skipn i segs) t max added =
  if fst (vlan_add t max p v) <? 0 then (-1, snd (vlan_add t max p v))
  else r_decl_go (skipn (S i) segs) (snd (vlan_add t max p v)) max (added + fst (vlan_add t max p v)).
Proof.
  intros segs i t max added p v Hi Hg Hs. rewrite (sq_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg, Hs.
  destruct (vlan_add t max p v) as [rv t']. reflexivity.
Qed.

Lemma dc_go_end : forall segs t max added, r_decl_go (skipn (length segs) segs) t max added = (added, t).
Proof. intros segs t max added. rewrite skipn_all. reflexivity. Qed.

(** vlan_add answers 0, 1 or -1. *)
Lemma dc_add_rv : forall t max p v,
  fst (vlan_add t max p v) = 0 \/ fst (vlan_add t max p v) = 1 \/ fst (vlan_add t max p v) = -1.
Proof.
  intros t max p v. unfold vlan_add.
  destruct (existsb _ t); [left; reflexivity|].
  destruct (max <=? Z.of_nat (length t)); [right; right; reflexivity | right; left; reflexivity].
Qed.

(** vlan_split's vid is a uint16_t and its parent has at most 15 bytes. *)
Lemma dc_split_some : forall s p v, vlan_split s = Some (p, v) -> 0 <= v < 65536 /\ (length p <= 15)%nat.
Proof.
  intros s p v. unfold vlan_split. destruct (strrchr s DOT) as [d|]; [|discriminate]. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
    intros H; try discriminate H.
  injection H as <- <-.
  repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?] end.
  match goal with H : (16 <? d + 1)%nat = false |- _ => apply Nat.ltb_ge in H end.
  split; [apply Z.mod_pos_bound; lia|]. rewrite length_firstn. lia.
Qed.

(** ** Intervals *)
Lemma dc_outside_ins : forall W1 W2 lo hi x, outside (W1 ++ W2) x -> ~ (lo <= x < hi) ->
  outside (W1 ++ (lo, hi) :: W2) x.
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 lo hi x H Hx; cbn [app outside] in *.
  - split; assumption.
  - destruct H as [H1 H2]. split; [exact H1 | apply IH; assumption].
Qed.

(** find_segment answers a segment of the list. *)
Lemma dc_find_in : forall (segs : list Segment) x k seg, find_segment segs x k = Some seg -> In seg segs.
Proof.
  induction segs as [|s l IH]; intros x k seg H; cbn [find_segment] in H; [discriminate H|]. cbv zeta in H.
  revert H. match goal with |- context [if ?b then _ else _] => destruct b end; intros H;
    [injection H as <-; left; reflexivity | right; exact (IH x k seg H)].
Qed.

(** ** Memory *)
Section Mem.
Variable segs : list Segment.

Lemma dc_wr_pre : forall m a n n', wr_at segs m a n -> 0 <= n' <= n -> wr_at segs m a n'.
Proof. intros m a n n' (Ha & Hb & H) Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma dc_wr_sub : forall m a n k n', wr_at segs m a n -> 0 <= k -> 0 <= n' -> k + n' <= n -> wr_at segs m (a + k) n'.
Proof.
  intros m a n k n' (Ha & Hn & H) Hk Hn' Hkn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma dc_wr_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 -> wr_at segs m a n1 -> wr_at segs m (a + n1) n2 ->
  wr_at segs m a (n1 + n2).
Proof.
  intros m a n1 n2 H1 H2 (Ha & Hb & HA) (_ & Hd & HB). split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1); [apply HA; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma dc_rwc_app : forall m a cs1 cs2, rw_cells segs m a cs1 -> rw_cells segs m (a + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells segs m a (cs1 ++ cs2).
Proof.
  intros m a cs1 cs2 [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply dc_wr_app; [lia | lia | exact R1 | exact R2].
Qed.

Lemma dc_rwc_split : forall m a cs1 cs2, rw_cells segs m a (cs1 ++ cs2) ->
  rw_cells segs m a cs1 /\ rw_cells segs m (a + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m a cs1 cs2 [[W B] R]. apply cells_wf_app in W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2]. rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in R. split; (split; [split; assumption|]).
  - apply (dc_wr_pre m a _ _ R). lia.
  - apply (dc_wr_sub m a _ _ _ R); lia.
Qed.

Lemma dc_rwc_wr : forall m a cs, rw_cells segs m a cs -> wr_at segs m a (Z.of_nat (cells_size cs)).
Proof. intros m a cs [_ R]. exact R. Qed.

Lemma dc_rwc_bytes : forall m a cs, rw_cells segs m a cs -> bytes_at segs m a (cells_bytes cs).
Proof. intros m a cs [[_ B] _]. exact B. Qed.

Lemma dc_c4_bytes : forall m a v, rw_cells segs m a [C4 v] -> bytes_at segs m a (le4 v).
Proof.
  intros m a v H. apply dc_rwc_bytes in H. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

(** The whole of bs, read at once. *)
Lemma dc_read_all : forall m a bs, bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn] in R. replace (a + Z.of_nat 0) with a in R by lia. rewrite firstn_all in R. exact R.
Qed.

(** A writable byte that the image does not give (seg_rom None) is in the overlay, when every loaded segment is
    readable: RiscvSemantics.wview reads a writable segment's byte where memory_read would read it too. *)
Lemma dc_present : forall m x, forallb seg_readable segs = true -> seg_rom segs x = None ->
  wview segs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x Hr Hrom Hw. unfold wview in Hw. destruct (m x) as [b|] eqn:Em; [exists b; reflexivity|].
  exfalso. try rewrite Em in Hw. revert Hw Hrom. unfold seg_rom, memory_read. cbn [Z.of_N].
  destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:Ef; [|intros Hw; exfalso; apply Hw; reflexivity].
  assert (R : seg_readable seg = true).
  { apply (proj1 (forallb_forall _ _) Hr). exact (dc_find_in segs _ _ _ Ef). }
  rewrite R. destruct (seg_writable seg); [|intros Hw; exfalso; apply Hw; reflexivity]. cbv zeta.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg)))) as [b|];
    [intros _ H; discriminate H | intros Hw; exfalso; apply Hw; reflexivity].
Qed.

Lemma dc_bytes_of_wr : forall m k a, forallb seg_readable segs = true ->
  (forall i, 0 <= i < Z.of_nat k -> seg_rom segs (wa (a + i)) = None) ->
  wr_at segs m a (Z.of_nat k) -> exists bs, length bs = k /\ bytes_at segs m a bs.
Proof.
  intros m k. induction k as [|k IH]; intros a Hr Hrom HW.
  - exists []. split; [reflexivity|]. destruct HW as (Ha & Hb & _). apply bytes_at_nil. lia.
  - pose proof HW as (Ha & Hb & H).
    destruct (dc_present m (wa (a + Z.of_nat 0)) Hr) as [b Eb]; [apply Hrom; lia | apply H; lia |].
    destruct (IH (a + 1) Hr) as (bs & L & HB).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hrom. lia. }
    { replace (Z.of_nat k) with (Z.of_nat (S k) - 1) by lia. apply (dc_wr_sub m a _ 1 _ HW); lia. }
    exists (b :: bs). split; [cbn [length]; rewrite L; reflexivity|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error]. unfold mrd. rewrite Eb. reflexivity.
    + cbn [length]. exact HB.
Qed.

Lemma dc_rwc_of_wr : forall m a k, forallb seg_readable segs = true ->
  (forall i, 0 <= i < Z.of_nat k -> seg_rom segs (wa (a + i)) = None) ->
  wr_at segs m a (Z.of_nat k) -> exists bs, rw_cells segs m a [CB k bs].
Proof.
  intros m a k Hr Hrom HW. destruct (dc_bytes_of_wr m k a Hr Hrom HW) as (bs & L & HB). exists bs.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

(** A block no byte of which lies in a reserved segment of the image is apart from any range inside one. *)
Lemma dc_noimg_apart : forall a n r b k, blk_noimg segs a n -> In r (segments_reserved segs) ->
  bv_unsigned (fst r) <= b -> b + k <= bv_unsigned (fst r) + bv_unsigned (snd r) -> 0 < k -> 0 < n ->
  b + k <= a \/ a + n <= b.
Proof.
  intros a n r b k H Hr H1 H2 Hk Hn.
  destruct (Z_le_gt_dec (b + k) a) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (a + n) b) as [L'|L']; [right; exact L'|]. exfalso.
  destruct (Z_le_gt_dec a b) as [Hab|Hab].
  - apply (H (b - a) ltac:(lia) r Hr). lia.
  - apply (H 0 ltac:(lia) r Hr). lia.
Qed.

(** A byte range W covers only through a cell e that holds the same bytes before and after keeps its bytes. *)
Lemma dc_bat_keep : forall W1 W2 e k eb m m' A bs,
  bytes_at segs m A bs -> munch (W1 ++ (e, e + k) :: W2) m m' ->
  bytes_at segs m e eb -> bytes_at segs m' e eb -> Z.of_nat (length eb) = k ->
  disjoint_from (W1 ++ W2) A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof.
  intros W1 W2 e k eb m m' A bs (Ha & Hl & H) MU (He & Hel & HE) (_ & _ & HE') Hk HD.
  split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  assert (Hin : e <= A + Z.of_nat i < e + k \/ ~ (e <= A + Z.of_nat i < e + k)) by lia.
  destruct Hin as [Hin|Hout].
  - destruct (Z_of_nat_complete (A + Z.of_nat i - e) ltac:(lia)) as [j Ej].
    assert (Ej' : A + Z.of_nat i = e + Z.of_nat j) by lia.
    assert (Jl : (j < length eb)%nat) by lia.
    rewrite Ej', (HE' j Jl), <- (HE j Jl), <- Ej'. apply H. exact Hi.
  - assert (EQ : m' (wa (A + Z.of_nat i)) = m (wa (A + Z.of_nat i))).
    { apply MU. rewrite wa_unsigned by lia. apply dc_outside_ins; [|exact Hout].
      eapply disjoint_outside; [exact HD | lia]. }
    transitivity (mrd segs m (wa (A + Z.of_nat i))); [unfold mrd; rewrite EQ; reflexivity | apply H; exact Hi].
Qed.

(** The C string p with its NUL, and the slack after it. *)
Lemma dc_cstr_of_cstrz : forall m a p sl, cstrz_at segs m a p ->
  bytes_at segs m (a + Z.of_nat (length p) + 1) sl ->
  (- (a + Z.of_nat (length p) + 1)) mod 8 <= Z.of_nat (length sl) -> cstr_at segs m a p.
Proof.
  intros m a p sl (bp & HB & Hz & Hn) HS Hm. exists bp, sl.
  assert (Lb : length bp = length p) by (rewrite <- Hz; unfold zs; symmetry; apply length_map).
  split; [|split; [exact Hz | split; [exact Hn | exact Hm]]].
  replace (bp ++ ZERO :: sl) with ((bp ++ [ZERO]) ++ sl) by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app. split; [exact HB|]. rewrite length_app, Lb. cbn [length].
  replace (a + Z.of_nat (length p + 1)) with (a + Z.of_nat (length p) + 1) by lia. exact HS.
Qed.

End Mem.
