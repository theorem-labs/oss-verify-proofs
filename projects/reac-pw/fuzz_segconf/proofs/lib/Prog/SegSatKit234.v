(** reac-pw/fuzz_segconf: the build-independent part of the kit for the satisfiability lemmas of the premises of
    contract families F2, F3 and F4 (lib/Prog/*_c.v, lib/U/Prog/*_c.v, Prog/seg_cuts.v and U/Prog/seg_cuts.v of
    commit aca5136e2baf), on top of Prog/SegSatKit.v (canonical images, encoding checkers, the region
    memory RMEM, sat_goal). The per-build parts are Prog/SegSat234.v (plain) and U/Prog/SegSat234.v (UBSan); the
    lemmas are in Prog/sat/ and U/Prog/sat/.

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    What it adds to SegSatKit.v.
    - Memory facts the printing and the VLAN contracts need: mem_inv of a region memory whose regions miss every
      read-only segment (the errno cell tp - 164 lies in .bss, inside the image), MemNorm.task_mem (LPS State.v:
      TASK_SIZE = 0x800000000000; every region lies below it), blk_noimg from segments_reserved by computation, a C
      string with its slack read from the image (.rodata literals), rw_cells of any cell list, frm0 of fcsr 0,
      apart_all and In of a format by computation.
    - The real values: the input INP2 (cap 4, flags 1, two files T1 and T2; T1 a drop-in under label byte 3, T2 the
      hand-written file), its states after each turn from seg_spec.seg_run / seg_after, and the states inside the
      functions at the call sites the lemmas use, all by SegModel's own functions.
    - The tactic sat2, which discharges a premise conjunct by conjunct (SegSatKit.sat_goal plus the cases above). *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec SegSatKit.
Import ListNotations.
Open Scope Z_scope.

(** ** 1. Memory facts *)

(** No region of rs meets a read-only segment of segs. *)
Definition ro_clear (segs : list Segment) (rs : list region) : bool :=
  forallb (fun r => forallb (fun s => seg_writable s || (fst r + Z.of_nat (length (snd r)) <=? Z.of_N (seg_base s)) ||
                                      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) segs) rs.

Lemma mem_inv_ro_clear : forall segs rs, ro_clear segs rs = true -> mem_inv segs (RMEM rs).
Proof.
  intros segs rs H a b Hm. unfold RMEM in Hm.
  destruct (rmem rs (bv_unsigned a)) as [z|] eqn:E1; [|discriminate].
  destruct (rmem_some_in rs (bv_unsigned a) z E1) as (a0 & zl & Hin & Hx).
  unfold ro_addr. destruct (find_segment segs (bv_unsigned a) 1) as [s|] eqn:F; [|reflexivity].
  destruct (fs_spec _ _ _ _ F) as (Hs & H1 & H2).
  unfold ro_clear in H. rewrite forallb_forall in H. specialize (H _ Hin). rewrite forallb_forall in H.
  specialize (H _ Hs). cbn [fst snd] in H.
  destruct (seg_writable s); [reflexivity|]. cbn [orb] in H.
  apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(** Every region ends at or below TASK_SIZE. *)
Definition below_task (rs : list region) : bool :=
  forallb (fun r => fst r + Z.of_nat (length (snd r)) <=? TASK_SIZE) rs.

Lemma task_mem_below : forall segs rs, below_task rs = true ->
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.MemNorm.task_mem segs (RMEM rs).
Proof.
  intros segs rs H a b Hm. unfold RMEM in Hm.
  destruct (rmem rs (bv_unsigned a)) as [z|] eqn:E1; [|discriminate].
  destruct (rmem_some_in rs (bv_unsigned a) z E1) as (a0 & zl & Hin & Hx).
  right. unfold below_task in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn [fst snd] in H.
  apply Z.leb_le in H. lia.
Qed.
(** The UBSan tree's copy of MemNorm states task_mem with the same text. *)
Lemma task_mem_below_U : forall segs rs, below_task rs = true ->
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.MemNorm.task_mem segs (RMEM rs).
Proof. exact task_mem_below. Qed.

(** The n bytes at a miss every reserved segment. *)
Definition noimgb (segs : list Segment) (a n : Z) : bool :=
  forallb (fun s => (a + n <=? bv_unsigned (fst s)) || (bv_unsigned (fst s) + bv_unsigned (snd s) <=? a))
    (segments_reserved segs).

Lemma blk_noimg_of : forall segs a n, noimgb segs a n = true -> blk_noimg segs a n.
Proof.
  intros segs a n H i Hi s Hs Hc. unfold noimgb in H. rewrite forallb_forall in H. specialize (H s Hs).
  apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma bytes_at_firstn : forall segs m p bs k, bytes_at segs m p bs -> bytes_at segs m p (firstn k bs).
Proof.
  intros segs m p bs k (H1 & H2 & H3). split; [exact H1|]. rewrite length_firstn. split; [lia|].
  intros i Hi. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec i k) as [_|]; [|lia]. apply H3. lia.
Qed.

(** A C string with its slack from any byte list L the memory holds at p. *)
Lemma cstr_of_bytes : forall segs m p L s,
  bytes_at segs m p (zb L) -> forallb byte_okb L = true -> nulfreeb s = true ->
  leqb (firstn (S (length s)) L) (s ++ [0]) = true -> (length s + 8 <= length L)%nat ->
  cstr_at segs m p s.
Proof.
  intros segs m p L s HB Hr Hn Heq Hl.
  set (sl := skipn (S (length s)) (firstn (length s + 8) L)).
  assert (E8 : firstn (length s + 8) L = s ++ 0 :: sl).
  { rewrite <- (firstn_skipn (S (length s)) (firstn (length s + 8) L)). fold sl.
    rewrite firstn_firstn. replace (Nat.min (S (length s)) (length s + 8)) with (S (length s)) by lia.
    apply leqb_eq in Heq. rewrite Heq, <- app_assoc. reflexivity. }
  assert (Hsl : length sl = 7%nat) by (unfold sl; rewrite length_skipn, length_firstn; lia).
  assert (Hrs : forallb byte_okb s = true).
  { rewrite <- (firstn_skipn (length s + 8) L), E8, !forallb_app in Hr.
    apply andb_true_iff in Hr as [Hr _]. apply andb_true_iff in Hr as [Hr _]. exact Hr. }
  exists (zb s), (zb sl). split; [|split; [|split]].
  - pose proof (bytes_at_firstn segs m p (zb L) (length s + 8) HB) as B.
    unfold zb in B. rewrite firstn_map, E8, map_app in B. exact B.
  - apply zs_zb. exact Hrs.
  - apply nulfreeb_ok. exact Hn.
  - unfold zb. rewrite length_map, Hsl. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
    lia.
Qed.

(** The n bytes of the image at p, as byte values (0 where the image has none: img_zb then fails). *)
Definition img_bytes (segs : list Segment) (p : Z) (n : nat) : list Z :=
  map (fun i => match seg_rom segs (wa (p + Z.of_nat i)) with Some b => bv_unsigned b | None => 0 end) (seq 0 n).

(** A C string and its slack read from the image (a .rodata literal), no region over it. *)
Lemma cstr_img : forall segs rs p s n,
  rclear rs p (p + Z.of_nat n) = true -> img_zb segs p (img_bytes segs p n) = true ->
  leqb (firstn (S (length s)) (img_bytes segs p n)) (s ++ [0]) = true -> nulfreeb s = true ->
  (length s + 8 <= n)%nat -> 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> cstr_at segs (RMEM rs) p s.
Proof.
  intros segs rs p s n Hc Hi Heq Hn Hl Hp Hpn.
  assert (Hlen : length (img_bytes segs p n) = n) by (unfold img_bytes; rewrite length_map, length_seq; reflexivity).
  assert (Hr : forallb byte_okb (img_bytes segs p n) = true)
    by (unfold img_zb in Hi; apply andb_true_iff in Hi as [Hi _]; exact Hi).
  apply (cstr_of_bytes segs (RMEM rs) p (img_bytes segs p n) s); [| exact Hr | exact Hn | exact Heq | lia].
  apply bytes_img.
  - unfold zb. rewrite length_map, Hlen. exact Hc.
  - rewrite zs_zb by exact Hr. exact Hi.
  - exact Hp.
  - unfold zb. rewrite length_map, Hlen. exact Hpn.
Qed.

Lemma rw_cells_of : forall segs m A cs, cells_wf cs -> bytes_at segs m A (cells_bytes cs) ->
  wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros segs m A cs H1 H2 H3. split; [split; assumption | exact H3]. Qed.

(** The n bytes the first region holding A has from A on (the witness of an `exists bs, rw_cells .. [CB n bs]`, of
    blk_slack and of pf_nm_at); one slice of one region, so its computation is linear in the region's size. *)
Fixpoint rbytes (rs : list region) (A : Z) (n : nat) : list byte :=
  match rs with
  | [] => repeat ZERO n
  | (a, zl) :: r =>
      if (a <=? A) && (A <? a + Z.of_nat (length zl)) then zb (firstn n (skipn (Z.to_nat (A - a)) zl))
      else rbytes r A n
  end.

Lemma frm0_zero : frm0 (Z_to_bv 32 0).
Proof. vm_compute. reflexivity. Qed.

(** A range no region covers reads as the image (the .data.rel.ro tables: cat_img, m_file's words_img). *)
Lemma img_range_clear : forall segs rs lo hi, rclear rs lo hi = true -> 0 <= lo -> hi <= 2 ^ 64 ->
  forall a, lo <= a < hi -> mrd segs (RMEM rs) (wa a) = seg_rom segs (wa a).
Proof.
  intros segs rs lo hi Hc H1 H2 a Ha. apply mrd_RMEM_none; [|lia]. apply (rmem_clear rs lo hi); [exact Hc | lia].
Qed.

Definition apart_allb (a n : Z) (W : list ivl) : bool :=
  forallb (fun iv => (a + n <=? fst iv) || (snd iv <=? a)) W.
Lemma apart_all_of : forall a n W, apart_allb a n W = true -> apart_all a n W.
Proof.
  intros a n W H. unfold apart_allb in H. unfold apart_all. rewrite Forall_forall. intros iv Hin.
  rewrite forallb_forall in H. specialize (H iv Hin). unfold apart.
  apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; [left | right]; lia.
Qed.

Lemma In_of_existsb : forall (f : list Z) (l : list (list Z)), existsb (leqb f) l = true -> In f l.
Proof.
  intros f l H. apply existsb_exists in H as (x & Hx & E). apply leqb_eq in E. subst. exact Hx.
Qed.

(** ** 2. The real values *)

(** The two texts. T1, the drop-in under the label byte 3 (label "reac-pw.conf.d/3-x.conf"): one segment eth0.5
    (role box, model s1608, ignore no) and a knock line. T2, the hand-written file (the last, read by
    reac_segconf_parse and m_file(m, text, NULL)): a second segment eth1.7 with role master and model s0808 (so both
    cross checks refuse the model: F_xmodel), ignore no, and a knock line. Each knock line is refused by both
    parsers: three refusals in all, each kept. *)
Definition T1 : list Z := sb "[segment eth0.5]
role = box
model = s1608
ignore = no
knock = 1
"%string.
Definition T2 : list Z := sb "[segment eth1.7]
role = master
model = s0808
ignore = no
knock = 2
"%string.
(** The first file's label byte (bit 7 clear, not 0: the snprintf label). *)
Definition LB1 : Z := 3.
(** The fuzz input: cap byte 4 (cap 4), flags 1 (the "enp1s0" VLAN seed), nfiles byte 1 (two files), then each
    file record: its label byte, its 16-bit little-endian length, its bytes (fuzz_segconf.c:583-600,
    SegModel.decode). *)
Definition D2 : list Z :=
  [4; 1; 1; LB1; Z.of_nat (length T1); 0] ++ T1 ++ [0; Z.of_nat (length T2); 0] ++ T2.
Definition INP2 : list byte := zb D2.
Definition P2 : payload := seg_pay INP2.
Definition LAB1 : list Z := snprintf_s 40 F_label [AI LB1].

Lemma P2_eq : P2 = Payload 4 1 [File LB1 T1; File 0 T2].
Proof. vm_compute. reflexivity. Qed.
Lemma INP2_len : length INP2 = 140%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma LAB1_eq : LAB1 = sb "reac-pw.conf.d/3-x.conf"%string.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_label_INP2 : seg_label INP2 0 = Some LAB1.
Proof. vm_compute. reflexivity. Qed.
(** No check of the harness aborts on this input: the reader's answers equal the model's. *)
Lemma harness_ok_P2 : harness_ok P2 = true.
Proof. vm_compute. reflexivity. Qed.

(** The states between the turns (seg_spec.seg_run / seg_after): after turn 0 (the drop-in T1) and after turn 1
    (the last file T2, m_cross and reac_segconf_parse), which is the whole run. *)
Definition ST1 : rconf * mconf * bool := seg_run INP2 1.
Definition ST2 : rconf * mconf * bool := seg_after INP2 1.
Definition RC1 : rconf := seg_rc ST1.
Definition MC1 : mconf := seg_mc ST1.
Definition RC2 : rconf := seg_rc ST2.
Definition MC2 : mconf := seg_mc ST2.
Lemma run_P2 : run P2 = ST2.
Proof. vm_compute. reflexivity. Qed.
(** Both states are nonempty: two segments, three refusals kept (the two knocks and cross_check's F_xmodel). *)
Lemma RC2_shape : length (rc_seg RC2) = 2%nat /\ length (rc_refusal RC2) = 3%nat /\ rc_refused RC2 = 3.
Proof. vm_compute. repeat split. Qed.
Lemma MC2_shape : length (mc_seg MC2) = 2%nat /\ length (mc_kept MC2) = 3%nat /\ mc_refused MC2 = 3.
Proof. vm_compute. repeat split. Qed.

(** The lines of each text. *)
Definition L1 : list (list Z) := lines T1.
Definition L2 : list (list Z) := lines T2.

(** Inside reac_segconf_parse_file, turn 0 (rconf0, label LAB1) and turn 1 (RC1, under reac_segconf_parse:
    "reac-pw.conf"): the state after the first k lines (pf_pieces_spec.pf_spine). *)
Definition PF1 (k : nat) : rconf * option nat * list Z := pf_spine rconf0 (Some LAB1) (firstn k L1).
Definition PF2 (k : nat) : rconf * option nat * list Z := pf_spine RC1 (Some S_base) (firstn k L2).
(** cross_check's argument: c after the last file's parse_file. *)
Definition RCX : rconf := fst (r_parse_file RC1 T2 (Some S_base)).
(** Inside m_file, turn 0 (mconf0, label LAB1) and turn 1 (MC1, no label): the state after the first k lines. *)
Definition mf_start (mc : mconf) (lab : option (list Z)) : mconf :=
  MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1)
    (snprintf_s 96 F_s [AS (match lab with Some l => l | None => S_base end)]).
Definition MF1 (k : nat) : mconf * option nat := m_lines (mf_start mconf0 (Some LAB1), None) 0 (firstn k L1).
Definition MF2 (k : nat) : mconf * option nat := m_lines (mf_start MC1 None, None) 0 (firstn k L2).
(** The VLAN tables: vlan_init of the payload (enp1s0, 33), and reac_segconf_declared's walk over RC2. *)
Definition CAP2 : Z := p_cap P2.
Definition TB0 : list (list Z * Z) := vlan_init P2.
(** The table after the first add of the walk (eth0, 5) and after the whole walk. *)
Definition TB1 : list (list Z * Z) := snd (r_decl_go (firstn 1 (rc_seg RC2)) TB0 CAP2 0).
Definition GOT2 : Z * list (list Z * Z) := r_declared RC2 TB0 CAP2.
Lemma TB_shape : TB0 = [(S_enp, 33)] /\ TB1 = [(S_enp, 33); (sb "eth0"%string, 5)] /\
  GOT2 = (2, [(S_enp, 33); (sb "eth0"%string, 5); (sb "eth1"%string, 7)]).
Proof. vm_compute. repeat split. Qed.

(** Addresses (16-aligned, above both images, below the stack region): the input block p, the two text blocks
    (fuzz_str's malloc(n + 1)). SegSatKit's C0, M0, TAB0, MT0 hold c, m, tab, mt; its S_TOP and LO bound the
    stack. *)
Definition INPA : Z := 0x7fffeff40000.
Definition TX1A : Z := 0x7fffeff50000.
Definition TX2A : Z := 0x7fffeff60000.

(** Canonical regions: a text block (the text, its NUL, 7 slack bytes the frame's block_slack_present gives), the
    m block with the 4 slack bytes after it (blk_slack), the input block with slack. *)
Definition txt_img (s : list Z) : list Z := s ++ [0] ++ zrep 7.
Definition mblk_img (pend : bool) (mc : mconf) : list Z := mconf_imgp pend mc ++ zrep 4.
Definition inp_img : list Z := D2 ++ zrep 8.
(** A frame cell holding the 8 bytes of v; the 8-byte words ws (saved_at's order). *)
Definition le8z (v : Z) : list Z := zs (le8 (Z_to_bv 64 v)).
Definition wimg (ws : list word) : list Z := zs (concat (map le8 ws)).
(** A register file from a list of (register number, value) pairs; every other register holds 0 (the cut
    predicates fix only the registers they name). *)
Definition rval (l : list (Z * Z)) (r : Z) : word :=
  Z_to_bv 64 (match find (fun e => fst e =? r) l with Some e => snd e | None => 0 end).
Definition rmap (l : list (Z * Z)) : bvmap 5 word :=
  mkR (rval l 1) (rval l 2) (rval l 3) (rval l 4) (rval l 5) (rval l 6) (rval l 7) (rval l 8) (rval l 9)
      (rval l 10) (rval l 11) (rval l 12) (rval l 13) (rval l 14) (rval l 15) (rval l 16) (rval l 17) (rval l 18)
      (rval l 19) (rval l 20) (rval l 21) (rval l 22) (rval l 23) (rval l 24) (rval l 25) (rval l 26) (rval l 27)
      (rval l 28) (rval l 29) (rval l 30) (rval l 31).

(** ** 3. Tactics *)

Ltac zside2 :=
  lazymatch goal with
  | |- (_ <= _)%nat => apply Nat.leb_le; vm_compute; reflexivity
  | |- (_ < _)%nat => apply Nat.ltb_lt; vm_compute; reflexivity
  | |- (_ <= _ < _)%nat => split; zside2
  | |- _ => zside
  end.

(** One conjunct of a premise over RMEM rs; HB : segs_below segs IMG_END = true for the build's segs. *)
Ltac sat2 HB :=
  lazymatch goal with
  | |- _ /\ _ => split; sat2 HB
  | |- mem_inv _ (RMEM _) => apply mem_inv_ro_clear; vm_compute; reflexivity
  | |- OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.MemNorm.task_mem _ (RMEM _) =>
      apply task_mem_below; vm_compute; reflexivity
  | |- OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.MemNorm.task_mem _ (RMEM _) =>
      apply task_mem_below_U; vm_compute; reflexivity
  | |- blk_noimg _ _ _ => apply blk_noimg_of; vm_compute; reflexivity
  | |- frm0 _ => vm_compute; reflexivity
  | |- apart_all _ _ _ => apply apart_all_of; vm_compute; reflexivity
  | |- In _ REFUSE_FORMATS => apply In_of_existsb; vm_compute; reflexivity
  | |- saved_at _ _ _ _ => unfold saved_at; sat2 HB
  | |- va_args_ok _ _ _ _ _ => cbn [va_args_ok va_arg_ok]; sat2 HB
  | |- ocstr_at _ _ _ (Some _) => unfold ocstr_at; split; [zside | sat2 HB]
  | |- ocstr_at _ _ _ None => reflexivity
  | |- exists g : word, bytes_at _ (RMEM _) _ (le8 g) => exists (Z_to_bv 64 0); sat2 HB
  | |- exists f, bytes_at _ (RMEM ?rs) ?a f /\ cstr_enc ?n _ f =>
      exists (rbytes rs a n); split; [sat2 HB | apply cstr_encb_ok; vm_compute; reflexivity]
  | |- blk_slack _ (RMEM ?rs) ?a ?n =>
      exists (rbytes rs (a + n) (Z.to_nat ((- (a + n)) mod 8))); split; [sat2 HB | zside]
  | |- forall x, ?lo <= x < ?hi -> mrd ?segs (RMEM ?rs) (wa x) = seg_rom _ (wa x) =>
      apply (img_range_clear segs rs lo hi); zside
  | |- rw_cells _ (RMEM _) _ _ =>
      apply rw_cells_of; [cbn [cells_wf cell_wf]; repeat split; try (vm_compute; reflexivity) | sat2 HB | sat2 HB]
  | |- exists bs, rw_cells _ (RMEM ?rs) ?A [CB ?n _] => exists (rbytes rs A n); sat2 HB
  | |- cstr_at ?segs (RMEM ?rs) ?p ?s =>
      first [ sat_goal HB | solve [apply (cstr_img segs rs p s (length s + 8)); zside2] ]
  | |- (_ <= _)%nat => zside2
  | |- (_ < _)%nat => zside2
  | |- _ => sat_goal HB
  end.
