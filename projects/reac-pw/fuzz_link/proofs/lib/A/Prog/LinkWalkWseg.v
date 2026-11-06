(* reac-pw/fuzz_link, image A: every byte of a writable segment of the image's loaded segments `tfibsegs`
   (lib/A/AB1v.v, the segments LinkPaCheck.v certifies the listing against) is writable at ANY memory.

   Why a walk needs it: `abuf` / `au8arr` hold `awrange`, i.e. `writable_at segs m a` (YP09.v: `wview` shows the
   byte, either from the memory or from a writable segment's bytes). A callee's apost keeps the VALUES of the
   caller's bytes (link_amem.v `akept`) but not their presence, except above the allocator's ceiling; for a byte off
   the image presence follows from the kept value (YCbq.v apresent_transfer), but for an IMAGE byte (a program
   global of the journal's G, e.g. a caller's buffer in .bss) it does not. Such a byte is writable at every memory
   whenever its segment is writable and the segment's bytes show it — which is this file's computation: the same
   fact link_ajkit.v's `writable_at_of_wseg` / `LA_G_NL_writable` give for fixed ranges, here for the whole of the
   two writable segments [0xa1000, 0xa3000) and [0xa3000, 0x654000).

   - wseg_writable_gen: over any segments without overlaps, a byte of a writable segment whose bytes show it is
     writable at any memory.
   - wseg_writable_tfib: the instance at tfibsegs (the checker `wseg_chk`, run once per writable segment).
   - wseg_writable_tfib_rng: the same, as the address range of the two writable segments.

   The check of the big segment (5967872 bytes) runs in about 140 s of vm_compute (measured: 22 s
   per MiB; link_ajkit.v's per-byte `wseg_ok` costs 48 s per MiB, so it is not used for the whole segment).

   Proves no function (kind: segment lemma). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the checker ---- *)
Definition wseg_okb (cs : list PrimString.string) (o : Z) : bool :=
  match segment_byte_at cs (Z.to_N o) with Some _ => true | None => false end.

(* the Z.pos p offsets from i *)
Fixpoint wseg_chk (cs : list PrimString.string) (i : Z) (p : positive) : bool :=
  match p with
  | xH => wseg_okb cs i
  | xO q => wseg_chk cs i q && wseg_chk cs (i + Z.pos q) q
  | xI q => wseg_okb cs i && wseg_chk cs (i + 1) q && wseg_chk cs (i + 1 + Z.pos q) q
  end.

Lemma wseg_chk_sound : forall cs p i o, wseg_chk cs i p = true -> i <= o < i + Z.pos p -> wseg_okb cs o = true.
Proof.
  intros cs p. induction p as [q IH | q IH |]; intros i o Hc Ho; cbn [wseg_chk] in Hc.
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    destruct (Z.eq_dec o i) as [->|Hne]; [exact H1|].
    destruct (Z_lt_le_dec o (i + 1 + Z.pos q)) as [Hl|Hl].
    + apply (IH (i + 1)); [exact H2 | lia].
    + apply (IH (i + 1 + Z.pos q)); [exact H3 | lia].
  - apply andb_prop in Hc as [H1 H2].
    destruct (Z_lt_le_dec o (i + Z.pos q)) as [Hl|Hl].
    + apply (IH i); [exact H1 | lia].
    + apply (IH (i + Z.pos q)); [exact H2 | lia].
  - assert (o = i) as -> by lia. exact Hc.
Qed.

(* ---- segments without overlaps: find_segment answers the segment that holds the byte ---- *)
Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).

Fixpoint wseg_disj_b (segs : list Segment) : bool :=
  match segs with
  | [] => true
  | s :: r => forallb (fun s' => (seg_hi s <=? seg_lo s') || (seg_hi s' <=? seg_lo s)) r && wseg_disj_b r
  end.

Lemma find_segment_hit_in : forall segs s a, wseg_disj_b segs = true -> In s segs ->
  seg_lo s <= a < seg_hi s -> find_segment segs a 1 = Some s.
Proof.
  induction segs as [|s0 r IH]; intros s a Hd Hin Ha; [destruct Hin|].
  cbn [wseg_disj_b] in Hd. apply andb_prop in Hd as [Hall Hd].
  cbn [find_segment]. unfold seg_lo, seg_hi in *.
  destruct Hin as [<- | Hin].
  - replace ((Z.of_N (seg_base s0) <=? a) && (a + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
    reflexivity.
  - rewrite forallb_forall in Hall. pose proof (Hall s Hin) as Hs.
    apply orb_prop in Hs as [Hs | Hs]; apply Z.leb_le in Hs;
    (replace ((Z.of_N (seg_base s0) <=? a) && (a + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false
       by (symmetry; apply andb_false_iff;
           destruct (Z_lt_le_dec a (Z.of_N (seg_base s0))) as [H|H];
           [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; unfold seg_lo, seg_hi in *; lia]));
    exact (IH s a Hd Hin Ha).
Qed.

(* ---- the semantic step (YP09.v writable_at, the memory's wview) ---- *)
Lemma wseg_writable_gen : forall segs (m : word -> option byte) s a,
  wseg_disj_b segs = true -> In s segs -> seg_writable s = true ->
  seg_lo s <= a < seg_hi s -> 0 <= a < 2 ^ 64 -> wseg_okb (seg_bytes s) (a - seg_lo s) = true ->
  writable_at segs m a.
Proof.
  intros segs m s a Hd Hin Hw Ha Ha64 Hok. unfold writable_at, wview.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  rewrite (find_segment_hit_in segs s a Hd Hin Ha), Hw.
  unfold wseg_okb, seg_lo in Hok.
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (a - Z.of_N (seg_base s)))); [discriminate | discriminate Hok].
Qed.

(* ---- the instance ---- *)
Lemma tfib_disj : wseg_disj_b tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_shape : map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs =
  [(65536, 200704, false); (200704, 659456, false); (659456, 667648, true); (667648, 6635520, true)].
Proof. vm_compute. reflexivity. Qed.

Definition tfib_bytes (i : nat) : list PrimString.string :=
  match nth_error tfibsegs i with Some s => seg_bytes s | None => [] end.

Lemma tfib_chk2 : wseg_chk (tfib_bytes 2) 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_chk3 : wseg_chk (tfib_bytes 3) 0 5967872 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wseg_writable_tfib : forall (m : word -> option byte) a,
  (exists s, In s tfibsegs /\ seg_writable s = true /\
     Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) ->
  writable_at tfibsegs m a.
Proof.
  intros m a (s & Hin & Hw & Ha).
  pose proof tfib_shape as Hsh.
  destruct (In_nth_error tfibsegs s Hin) as (i & Hi).
  assert (Hlen : length tfibsegs = 4%nat) by (rewrite <- (length_map (fun s => (seg_lo s, seg_hi s, seg_writable s))), Hsh; reflexivity).
  assert (Hil : (i < 4)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hi; discriminate).
  assert (Hmi : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) i =
                Some (seg_lo s, seg_hi s, seg_writable s)) by (rewrite nth_error_map, Hi; reflexivity).
  rewrite Hsh in Hmi.
  assert (Hb : tfib_bytes i = seg_bytes s) by (unfold tfib_bytes; rewrite Hi; reflexivity).
  destruct i as [|[|[|[|i]]]]; [| | | | lia]; cbn [nth_error] in Hmi; injection Hmi as E1 E2 E3;
    unfold seg_lo, seg_hi in *;
    [rewrite Hw in E3; discriminate | rewrite Hw in E3; discriminate | |].
  - apply (wseg_writable_gen tfibsegs m s a tfib_disj Hin Hw); [unfold seg_lo, seg_hi; lia | lia |].
    rewrite <- Hb. apply (wseg_chk_sound _ 8192 0); [exact tfib_chk2 | unfold seg_lo; lia].
  - apply (wseg_writable_gen tfibsegs m s a tfib_disj Hin Hw); [unfold seg_lo, seg_hi; lia | lia |].
    rewrite <- Hb. apply (wseg_chk_sound _ 5967872 0); [exact tfib_chk3 | unfold seg_lo; lia].
Qed.

(* the same, as the address range of the two writable segments *)
Lemma wseg_writable_tfib_rng : forall (m : word -> option byte) a,
  0xa1000 <= a < 0x654000 -> writable_at tfibsegs m a.
Proof.
  intros m a Ha. apply wseg_writable_tfib.
  pose proof tfib_shape as Hsh.
  destruct (Z_lt_le_dec a 0xa3000) as [Hl|Hl].
  - destruct (nth_error tfibsegs 2) as [s|] eqn:Hs.
    + exists s. split; [exact (nth_error_In _ _ Hs)|].
      assert (Hm : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 2 =
                   Some (seg_lo s, seg_hi s, seg_writable s)) by (rewrite nth_error_map, Hs; reflexivity).
      rewrite Hsh in Hm. cbn [nth_error] in Hm. injection Hm as E1 E2 E3. unfold seg_lo, seg_hi in *.
      split; [congruence | lia].
    + exfalso. assert (Hn : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 2 = None)
        by (rewrite nth_error_map, Hs; reflexivity). rewrite Hsh in Hn. discriminate.
  - destruct (nth_error tfibsegs 3) as [s|] eqn:Hs.
    + exists s. split; [exact (nth_error_In _ _ Hs)|].
      assert (Hm : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 3 =
                   Some (seg_lo s, seg_hi s, seg_writable s)) by (rewrite nth_error_map, Hs; reflexivity).
      rewrite Hsh in Hm. cbn [nth_error] in Hm. injection Hm as E1 E2 E3. unfold seg_lo, seg_hi in *.
      split; [congruence | lia].
    + exfalso. assert (Hn : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 3 = None)
        by (rewrite nth_error_map, Hs; reflexivity). rewrite Hsh in Hn. discriminate.
Qed.
