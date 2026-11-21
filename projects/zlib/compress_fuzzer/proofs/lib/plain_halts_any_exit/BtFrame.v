(** * BtFrame — G3 groundwork: the tree builders never touch the symbol
      buffer or the bit writer.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [build_tree]/[gen_bitlen]/[build_bl_tree] end in setter chains applied
    to the ORIGINAL state — their internal loops only compute the setter
    ARGUMENTS — so each frame is destructs + reflexivity, no loop
    induction.  These are what let the flush's [compress_block] read the
    SAME [sym_buf]/[sym_next] the walk's [BufToks] talks about, and write
    onto the SAME [bw] the event snapshot recorded. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac tsimp :=
  cbn [ts_trees ts_maxcode ts_blcount ts_heap ts_heaplen ts_heapmax
       ts_depth ts_symbuf ts_symnext ts_optlen ts_statlen ts_matches ts_bw
       set_trees set_maxcode set_blcount set_heap set_heaplen set_heapmax
       set_depth set_symbuf set_symnext set_optlen set_statlen set_matches
       set_bw set_tree set_max
       fst snd].

Definition TFrame (s' s : TSt) : Prop :=
  ts_symbuf s' = ts_symbuf s
  /\ ts_symnext s' = ts_symnext s
  /\ ts_bw s' = ts_bw s
  /\ ts_matches s' = ts_matches s.

Lemma tframe_refl : forall s, TFrame s s.
Proof. intros s. repeat split. Qed.

Lemma tframe_trans : forall s3 s2 s1,
  TFrame s3 s2 -> TFrame s2 s1 -> TFrame s3 s1.
Proof.
  intros s3 s2 s1 (A1&A2&A3&A4) (B1&B2&B3&B4).
  repeat split; congruence.
Qed.

Lemma gen_bitlen_frame : forall k s, TFrame (gen_bitlen k s) s.
Proof.
  intros k s. unfold gen_bitlen. cbv zeta.
  destruct (gb_pass1 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as [[[[t2 blc1] ol1] sl1] ov].
  destruct (Z.eqb ov 0).
  - repeat split; tsimp; reflexivity.
  - destruct (gb_pass2 _ _ _ _ _ _ _ _ _) as [t3 ol2].
    repeat split; tsimp; reflexivity.
Qed.

Lemma build_tree_frame : forall k s, TFrame (build_tree k s) s.
Proof.
  intros k s. unfold build_tree. cbv zeta.
  destruct (bt_init _ _ _ _ _ _ _ _)
    as [[[[t0 hp0] dep0] hlen0] maxc0].
  destruct (bt_force2 _ _ _ _ _ _ _ _ _)
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1].
  destruct (bt_loop _ _) as [stf|]; [|apply tframe_refl].
  eapply tframe_trans.
  - (* the outer [set_tree k (gen_codes ...)] over [gen_bitlen k s1] *)
    instantiate (1 := gen_bitlen _ _).
    repeat split; tsimp; reflexivity.
  - eapply tframe_trans; [apply gen_bitlen_frame|].
    repeat split; tsimp; reflexivity.
Qed.

Lemma build_bl_tree_frame : forall s, TFrame (snd (build_bl_tree s)) s.
Proof.
  intros s. unfold build_bl_tree. cbv zeta. cbn [snd].
  eapply tframe_trans.
  - (* set_optlen over build_tree TK_BL s2 *)
    instantiate (1 := build_tree TK_BL _).
    repeat split; tsimp; reflexivity.
  - eapply tframe_trans; [apply build_tree_frame|].
    repeat split; tsimp; reflexivity.
Qed.

Print Assumptions build_tree_frame.
Print Assumptions build_bl_tree_frame.
