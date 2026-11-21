(** * Bridge.DEmit.BrFbPre — pair D22, the tree phase: S5's trees at the branch
    point against RT's.

    S5 builds the literal and distance trees and then the bit-length tree
    ([FlushBlockModel.build_bl_tree_tfb]: [ov_X6], [ov_mb]); RT runs the same
    three steps ([rt_tp]).  The pairs are [BrBuildTree.br_build_tree] twice
    and [BrBlTree.br_build_bl_tree_x3]; their side conditions are the facts
    of S5's [RefDeflSafeE3.tree_phase], which S5 proves from [fb_entry].  The
    tree phase writes no bits and no symbols on either side, so the bit writer
    and the symbol buffer carry over. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel FlushBlockModel DeflateOverlay
  RefDeflSafeFB RefDeflSafeE3 RefDeflSafeE5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSendAll BrFbKit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrBuildTree BrBlTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module E3 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.

(** RT's tree phase. *)
Definition rt_tp (ts : RT.TSt) : Z * RT.TSt :=
  RT.build_bl_tree (RT.build_tree RT.TK_D (RT.build_tree RT.TK_L ts)).

(** Pair projections by rewriting.  A [cbn] leaves a conversion
    [snd (X6, mb) == mb] for the kernel, which unfolds S5's [tfb_mb]
    (declared [Strategy expand]) first and evaluates the tree phase. *)
Lemma fst_pair' : forall {A B} (a : A) (b : B), fst (a, b) = a.
Proof. reflexivity. Qed.
Lemma snd_pair' : forall {A B} (a : A) (b : B), snd (a, b) = b.
Proof. reflexivity. Qed.

Theorem br_fb_trees : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  trel (DO.ov_X6 s) (snd (rt_tp (RD.d_ts t))) /\ DO.ov_mb s = fst (rt_tp (RD.d_ts t))
  /\ TM.tree_lens (DO.ov_X6 s) /\ bw_rel (DO.ov_X6 s) (RT.ts_bw (snd (rt_tp (RD.d_ts t))))
  /\ RT.ts_symbuf (snd (rt_tp (RD.d_ts t))) = RT.ts_symbuf (RD.d_ts t)
  /\ RT.ts_symnext (snd (rt_tp (RD.d_ts t))) = RT.ts_symnext (RD.d_ts t).
Proof.
  intros s t pre_out pre_in last Hrel Hem Hlz Hlast.
  pose proof (fb_entry_of s t pre_out pre_in last Hrel Hem Hlz Hlast) as FE.
  pose proof (E3.tree_phase s (E5.OP s last FE)) as TP.
  destruct Hrel as (_ & _ & Hb & _ & Ht & _).
  (* the trees *)
  assert (HT0 : trel (FBM.tfb_X0 s) (RD.d_ts t)) by (apply (trel_nbw s); [apply nbw_X0 | exact Ht]).
  assert (HL0 : TM.tree_lens (FBM.tfb_X0 s)) by (apply (tree_lens_nbw s); [apply nbw_X0 | exact (ec_tl _ Hem)]).
  pose proof (BrBuildTree.br_build_tree _ _ DS.TL HT0 HL0 (E3.tp_h1 _ TP)) as T1.
  pose proof (BrBuildTree.br_build_tree_lens _ _ DS.TL HT0 HL0 (E3.tp_h1 _ TP)) as L1.
  cbn [tk_of] in T1.
  pose proof (BrBuildTree.br_build_tree _ _ DS.TD T1 L1 (E3.tp_h2 _ TP)) as T2.
  pose proof (BrBuildTree.br_build_tree_lens _ _ DS.TD T1 L1 (E3.tp_h2 _ TP)) as L2.
  cbn [tk_of] in T2.
  pose proof (E3.tp_h3 _ TP) as H3. pose proof (E3.tp_lmax _ TP) as Hlm. pose proof (E3.tp_h4 _ TP) as H4.
  pose proof (E3.tp_h7 _ TP) as H7. pose proof (E3.tp_dmax _ TP) as Hdm. pose proof (E3.tp_h8 _ TP) as H8.
  unfold DS.L_CODES in Hlm. unfold DS.D_CODES in Hdm.
  assert (HsL : scan_ok (DO.ov_X2 s) DS.TL (DS.ds_l_max_code (DO.ov_X2 s))).
  { split; [discriminate|]. cbn [TM.tsize]. rewrite H3. split; [lia|]. split; [lia|]. rewrite <- H3. exact H4. }
  assert (HmcL : DS.ds_l_max_code (DO.ov_X2 s) < DS.L_CODES) by (rewrite H3; unfold DS.L_CODES; lia).
  assert (HsD1 : scan_ok (DO.ov_X3 s) DS.TD (DS.ds_d_max_code (DO.ov_X3 s))).
  { split; [discriminate|]. cbn [TM.tsize]. rewrite H7. split; [lia|]. split; [lia|]. rewrite <- H7. exact H8. }
  pose proof (BrBlTree.br_build_bl_tree_x3 (DO.ov_X2 s) _ T2 L2 HsL HmcL HsD1 (E3.tp_h11 _ TP)) as (E & T6 & L6).
  change (DO.ov_X2 s) with (DT.build_tree (DT.build_tree (FBM.tfb_X0 s) DS.TL) DS.TD) in E, T6, L6.
  rewrite (FBM.build_bl_tree_tfb (FBM.tfb_X0 s)) in E, T6, L6.
  rewrite snd_pair' in E. rewrite fst_pair' in T6, L6.
  (* the frames *)
  destruct (rt_bbl_frame (RT.build_tree RT.TK_D (RT.build_tree RT.TK_L (RD.d_ts t)))) as (F1 & F2 & F3).
  destruct (BrBuildTree.rt_build_tree_frame RT.TK_L (RD.d_ts t)) as (G1 & G2 & _ & G4).
  destruct (BrBuildTree.rt_build_tree_frame RT.TK_D (RT.build_tree RT.TK_L (RD.d_ts t))) as (K1 & K2 & _ & K4).
  cbv zeta in G1, G2, G4, K1, K2, K4.
  pose proof (E5.X6n s last FE) as (P1 & P2 & P3 & P4 & _ & _ & P7 & _).
  unfold rt_tp. rewrite F1, F2, F3, K1, K2, K4, G1, G2, G4.
  split; [exact T6|]. split; [exact E|]. split; [exact L6|].
  split; [|split; reflexivity].
  destruct Hb as ((B1 & B2 & B3 & B4) & B5 & B6).
  rewrite (ec_pout _ Hem) in B3, B4. rewrite (ec_pending _ Hem) in B3, B4.
  unfold bw_rel, pend_rel. rewrite P1, P2, P3, P4, P7.
  split; [split; [lia | split; [lia | split; [exact B3 | exact B4]]] | split; assumption].
Qed.

Print Assumptions br_fb_trees.
