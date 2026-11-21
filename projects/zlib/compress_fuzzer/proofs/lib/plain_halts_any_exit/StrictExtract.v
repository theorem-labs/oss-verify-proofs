(** * StrictExtract — piece 1 of the header-segment selection walk
    (an earlier development run lane fork, dynsel parcel).

    (i)   [strict_extract]: the strict header decoder's success unpacks
          into the read chain + every guard boolean (pure destruct chain
          on Gap7Strict.decode_dynamic_tables_strict, :183-220).
    (ii)  [code_for_256_lens]: the missing-EOB connective — a code FOR
          symbol 256 forces a nonzero length at index 256.
    (iii) [accepts_transport]: build_accepts_b (t0 = tnone, zlens view)
          transports o_ret = 0 to the machine's it_model call at any
          window-agreeing lens array and any accumulator table, via
          ItGModelExt.it_model_lens_ext + Gap7Strict.it_model_tbl_ext.

    PA-EXPORTS: strict_extract, code_for_256_lens, accepts_transport,
    nth_error_firstn_some.
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff Inftrees DeflateSpec ItGModelExt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** (i) The unpacking. *)
Lemma strict_extract : forall bits lit dst r3,
  decode_dynamic_tables_strict bits = Some (lit, dst, r3) ->
  exists hlit r1 hdist r2 hclen r3a cl r4 ls,
    read_bits 5%nat bits = Some (hlit, r1)
    /\ read_bits 5%nat r1 = Some (hdist, r2)
    /\ read_bits 4%nat r2 = Some (hclen, r3a)
    /\ read_cl_lengths (Z.to_nat hclen + 4) r3a = Some (cl, r4)
    /\ valid_lengths_b cl 7%nat = true
    /\ Gap7Strict.build_accepts_b CT_CODES cl 7 = true
    /\ read_lengths cl (Z.to_nat hlit + 257 + (Z.to_nat hdist + 1))%nat r4
       = Some (ls, r3)
    /\ lit = firstn (Z.to_nat hlit + 257) ls
    /\ dst = skipn (Z.to_nat hlit + 257) ls
    /\ valid_lengths_b lit 15%nat = true
    /\ valid_lengths_b dst 15%nat = true
    /\ (length lit <= 286)%nat
    /\ (length dst <= 30)%nat
    /\ Gap7Strict.build_accepts_b CT_LENS lit 9 = true
    /\ Gap7Strict.build_accepts_b CT_DISTS dst 6 = true.
Proof.
  intros bits lit dst r3 H. revert H.
  unfold decode_dynamic_tables_strict. cbv zeta.
  destruct (read_bits 5%nat bits) as [[hlit r1]|] eqn:E1;
    [|intro H; discriminate H].
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2;
    [|intro H; discriminate H].
  destruct (read_bits 4%nat r2) as [[hclen r3a]|] eqn:E3;
    [|intro H; discriminate H].
  destruct (read_cl_lengths (Z.to_nat hclen + 4) r3a)
    as [[cl r4]|] eqn:E4; [|intro H; discriminate H].
  destruct (valid_lengths_b cl 7%nat
            && Gap7Strict.build_accepts_b CT_CODES cl 7)%bool eqn:G1;
    [|intro H; discriminate H].
  apply andb_true_iff in G1. destruct G1 as (G1a & G1b).
  destruct (read_lengths cl
              (Z.to_nat hlit + 257 + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|intro H; discriminate H].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257) ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257) ls) 15%nat
            && (length (firstn (Z.to_nat hlit + 257) ls) <=? 286)%nat
            && (length (skipn (Z.to_nat hlit + 257) ls) <=? 30)%nat
            && Gap7Strict.build_accepts_b CT_LENS
                 (firstn (Z.to_nat hlit + 257) ls) 9
            && Gap7Strict.build_accepts_b CT_DISTS
                 (skipn (Z.to_nat hlit + 257) ls) 6)%bool eqn:G2;
    [|intro H; discriminate H].
  intro H. injection H as HL HD HR. subst.
  apply andb_true_iff in G2; destruct G2 as (G2 & Hacd).
  apply andb_true_iff in G2; destruct G2 as (G2 & Hacl).
  apply andb_true_iff in G2; destruct G2 as (G2 & Hl30).
  apply andb_true_iff in G2; destruct G2 as (G2 & Hl286).
  apply andb_true_iff in G2; destruct G2 as (Hvl & Hvd).
  exists hlit, r1, hdist, r2, hclen, r3a, cl, r4, ls.
  repeat split;
    first [ exact E1 | exact E2 | exact E3 | exact E4 | exact G1a
          | exact G1b | exact E5 | reflexivity | assumption
          | now apply Nat.leb_le ].
Qed.

(** (ii) A tiny nth_error/firstn connective, then the EOB fact. *)
Lemma nth_error_firstn_some : forall (l : list nat) n k x,
  nth_error (firstn n l) k = Some x -> nth_error l k = Some x.
Proof.
  intros l n k. revert l n.
  induction k as [|k IH]; intros l n x H;
    destruct n as [|n]; try discriminate;
    destruct l as [|y l]; try discriminate.
  - exact H.
  - cbn [firstn nth_error] in H. cbn [nth_error]. exact (IH l n x H).
Qed.

Lemma code_for_256_lens : forall (lit ls : list nat) (nlit : nat) cw,
  lit = firstn nlit ls ->
  (256 < nlit)%nat ->
  code_for lit 15%nat 256%nat = Some cw ->
  zlens ls 256 <> 0.
Proof.
  intros lit ls nlit cw Hlit Hn Hc.
  unfold code_for in Hc.
  destruct (nth_error lit 256) as [len|] eqn:En; [|discriminate].
  destruct ((len =? 0)%nat || (15 <? len)%nat)%bool eqn:Ez; [discriminate|].
  apply orb_false_iff in Ez. destruct Ez as (Ez & _).
  apply Nat.eqb_neq in Ez.
  subst lit.
  pose proof (nth_error_firstn_some ls nlit 256 len En) as En'.
  unfold zlens.
  change (Z.to_nat 256) with 256%nat.
  rewrite (nth_error_nth ls 256%nat 0%nat En').
  cbn. lia.
Qed.

(** (iii) The accept transport: guard at (tnone, zlens) => machine site. *)
Lemma accepts_transport : forall ty (L : list nat) root0 lensM codes t0M o,
  Gap7Strict.build_accepts_b ty L root0 = true ->
  codes = Z.of_nat (length L) ->
  0 < codes ->
  arr_eq_on lensM (zlens L) 0 codes ->
  it_model ty lensM codes root0 t0M = Some o ->
  o_ret o = 0.
Proof.
  intros ty L root0 lensM codes t0M o HB Hcodes Hpos Hag HM.
  unfold Gap7Strict.build_accepts_b in HB.
  destruct (it_model ty (Gap7Strict.lens_of_list L) (Z.of_nat (length L))
              root0 tnone) as [o0|] eqn:E0; [|discriminate].
  apply Z.eqb_eq in HB.
  rewrite (it_model_lens_ext ty lensM (zlens L) codes root0 t0M Hpos Hag)
    in HM.
  pose proof (it_model_tbl_ext ty (zlens L) codes root0 t0M tnone) as T.
  rewrite HM in T.
  rewrite <- Hcodes in E0.
  change (Gap7Strict.lens_of_list L) with (zlens L) in E0.
  rewrite E0 in T.
  destruct T as (Tret & _ & _). lia.
Qed.

Set Printing Width 2000.
Print Assumptions strict_extract.
Print Assumptions code_for_256_lens.
Print Assumptions accepts_transport.
