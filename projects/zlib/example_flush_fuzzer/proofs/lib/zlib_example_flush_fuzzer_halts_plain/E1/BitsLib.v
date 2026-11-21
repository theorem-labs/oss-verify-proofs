(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout FillWinMem TreeMem BitsModel BitsModel2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Section WithImage.
Variable segs : list Segment.
Variables AL AD AB : Z.
Local Abbreviation dscal := (dsl_scalars segs AL AD AB).
Local Abbreviation darr := (dsl_arrays segs).


Lemma arrays_write_scalar : forall m S s (b : Z) bs,
  dsl_arrays segs m S s -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 -> 0 <= b ->
  b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (b + Z.of_nat (length bs) <= S + 212 \/ S + 5884 <= b) ->
  dsl_arrays segs (wbytes m (zw b) bs) S s.
Proof.
  intros m S s b bs H HS0 HS1 Hb0 Hb1 Hd. unfold dsl_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  repeat split;
    (eapply cells_write_other; [eassumption | cbn; lia | lia | lia | cbn; lia | lia | lia]).
Qed.


Section Rel.
Variables (F : franges) (mem0 : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z).
Local Abbreviation PB := (p_pending_buf p).

Definition BR (m : word -> option byte) (s : deflate_state) : Prop :=
  dscal m S p s
  /\ darr m S s
  /\ tree_lens s
  /\ cells segs m PB 1 1 PBL (arr_get (ds_pending_buf s))
  /\ arr_len (ds_pending_buf s) = PBL
  /\ agree_out F mem0 m
  /\ mapped m S dsl_SIZE /\ mapped m PB PBL
  /\ (forall x, mem0 x <> None -> m x <> None).

Definition BRx (m : word -> option byte) (s : deflate_state) : Prop :=
  exists j, BR m (set_bi_buf s j).

Definition BRH : Prop :=
  (0 <= S /\ S + dsl_SIZE <= 2 ^ 63) /\ (0 <= PB /\ PB + PBL <= 2 ^ 63) /\ (S + dsl_SIZE <= PB \/ PB + PBL <= S)
  /\ sub_franges F (S + 40) 8 /\ sub_franges F (S + 5936) 2 /\ sub_franges F (S + 5940) 4 /\ sub_franges F PB PBL.
Hypothesis HL : BRH.

Lemma BR_init : forall s,
  dscal mem0 S p s -> darr mem0 S s -> tree_lens s -> dsl_pendA segs mem0 p s ->
  arr_len (ds_pending_buf s) = PBL -> mapped mem0 S dsl_SIZE -> mapped mem0 PB PBL -> BR mem0 s.
Proof.
  intros s A B C D E G H. unfold BR, dsl_pendA in *. rewrite E in D.
  repeat (split; [assumption|]). split; [apply agree_out_refl|]. split; [assumption|]. split; [assumption|]. auto.
Qed.


Lemma BR_eqst : forall m s1 s2, BR m s1 -> s1 = s2 -> BR m s2.
Proof. intros m s1 s2 H <-. exact H. Qed.


Lemma BR_out : forall m s, BR m s ->
  dscal m S p s /\ darr m S s /\ tree_lens s /\ dsl_pendA segs m p s /\ agree_out F mem0 m
  /\ mapped m S dsl_SIZE /\ mapped m PB PBL /\ (forall x, mem0 x <> None -> m x <> None).
Proof.
  intros m s (A & B & C & D & E & G & H & I & J). unfold dsl_pendA. rewrite E. tauto.
Qed.

Lemma BR_cells : forall m s, BR m s ->
  cell segs m (S + 40) 8 (ds_pending s) /\ cell segs m (S + 16) 8 PB
  /\ cell segs m (S + 5936) 2 (ds_bi_buf s) /\ cell segs m (S + 5940) 4 (ds_bi_valid s)
  /\ cells segs m PB 1 1 PBL (arr_get (ds_pending_buf s)).
Proof.
  intros m s (A & _ & _ & D & _).
  split; [exact (dsl_pending _ _ _ _ _ _ _ _ A)|]. split; [exact (dsl_pending_buf _ _ _ _ _ _ _ _ A)|].
  split; [exact (dsl_bi_buf _ _ _ _ _ _ _ _ A)|]. split; [exact (dsl_bi_valid _ _ _ _ _ _ _ _ A)|]. exact D.
Qed.



Local Ltac other9 A :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact A.

Lemma BR_st_pending : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 40)) (Z_to_le_bytes 8 v)) (set_pending s v).
Proof.
  intros m s v (A & B & C & D & E & G & H & I & J).
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  split; [apply dsl_upd_pending; unfold dsl_SIZE; try lia; exact A|].
  split; [apply arrays_write_scalar; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [exact C|].
  split; [change (ds_pending_buf (set_pending s v)) with (ds_pending_buf s); other9 D|].
  split; [exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | exact HF40]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_st_bi_buf : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5936)) (Z_to_le_bytes 2 v)) (set_bi_buf s (v mod 2 ^ 16)).
Proof.
  intros m s v (A & B & C & D & E & G & H & I & J).
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  split.
  { rewrite <- (SymExec.Z_to_le_bytes_mod 2 v). change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16).
    apply dsl_upd_bi_buf; unfold dsl_SIZE; try lia; exact A. }
  split; [apply arrays_write_scalar; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [exact C|].
  split; [change (ds_pending_buf (set_bi_buf s ?a)) with (ds_pending_buf s); other9 D|].
  split; [exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | exact HF5936]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_st_bi_valid : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5940)) (Z_to_le_bytes 4 v)) (set_bi_valid s v).
Proof.
  intros m s v (A & B & C & D & E & G & H & I & J).
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  split; [apply dsl_upd_bi_valid; unfold dsl_SIZE; try lia; exact A|].
  split; [apply arrays_write_scalar; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [exact C|].
  split; [change (ds_pending_buf (set_bi_valid s v)) with (ds_pending_buf s); other9 D|].
  split; [exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | exact HF5940]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

(* 1.4: bi_used (int, 5944) is a junk range of the layout (DSLayout.dsl_upd_bi_used). A store
   there keeps BR and the model state when the frame covers it; bi_windup writes it inline at 1.4. *)
Lemma BR_st_bi_used : forall m s v,
  sub_franges F (S + 5944) 4 ->
  BR m s -> BR (wbytes m (zw (S + 5944)) (Z_to_le_bytes 4 v)) s.
Proof.
  intros m s v HF5944 (A & B & C & D & E & G & H & I & J).
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  split; [apply dsl_upd_bi_used; unfold dsl_SIZE; try lia; exact A|].
  split; [apply arrays_write_scalar; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [exact C|].
  split; [other9 D|].
  split; [exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | exact HF5944]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_st_pb : forall m s (a i c : Z),
  BR m s -> a = PB + i -> 0 <= i < PBL ->
  BR (wbytes m (zw a) (Z_to_le_bytes 1 c)) (set_pending_buf s (arr_set (ds_pending_buf s) i (wrap8 c))).
Proof.
  intros m s a i c (A & B & C & D & E & G & H & I & J) -> Hi.
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  split.
  { apply (proj2 (scalars_set_pending_buf _ _ _ _ _ _ _ _ _)).
    apply dsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia). exact A. }
  split.
  { change (dsl_arrays segs ?M S (set_pending_buf s ?x)) with (dsl_arrays segs M S s).
    apply arrays_write_other; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia). exact B. }
  split; [unfold tree_lens in *; cbn; exact C|].
  split.
  { change (ds_pending_buf (set_pending_buf s ?x)) with x.
    intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite E.
    pose proof (cells_write_cell segs m PB 1 1 PBL (arr_get (ds_pending_buf s)) i c D
                  ltac:(cbn; lia) Hi ltac:(lia) ltac:(lia) j Hj) as Hc0.
    cbn beta in Hc0. replace (PB + 1 * i) with (PB + i) in Hc0 by lia.
    destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i PBL); cbn [andb]; subst; try lia;
      try exact Hc0.
    apply (proj1 (cell_mod segs _ _ 1 (wrap8 c))). apply (proj2 (cell_mod segs _ _ 1 c)) in Hc0.
    rewrite wrap8_mod'. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in *.
    rewrite Z.mod_mod by lia. exact Hc0. }
  split; [change (ds_pending_buf (set_pending_buf s ?x)) with x; rewrite arr_len_set; exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G |]|].
  { intros x Hx. apply HFPB. cbn in Hx. lia. }
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_st_other : forall m s (b : Z) bs,
  BR m s -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + dsl_SIZE <= b \/ b + Z.of_nat (length bs) <= S) ->
  (PB + PBL <= b \/ b + Z.of_nat (length bs) <= PB) ->
  sub_franges F b (Z.of_nat (length bs)) ->
  BR (wbytes m (zw b) bs) s.
Proof.
  intros m s b bs (A & B & C & D & E & G & H & I & J) Hb0 Hb1 HdS HdP HF.
  destruct HL as (HS & HPB & Hdisj & _). unfold BR, dsl_SIZE in *.
  split.
  { apply dsl_scalars_frame; unfold dsl_SIZE; try lia. exact A. }
  split; [apply arrays_write_other; unfold dsl_SIZE; try lia; exact B|].
  split; [exact C|].
  split.
  { destruct (Z_le_gt_dec PBL 0) as [Hz|Hz].
    - intros i Hi. lia.
    - apply cells_write_other; try (cbn; lia). exact D. }
  split; [exact E|].
  split; [apply agree_out_wbytes; try lia; [exact G | exact HF]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_memcpy_pb : forall m s (i : Z) (off : Z) (n : nat) (bs : list byte),
  BR m s -> bs = fbytes (arr_get (ds_window s)) off n ->
  (forall j, off <= j < off + Z.of_nat n -> 0 <= arr_get (ds_window s) j < 256) ->
  0 <= i -> i + Z.of_nat n <= PBL ->
  BR (wbytes m (zw (PB + i)) bs)
     (set_pending_buf s (arr_blit (ds_pending_buf s) i (ds_window s) off (Z.of_nat n))).
Proof.
  intros m s i off n bs (A & B & C & D & E & G & H & I & J) Hbs Hwb Hi0 Hin.
  destruct HL as (HS & HPB & Hdisj & HF40 & HF5936 & HF5940 & HFPB). unfold BR, dsl_SIZE in *.
  assert (Hlen : length bs = n) by (subst bs; apply fbytes_length).
  split.
  { apply (proj2 (scalars_set_pending_buf _ _ _ _ _ _ _ _ _)).
    apply dsl_scalars_frame; rewrite ?Hlen; unfold dsl_SIZE; try lia. exact A. }
  split.
  { change (dsl_arrays segs ?M S (set_pending_buf s ?x)) with (dsl_arrays segs M S s).
    apply arrays_write_other; rewrite ?Hlen; unfold dsl_SIZE; try lia. exact B. }
  split; [unfold tree_lens in *; cbn; exact C|].
  split.
  { change (ds_pending_buf (set_pending_buf s ?x)) with x.
    pose proof (cells_wbytes_bytes segs m PB PBL (arr_get (ds_pending_buf s)) i bs D
                  ltac:(lia) ltac:(rewrite Hlen; lia) ltac:(lia) ltac:(lia)) as Hc.
    refine (cells_ext _ _ _ _ _ _ _ _ _ Hc). intros j Hj. cbn beta.
    rewrite arr_get_blit. unfold arr_inb. rewrite E, Hlen.
    destruct (Z.leb_spec i j), (Z.ltb_spec j (i + Z.of_nat n)), (Z.ltb_spec j (i + Z.max 0 (Z.of_nat n))),
      (Z.leb_spec 0 j), (Z.ltb_spec j PBL); cbn [andb]; try reflexivity; try lia.
    subst bs. rewrite fbytes_nth; [f_equal; lia | lia |].
    intros q Hq. apply Hwb. lia. }
  split; [change (ds_pending_buf (set_pending_buf s ?x)) with x; rewrite arr_len_blit; exact E|].
  split.
  { apply agree_out_wbytes; rewrite ?Hlen; try lia; [exact G|]. intros x Hx. apply HFPB. lia. }
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.


End Rel.

Lemma agree_out_via : forall F m0 m1 m2,
  agree_out F m0 m1 -> agree_out F m0 m2 -> agree_out F m1 m2.
Proof. intros F m0 m1 m2 H1 H2 x Hx. rewrite (H1 x Hx), (H2 x Hx). reflexivity. Qed.

Lemma BR_weaken : forall F G mem0 S p PBL m s,
  BR F mem0 S p PBL m s -> (forall x, in_franges F x -> in_franges G x) -> BR G mem0 S p PBL m s.
Proof.
  intros F G mem0 S p PBL m s (A & B & C & D & E & Hag & H & I & J) HFG. unfold BR.
  repeat (split; [assumption|]). split; [eapply agree_out_weaken; [exact Hag | exact HFG]|]. tauto.
Qed.

Lemma BR_rebase : forall F mem0 mem S p PBL m s0 s,
  BR F mem0 S p PBL mem s0 -> BR F mem S p PBL m s -> BR F mem0 S p PBL m s.
Proof.
  intros F mem0 mem S p PBL m s0 s (_ & _ & _ & _ & _ & Hag0 & _ & _ & J0) (A & B & C & D & E & Hag & H & I & J).
  unfold BR. repeat (split; [assumption|]).
  split; [eapply agree_out_trans; [exact Hag0 | exact Hag]|].
  split; [exact H|]. split; [exact I|]. intros x Hx. apply J. apply J0. exact Hx.
Qed.


Lemma arrays_write_gap : forall m S s (b : Z) bs,
  dsl_arrays segs m S s -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 -> 0 <= b ->
  b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (b + Z.of_nat (length bs) <= S + 212
   \/ (S + 2904 <= b /\ b + Z.of_nat (length bs) <= S + 2976)
   \/ (S + 5300 <= b /\ b + Z.of_nat (length bs) <= S + 5308)
   \/ S + 5881 <= b) ->
  dsl_arrays segs (wbytes m (zw b) bs) S s.
Proof.
  intros m S s b bs H HS0 HS1 Hb0 Hb1 Hd. unfold dsl_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  repeat split;
    first [ eapply cells_write_other; [eassumption | cbn; lia | lia | lia | lia | lia | cbn; lia]
          |
            intros j Hj; apply cell_write_other; [apply A6; exact Hj | lia | cbn; lia | lia | lia | cbn; lia] ].
Qed.

Lemma set_tree_fc_twice : forall s t a b, set_tree_fc (set_tree_fc s t a) t b = set_tree_fc s t b.
Proof. intros s [| |] a b; reflexivity. Qed.
Lemma tree_fc_set_tree_fc : forall s t a, tree_fc (set_tree_fc s t a) t = a.
Proof. intros s [| |] a; reflexivity. Qed.
Lemma tree_dl_set_tree_dl : forall s t a, tree_dl (set_tree_dl s t a) t = a.
Proof. intros s [| |] a; reflexivity. Qed.

Section Rel2.
Variables (F : franges) (mem0 : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation BR := (BR F mem0 S p PBL).
Hypothesis HL : BRH F S p PBL.
Hypothesis HFS : sub_franges F S dsl_SIZE.

Local Ltac other9 A :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact A.

Local Ltac scalar_tail UPD :=
  intros m s v (A & B & C & D & E & G & H & I & J);
  destruct HL as (HS & HPB & Hdisj & _); unfold BR, dsl_SIZE in *;
  split; [apply UPD; unfold dsl_SIZE; try lia; exact A|];
  split; [apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|];
  split; [exact C|];
  split; [dsred; other9 D|];
  split; [dsred; exact E|];
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS; cbn in Hx; lia]|];
  split; [apply mapped_wbytes; exact H|]; split; [apply mapped_wbytes; exact I|];
  intros x Hx; apply wbytes_grows; exact (J x Hx).

Lemma BR_st_opt_len : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5912)) (Z_to_le_bytes 8 v)) (set_opt_len s v).
Proof. scalar_tail dsl_upd_opt_len. Qed.
Lemma BR_st_static_len : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5920)) (Z_to_le_bytes 8 v)) (set_static_len s v).
Proof. scalar_tail dsl_upd_static_len. Qed.
Lemma BR_st_matches : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5928)) (Z_to_le_bytes 4 v)) (set_matches s v).
Proof. scalar_tail dsl_upd_matches. Qed.
Lemma BR_st_sym_next : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5900)) (Z_to_le_bytes 4 v)) (set_sym_next s v).
Proof. scalar_tail dsl_upd_sym_next. Qed.
Lemma BR_st_heap_len : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5300)) (Z_to_le_bytes 4 v)) (set_heap_len s v).
Proof. scalar_tail dsl_upd_heap_len. Qed.
Lemma BR_st_heap_max : forall m s v,
  BR m s -> BR (wbytes m (zw (S + 5304)) (Z_to_le_bytes 4 v)) (set_heap_max s v).
Proof. scalar_tail dsl_upd_heap_max. Qed.

Lemma BR_st_fc : forall m s t i v,
  BR m s -> 0 <= i < tsize t ->
  BR (wbytes m (zw (S + toff t + 4 * i)) (Z_to_le_bytes 2 v)) (set_tree_fc s t (arr_set (tree_fc s t) i (wrap16 v))).
Proof.
  intros m s t i v (A & B & C & D & E & G & H & I & J) Hi.
  destruct HL as (HS & HPB & Hdisj & _). unfold BR, dsl_SIZE in *. pose proof (toff_tsize t) as Ht.
  split.
  { apply (proj2 (scalars_set_tree_fc _ _ _ _ _ _ _ _ _ _)).
    replace (S + toff t + 4 * i) with (S + toff t + 4 * i + 0) by lia.
    apply scalars_tree_set; unfold dsl_SIZE; try lia. exact A. }
  split; [apply arrays_set_fc; unfold dsl_SIZE; try lia; assumption|].
  split; [apply tree_lens_set_fc; [exact C | rewrite arr_len_set; apply tree_lens_fc; exact C]|].
  split; [replace (ds_pending_buf (set_tree_fc s t _)) with (ds_pending_buf s) by (destruct t; reflexivity); other9 D|].
  split; [replace (ds_pending_buf (set_tree_fc s t _)) with (ds_pending_buf s) by (destruct t; reflexivity); exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS; cbn in Hx; lia]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BR_st_dl : forall m s t i v,
  BR m s -> 0 <= i < tsize t ->
  BR (wbytes m (zw (S + toff t + 4 * i + 2)) (Z_to_le_bytes 2 v)) (set_tree_dl s t (arr_set (tree_dl s t) i (wrap16 v))).
Proof.
  intros m s t i v (A & B & C & D & E & G & H & I & J) Hi.
  destruct HL as (HS & HPB & Hdisj & _). unfold BR, dsl_SIZE in *. pose proof (toff_tsize t) as Ht.
  split.
  { apply (proj2 (scalars_set_tree_dl _ _ _ _ _ _ _ _ _ _)).
    apply scalars_tree_set; unfold dsl_SIZE; try lia. exact A. }
  split; [apply arrays_set_dl; unfold dsl_SIZE; try lia; assumption|].
  split; [apply tree_lens_set_dl; [exact C | rewrite arr_len_set; apply tree_lens_dl; exact C]|].
  split; [replace (ds_pending_buf (set_tree_dl s t _)) with (ds_pending_buf s) by (destruct t; reflexivity); other9 D|].
  split; [replace (ds_pending_buf (set_tree_dl s t _)) with (ds_pending_buf s) by (destruct t; reflexivity); exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS; cbn in Hx; lia]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Local Ltac arr_tail AUPD SUPD :=
  intros m s i v (A & B & C & D & E & G & H & I & J) Hi;
  destruct HL as (HS & HPB & Hdisj & _); unfold BR, dsl_SIZE in *;
  split; [apply SUPD; unfold dsl_SIZE; try lia; exact A|];
  split; [apply AUPD; unfold dsl_SIZE; try lia; assumption|];
  split; [unfold tree_lens, heap_set, depth_set, bl_count_set in *; dsred; rewrite ?arr_len_set; exact C|];
  split; [unfold heap_set, depth_set, bl_count_set; dsred; other9 D|];
  split; [unfold heap_set, depth_set, bl_count_set; dsred; exact E|];
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS; cbn in Hx; lia]|];
  split; [apply mapped_wbytes; exact H|]; split; [apply mapped_wbytes; exact I|];
  intros x Hx; apply wbytes_grows; exact (J x Hx).

Lemma BR_st_heap : forall m s i v,
  BR m s -> 0 <= i < 573 ->
  BR (wbytes m (zw (S + 3008 + 4 * i)) (Z_to_le_bytes 4 v)) (heap_set s i v).
Proof. arr_tail arrays_heap_set scalars_heap_set. Qed.
Lemma BR_st_depth : forall m s i v,
  BR m s -> 0 <= i < 573 ->
  BR (wbytes m (zw (S + 5308 + i)) (Z_to_le_bytes 1 v)) (depth_set s i v).
Proof. arr_tail arrays_depth_set scalars_depth_set. Qed.
Lemma BR_st_bl_count : forall m s i v,
  BR m s -> 0 <= i < 16 ->
  BR (wbytes m (zw (S + 2976 + 2 * i)) (Z_to_le_bytes 2 v)) (bl_count_set s i v).
Proof. arr_tail arrays_bl_count_set scalars_bl_count_set. Qed.

End Rel2.

Lemma frame_fix : forall (R regs : bvmap 5 word) (a : reg) (L : list reg),
  getr R a = getr regs a ->
  (forall r : reg, reg_in r (a :: L) = false -> getr R r = getr regs r) ->
  forall r : reg, reg_in r L = false -> getr R r = getr regs r.
Proof.
  intros R regs a L Ha HL r Hr. destruct (bv_eqb r a) eqn:E.
  - assert (r = a) by (apply bv_eq; unfold bv_eqb in E; lia). subst r. exact Ha.
  - apply HL. cbn [reg_in]. rewrite E, Hr. reflexivity.
Qed.

Lemma franges_apart : forall F a n b k,
  sub_franges F a n -> disj_franges F b k -> 0 < n -> 0 < k -> a + n <= b \/ b + k <= a.
Proof.
  intros F a n b k Hs Hd Hn Hk.
  destruct (Z_le_gt_dec (a + n) b) as [|H1]; [left; lia|].
  destruct (Z_le_gt_dec (b + k) a) as [|H2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec a b).
  - apply (Hd b ltac:(lia)). apply Hs. lia.
  - apply (Hd a ltac:(lia)). apply Hs. lia.
Qed.

Lemma sub_franges_mono : forall F a n b k,
  sub_franges F a n -> a <= b -> b + k <= a + n -> sub_franges F b k.
Proof. intros F a n b k H H1 H2 x Hx. apply H. lia. Qed.


End WithImage.


End FXG.
Ltac br_fwd HB M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      br_fwd HB M1;
      lazymatch goal with
      | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 ?s1, HL : BRH ?F ?S ?p ?PBL |- _ =>
          let H2 := fresh "HBR" in
          lazymatch a with
          | S + 40 => pose proof (BR_st_pending sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5936 => pose proof (BR_st_bi_buf sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5940 => pose proof (BR_st_bi_valid sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | _ =>
              let Hi := fresh in
              let ty := constr:(0 <= a - p_pending_buf p < PBL) in
              assert (Hi : ty) by lia;
              pose proof (BR_st_pb sg AL AD AB F mem0 S p PBL HL M1 s1 a (a - p_pending_buf p) v H1 ltac:(lia) Hi) as H2;
              clear Hi
          end;
          clear H1
      end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma upd4_congr : forall s A A' P P' B B' V V',
  A = A' -> P = P' -> B = B' -> V = V' -> upd4 s A P B V = upd4 s A' P' B' V'.
Proof. intros; subst; reflexivity. Qed.

End FXG.
Ltac u4 t :=
  lazymatch t with
  | set_bi_valid ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P B v) end
  | set_bi_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P v V) end
  | set_pending ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A v B V) end
  | set_pending_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s v P B V) end
  | upd4 _ _ _ _ _ => t
  | ?s => constr:(upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s))
  end.
Ltac st_eq :=
  lazymatch goal with
  | |- ?a = ?b =>
      let a' := u4 a in let b' := u4 b in
      change (a' = b'); apply upd4_congr; dsred
  end.
