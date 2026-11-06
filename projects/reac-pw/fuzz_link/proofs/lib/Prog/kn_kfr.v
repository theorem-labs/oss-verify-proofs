(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 225 of its 266 lines of code are new or changed and 660 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: the walk kit for `kernel` (lib/Prog/kernel.v and its block files).

   kernel has a 4336-byte frame and a 4112-byte `struct nl_w` in it, and it writes that buffer at offsets
   it computes (w->n). The released step tactics (lib/Lib/Step.v, Tac.v) handle a store only into a cell
   at a literal offset from a cell base. This file adds, for a run `CB N j` of bytes at a base A:
   - a store at any address E with A <= E and E + len <= A + N (the bounds by lia): `solve_store` and
     `mem_after_store_opt` gain that case, and the run's bytes after the store are forgotten (the
     contracts of kernel and its callees never read them back as values);
   - the frame cut by Z sizes, so no cell carries a large unary offset.
   It also gives the reads of the input bytes and of the two .rodata tables kernel indexes, and the
   byte-wide divisions the compiler turned into multiplications. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf kn_nlk.
Local Open Scope Z_scope.

(* ==========================================================================
   1. A run of bytes written at computed offsets
   ========================================================================== *)

Lemma rw_cells_CB_store_ok : forall m A N j E n,
  rw_cells rsegs m A [CB N j] -> A <= E -> E + Z.of_nat n <= A + Z.of_nat N ->
  store_ok rsegs m (wa E) n = true.
Proof.
  intros m A N j E n [_ HW] H1 H2. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  replace E with (A + (E - A)) by lia. apply wr_at_store_ok with (n := Z.of_nat N); [exact HW | lia | lia].
Qed.

Lemma rw_cells_CB_write : forall m A N j E bs,
  rw_cells rsegs m A [CB N j] -> A <= E -> E + Z.of_nat (length bs) <= A + Z.of_nat N ->
  rw_cells rsegs (write_to_mem m (wa E) bs) A [CB N (upd_bytes j (Z.to_nat (E - A)) bs)].
Proof.
  intros m A N j E bs [[Hwf HB] HW] H1 H2. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  pose proof (bytes_at_bound rsegs m A j HB) as HBB.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite upd_bytes_length by lia. exact Hl.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    assert (EE : wa E = wa (A + (E - A))) by (f_equal; lia). rewrite EE.
    apply bytes_at_write_inside; [exact HB | lia | lia].
  - apply wr_at_write. exact HW.
Qed.

(* Step.v's solve_store under another name, with one change: the address a store writes through may be a bare
   register (`sd a2, 0(s0)` with s0 = the caller's a0); Step.v's `addr_eq_tac` proves only
   `a = wa (...)` for it, and the final `replace` needs `wa (...) = a`. *)
Ltac solve_store_base :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs)
                by (f_equal; first [addr_eq_tac | apply wa_of_var; lia])
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

(* a store into a run `CB N j` at a computed offset *)
Ltac solve_store_cb :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A [CB ?N ?j] |- _ =>
        let HS := fresh "HS" in
        assert (HS : store_ok segs m a n = true)
          by (change a with (wa E); apply (rw_cells_CB_store_ok m A N j E n H); [lia | lia]);
        rewrite HS; clear HS; cbv beta iota
    end
  end.

Ltac solve_store ::= first [ solve_store_base | solve_store_cb ].

Ltac cb_after_store :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A [CB ?N ?j] |- _ =>
        let H1 := fresh "CB1" in let H2 := fresh "CB2" in
        assert (H1 : A <= E) by lia;
        assert (H2 : E + Z.of_nat (length bs) <= A + Z.of_nat N) by (simpl_sizes; lia);
        let H' := fresh "CBW" in
        pose proof (rw_cells_CB_write m A N j E bs H H1 H2) as H';
        try lazymatch goal with HI : mem_inv segs m |- _ =>
          apply (mem_inv_store segs m (wa E) bs) in HI;
          [ | apply (rw_cells_CB_store_ok m A N j E (length bs) H H1 H2) ] end;
        clear H1 H2 H;
        change (write_to_mem m a bs) with (write_to_mem m (wa E) bs);
        transport_chunks segs m E bs;
        footprint_after_store segs m E bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
        clear Heqm; try clear m;
        let j' := fresh "wbj" in
        lazymatch type of H' with rw_cells _ _ _ [CB _ ?nj] => set (j' := nj) in H'; clearbody j' end;
        rename H' into H
    end
  end.

Ltac mem_after_store_opt ::=
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end;
  try cb_after_store.

(* ==========================================================================
   2. The frame, cut by Z sizes
   ========================================================================== *)

Lemma stk_carve_z : forall m lo hi n, stk rsegs m lo hi -> 0 <= n -> lo <= hi - n ->
  stk rsegs m lo (hi + - n) /\ exists junk, rw_cells rsegs m (hi + - n) [CB (Z.to_nat n) junk].
Proof.
  intros m lo hi n ST H0 H1.
  destruct (stk_carve rsegs m lo hi (Z.to_nat n) ST ltac:(lia)) as [ST' [junk FR]].
  rewrite Z2Nat.id in ST', FR by lia. replace (hi + - n) with (hi - n) by lia.
  split; [exact ST'|]. exists junk. exact FR.
Qed.

Ltac carve_z n ST :=
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi =>
      let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
      destruct (stk_carve_z m lo hi n ST ltac:(lia) ltac:(lia)) as [ST' [junk FR]];
      clear ST; rename ST' into ST;
      repeat match type of FR with
      | context [Z.add (Z.add ?b ?c) (Z.opp ?d)] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
           replace (Z.add (Z.add b c) (Z.opp d)) with (Z.add b v) in * by lia
      | context [Z.add ?b (Z.opp ?d)] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
           replace (Z.add b (Z.opp d)) with (Z.add b v) in * by lia
      end
  end.

(* ==========================================================================
   3. Reads: input bytes, small words
   ========================================================================== *)

Lemma slice_le1 : forall bs a, 0 <= a -> a + 1 <= Z.of_nat (length bs) -> slice bs a 1 = le1 (wz (rdn bs a 1)).
Proof.
  intros bs a H0 H1. unfold le1, wz, rdn.
  pose proof (slice_length bs a 1 H0 ltac:(lia) H1) as L. change (Z.to_nat 1) with 1%nat in L.
  pose proof (bytes_le_to_Z_nonneg (slice bs a 1)) as N.
  pose proof (bytes_le_to_Z_bound (slice bs a 1)) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in B.
  rewrite unsigned_lit by lia.
  transitivity (Z_to_le_bytes (length (slice bs a 1)) (bytes_le_to_Z (slice bs a 1))).
  - symmetry. apply Z_to_le_bytes_of_bytes.
  - rewrite L. reflexivity.
Qed.

Lemma bytes_at_rd1 : forall m A d E a,
  bytes_at rsegs m A d -> A <= E -> E + 1 <= A + Z.of_nat (length d) -> a = wa E ->
  ov_read_bytes rsegs m a 1 = Some (le1 (wz (rdn d (E - A) 1))).
Proof.
  intros m A d E a HB H1 H2 ->.
  assert (EE : wa E = wa (A + (E - A))) by (f_equal; lia). rewrite EE.
  rewrite (bytes_at_read rsegs m A d (E - A) 1 HB) by lia.
  f_equal. rewrite <- slice_le1 by lia. reflexivity.
Qed.

Lemma zx8_wz : forall v, 0 <= v < 256 -> zx8 (wz v) = wz v.
Proof. intros v H. unfold zx8, wz. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.

Lemma rdn1_range : forall d a, 0 <= a -> a + 1 <= Z.of_nat (length d) -> 0 <= rdn d a 1 < 256.
Proof. intros d a H0 H1. pose proof (rdn_range d a 1 H0 ltac:(lia) H1) as R. exact R. Qed.

(* ==========================================================================
   4. Runs of cells cut and glued, and the reply buffer as `nlw_at`
   ========================================================================== *)

Lemma wr_at_app : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H0 & H1 & H) (G0 & G1 & G) N1 N2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i n1) as [L|L]; [apply H; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply G. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. split.
  - intros [[Hwf HB] HW]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
    rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
    rewrite cells_size_app in HW. rewrite cells_bytes_length in B2 by exact W1.
    split; split; try (split; assumption).
    + eapply wr_at_sub with (k := 0) in HW; [rewrite Z.add_0_r in HW; exact HW | lia | lia | lia].
    + eapply wr_at_sub with (k := Z.of_nat (cells_size cs1)) in HW; [exact HW | lia | lia | lia].
  - intros [[[W1 B1] H1] [[W2 B2] H2]]. split; [split|].
    + apply cells_wf_app. split; assumption.
    + rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
      rewrite cells_bytes_length by exact W1. exact B2.
    + rewrite cells_size_app, Nat2Z.inj_add. apply wr_at_app; [exact H1 | exact H2 | lia | lia].
Qed.

Lemma rw_cells_same_bytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf HB] HW] W' EB ES. split; [split|].
  - exact W'.
  - rewrite EB. exact HB.
  - rewrite ES. exact HW.
Qed.

Lemma le8_lit_bytes : forall l : list byte, length l = 8%nat -> l = le8 (Z_to_bv 64 (rdn l 0 8)).
Proof.
  intros l L. pose proof (rdn_le8_slice l 0 ltac:(lia) ltac:(lia)) as E.
  unfold slice in E. change (Z.to_nat 0) with 0%nat in E. change (Z.to_nat 8) with 8%nat in E.
  cbn [skipn] in E. rewrite <- L in E at 1. rewrite firstn_all in E. exact E.
Qed.

Lemma le4_lit_bytes : forall l : list byte, length l = 4%nat -> l = le4 (Z_to_bv 64 (rdn l 0 4)).
Proof.
  intros l L. pose proof (rdn_le4_slice l 0 ltac:(lia) ltac:(lia)) as E.
  unfold slice in E. change (Z.to_nat 0) with 0%nat in E. change (Z.to_nat 4) with 4%nat in E.
  cbn [skipn] in E. rewrite <- L in E at 1. rewrite firstn_all in E. exact E.
Qed.

(* the buffer's two runs give the `nlw_at` attr_text and nl_error take *)
Lemma kw_nlw : forall m A wbj wn wf pad,
  rw_cells rsegs m A [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (A + 4096) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad] ->
  0 <= wn <= 4096 -> 0 <= wf <= 1 ->
  exists bs, nlw_at m A bs /\ nlw_wf bs /\ nw_n bs = wn /\ nw_full bs = wf.
Proof.
  intros m A wbj wn wf pad C1 C2 N F.
  assert (C : rw_cells rsegs m A ([CB (Z.to_nat 4096) wbj] ++ [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad])).
  { apply rw_cells_app. split; [exact C1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact C2. }
  pose proof C as [[Hwf HB] HW]. cbn [app cells_wf cell_wf] in Hwf. destruct Hwf as [L1 [_ [_ [L4 _]]]].
  exists (cells_bytes [CB (Z.to_nat 4096) wbj; C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad]).
  cbn [cells_bytes cbytes app] in *. rewrite ?app_nil_r in *.
  assert (LL : Z.of_nat (length (wbj ++ le8 (Z_to_bv 64 wn) ++ le4 (Z_to_bv 64 wf) ++ pad)) = 4112)
    by (rewrite !length_app, length_le8, length_le4, L1, L4; lia).
  split; [split; [split; [exact HB|] |] |].
  - cbn [cells_size csize] in HW. rewrite LL.
    replace 4112 with (Z.of_nat (Z.to_nat 4096 + (8 + (4 + (4 + 0))))) by lia. exact HW.
  - rewrite LL. reflexivity.
  - unfold nlw_wf, nw_n, nw_full, fld_u32, fld_u64, NW_N, NW_FULL, NL_CHUNK_MAX.
    assert (E1 : rdn (wbj ++ le8 (Z_to_bv 64 wn) ++ le4 (Z_to_bv 64 wf) ++ pad) 4096 8 = wn).
    { unfold rdn. rewrite slice_app_r by lia. rewrite L1, Z2Nat.id by lia. replace (4096 - 4096) with 0 by lia.
      fold (rdn (le8 (Z_to_bv 64 wn) ++ le4 (Z_to_bv 64 wf) ++ pad) 0 8). rewrite rdn_le8_head by reflexivity.
      apply unsigned_lit. lia. }
    assert (E2 : rdn (wbj ++ le8 (Z_to_bv 64 wn) ++ le4 (Z_to_bv 64 wf) ++ pad) 4104 4 = wf).
    { unfold rdn. rewrite slice_app_r by lia. rewrite L1, Z2Nat.id by lia. replace (4104 - 4096) with 8 by lia.
      fold (rdn (le8 (Z_to_bv 64 wn) ++ le4 (Z_to_bv 64 wf) ++ pad) 8 4).
      rewrite rdn_le8_cons by lia. replace (8 - 8) with 0 by lia. rewrite rdn_le4_head by reflexivity.
      rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
    rewrite E1, E2. lia.
Qed.

Lemma slice_full : forall bs, slice bs 0 (Z.of_nat (length bs)) = bs.
Proof. intros bs. unfold slice. change (Z.to_nat 0) with 0%nat. cbn [skipn]. rewrite Nat2Z.id. apply firstn_all. Qed.

Lemma rw_cells_at : forall m A B cs, rw_cells rsegs m A cs -> A = B -> rw_cells rsegs m B cs.
Proof. intros; subst; assumption. Qed.

(* ... and back after the call *)
Lemma nlw_kw : forall m A bs, nlw_at m A bs -> nlw_wf bs ->
  exists wbj pad, rw_cells rsegs m A [CB (Z.to_nat 4096) wbj] /\
    rw_cells rsegs m (A + 4096) [C8 (Z_to_bv 64 (nw_n bs)); C4 (Z_to_bv 64 (nw_full bs)); CB 4 pad].
Proof.
  intros m A bs [HU HL] WF. unfold NW_SIZE in HL.
  pose proof (rw_cells_of_u8arr rsegs m A bs HU) as C.
  assert (EB : bs = slice bs 0 4096 ++ slice bs 4096 8 ++ slice bs 4104 4 ++ slice bs 4108 4).
  { rewrite <- (slice_full bs) at 1. rewrite HL.
    replace 4112 with (4096 + (8 + (4 + 4))) by reflexivity.
    rewrite slice_split by lia. replace (0 + 4096) with 4096 by reflexivity.
    rewrite slice_split by lia. replace (4096 + 8) with 4104 by reflexivity.
    rewrite slice_split by lia. replace (4104 + 4) with 4108 by reflexivity. reflexivity. }
  exists (slice bs 0 4096), (slice bs 4108 4).
  assert (L1 : length (slice bs 0 4096) = Z.to_nat 4096) by (apply slice_length; lia).
  assert (L4 : length (slice bs 4108 4) = 4%nat) by (apply (slice_length bs 4108 4); lia).
  assert (C' : rw_cells rsegs m A
                 ([CB (Z.to_nat 4096) (slice bs 0 4096)] ++
                  [C8 (Z_to_bv 64 (nw_n bs)); C4 (Z_to_bv 64 (nw_full bs)); CB 4 (slice bs 4108 4)])).
  { apply (rw_cells_same_bytes m A [CB (length bs) bs]); [exact C | | | ].
    - cbn [app cells_wf cell_wf]. repeat split; assumption.
    - cbn [app cells_bytes cbytes]. rewrite app_nil_r. rewrite EB at 5.
      unfold nw_n, nw_full, fld_u64, fld_u32, NW_N, NW_FULL.
      change (Z_to_bv 64 (rdn bs 4096 8)) with (wz (rdn bs 4096 8)).
      change (Z_to_bv 64 (rdn bs 4104 4)) with (wz (rdn bs 4104 4)).
      rewrite <- (rdn_le8_slice bs 4096) by lia. rewrite <- (rdn_le4_slice bs 4104) by lia.
      rewrite ?app_nil_r. reflexivity.
    - cbn [app cells_size csize]. lia. }
  apply rw_cells_app in C'. destruct C' as [C1 C2]. split; [exact C1|].
  eapply rw_cells_at; [exact C2|]. cbn [cells_size csize]. lia.
Qed.

(* ==========================================================================
   5. Byte-wide arithmetic, checked over the 256 values
   ========================================================================== *)

Lemma by_enum256 : forall (f g : Z -> Z),
  forallb (fun v => f v =? g v) (map Z.of_nat (seq 0 256)) = true -> forall z, 0 <= z < 256 -> f z = g z.
Proof.
  intros f g H z Hz. rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia.
Qed.
