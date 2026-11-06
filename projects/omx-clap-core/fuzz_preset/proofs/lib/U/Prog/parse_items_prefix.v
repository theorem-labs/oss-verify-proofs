From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require ReaderRes.
Import ListNotations.
Open Scope Z_scope.

Definition pres (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Definition chg (W : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  munch W m m' /\ wmono rsegs m m' /\ pres m m'.

Lemma pres_write : forall bs m a, pres m (write_to_mem m a bs).
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply (IH _ _ x). destruct (bv_eqb x a); [discriminate | exact H].
Qed.

Lemma chg_refl : forall W m, chg W m m.
Proof. intros W m. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x H; exact H. Qed.

Lemma chg_write : forall W m0 m a bs, chg W m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  inside W a (Z.of_nat (length bs)) -> chg W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs (H1 & H2 & H3) Ha Hb Hi. split; [apply munch_write; assumption|].
  split; [apply wmono_write; exact H2|]. intros x Hx. apply pres_write. apply H3. exact Hx.
Qed.

Lemma pip_rd8 : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w H. rewrite <- (Z.add_0_r a) at 1. rewrite (bytes_at_read rsegs m a _ 0 8 H) by (rewrite ?length_le8; cbn; lia).
  rewrite firstn_all2 by (rewrite ?length_skipn, ?length_le8; lia). reflexivity.
Qed.

Lemma pip_rd4 : forall m a w, bytes_at rsegs m a (le4 w) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 w).
Proof.
  intros m a w H. rewrite <- (Z.add_0_r a) at 1. rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; cbn; lia).
  rewrite firstn_all2 by (rewrite ?length_skipn, ?length_le4; lia). reflexivity.
Qed.

Lemma pip_sok : forall m A N X (j : nat), wr_at rsegs m A N -> A <= X -> X + Z.of_nat j <= A + N ->
  store_ok rsegs m (wa X) j = true.
Proof.
  intros m A N X j H H1 H2. replace X with (A + (X - A)) by lia. apply (wr_at_store_ok rsegs m A N (X - A) j H); lia.
Qed.

Lemma pip_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma pip_skipn_nth : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|a l IH]; intros [|k] b H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma pip_rest_cons : forall tb text x b, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some b ->
  ReaderRes.rest_at tb text x = bv_unsigned b :: ReaderRes.rest_at tb text (x + 1).
Proof.
  intros tb text x b Hx H. unfold ReaderRes.rest_at, ReaderRes.zb.
  rewrite (pip_skipn_nth tb _ b H). replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia.
  reflexivity.
Qed.

Lemma pip_rest_ge : forall tb text len x, Z.of_nat (length tb) = len -> text + len <= x ->
  ReaderRes.rest_at tb text x = [].
Proof.
  intros tb text len x H Hx. unfold ReaderRes.rest_at, ReaderRes.zb. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma pip_rdt : forall m text tb x, bytes_at rsegs m text tb -> text <= x < text + Z.of_nat (length tb) ->
  exists b, nth_error tb (Z.to_nat (x - text)) = Some b /\ ov_read_bytes rsegs m (wa x) 1 = Some [b].
Proof.
  intros m text tb x H Hx.
  destruct (nth_error tb (Z.to_nat (x - text))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. split; [reflexivity|].
  assert (Ex : wa x = wa (text + (x - text))) by (f_equal; lia). rewrite Ex.
  rewrite (bytes_at_read rsegs m text tb (x - text) 1 H) by lia.
  rewrite (pip_skipn_nth tb _ b E). reflexivity.
Qed.

Lemma pip_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_eqb_byte : forall c (b : byte), 0 <= c < 2 ^ 64 -> bv_eqb (Z_to_bv 64 c) (zxb b) = (c =? bv_unsigned b).
Proof. intros c b H. pose proof (pip_byte b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_eqb_byte_r : forall c (b : byte), 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof. intros c b H. pose proof (pip_byte b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_sh3 : forall n, 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 3) = Z_to_bv 64 (8 * n).
Proof. intros n H. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. change (2 ^ 3) with 8. lia. Qed.

Lemma pip_ne_m1 : forall x, 0 <= x < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x H. unfold bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. assert (E : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by reflexivity. lia.
Qed.

Lemma pip_eqb0 : forall w : word, bv_eqb w (Z_to_bv 64 0) = true -> w = Z_to_bv 64 0.
Proof. intros w H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite <- (Z_to_bv_bv_unsigned w), H. apply Z_to_bv_bv_unsigned. Qed.

Lemma pip_shl : forall x k, 0 <= x -> 0 <= k -> x * 2 ^ k < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) k) = Z_to_bv 64 (x * 2 ^ k).
Proof. intros x k H0 H1 H2. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma pip_signed : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma pip_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma pip_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))), (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma pip_sx32 : forall d, 0 <= d < 2 ^ 31 -> sx32 (Z_to_bv 64 d) = Z_to_bv 64 d.
Proof.
  intros d H. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

Lemma pip_addiw : forall d k, 0 <= d < 2 ^ 64 -> - 2 ^ 31 <= d + k < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 d) + k)) = Z_to_bv 64 (d + k).
Proof.
  intros d k H1 H2. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

Lemma pip_snez : forall o : bool, v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (if o then 1 else 0)) = Z_to_bv 64 (if o then 1 else 0).
Proof. intros [|]; first [ reflexivity | apply bv_eq; vm_compute; reflexivity ]. Qed.

Lemma pip_sp_back : forall sp : word, Z_to_bv 64 (bv_unsigned sp - 96 + 96) = sp.
Proof. intros sp. rewrite Z.sub_add. apply Z_to_bv_bv_unsigned. Qed.

Ltac pip_trap H :=
  zify_cond H; rewrite ?unsigned_lit in H by lia; rewrite ?Z.shiftl_mul_pow2 in H by lia;
  rewrite ?unsigned_lit in H by lia; rewrite ?pip_land7 in H; rewrite ?Z.shiftr_div_pow2 in H by lia;
  revert H; repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  intros H; cbn [Z.b2z] in H; first [discriminate | lia | contradiction].

Ltac sok X n :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m (wa X) n = true)
      by (match goal with H : wr_at rsegs m _ _ |- _ => apply (pip_sok _ _ _ _ _ H); lia end)
  end.

Ltac mst :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
    let E := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa E) bs);
    let NB := fresh "NB" in
    assert (NB : bytes_at rsegs (write_to_mem m (wa E) bs) E bs)
      by (apply bytes_at_write_same; simpl_sizes; lia);
    repeat match goal with
    | CH : chg ?W ?m0 m |- _ =>
        apply (chg_write W m0 m E bs) in CH; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]
    end;
    transport_chunks rsegs m E bs;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm; clear Heqm;
    repeat match goal with
    | H : store_ok rsegs m _ _ = true |- _ => clear H
    | H : ov_read_bytes rsegs m _ _ = Some _ |- _ => clear H
    end
  end.

Definition pi_frame (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word) : Prop :=
  0 <= f /\
  bytes_at rsegs m (f + 8) (le8 c9) /\ bytes_at rsegs m (f + 16) (le8 c8) /\ bytes_at rsegs m (f + 24) (le8 c7) /\
  bytes_at rsegs m (f + 32) (le8 c6) /\ bytes_at rsegs m (f + 40) (le8 c5) /\ bytes_at rsegs m (f + 48) (le8 c4) /\
  bytes_at rsegs m (f + 56) (le8 c3) /\ bytes_at rsegs m (f + 64) (le8 c2) /\ bytes_at rsegs m (f + 72) (le8 c1) /\
  bytes_at rsegs m (f + 80) (le8 c0) /\ bytes_at rsegs m (f + 88) (le8 r0).

Ltac frame_pack := unfold pi_frame; split; [lia|]; repeat (split; [eassumption|]); eassumption.

Lemma pip_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 s3 a1 a2 a3 a4 a5 a6 a7
                          c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16dd0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 (P & P9 & P8 & P7 & P6 & P5 & P4 & P3 & P2 & P1 & P0 & PR).
  pose proof (bytes_at_bound rsegs m _ _ PR) as BR. rewrite length_le8 in BR. cbn in BR.
  apply pip_rd8 in P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, PR.
  do 14 step. apply evt_done. reflexivity.
Qed.

Definition pi_q (m : word -> option byte) (q text len p d : Z) (tb : list byte) : Prop :=
  bytes_at rsegs m q (le8 (Z_to_bv 64 p)) /\ bytes_at rsegs m (q + 8) (le8 (Z_to_bv 64 (text + len))) /\
  bytes_at rsegs m (q + 16) (le4 (Z_to_bv 64 d)) /\ wr_at rsegs m q 24 /\ bytes_at rsegs m text tb.

Lemma pip_mk_in : forall m q text len p d tb,
  bytes_at rsegs m q (le8 (Z_to_bv 64 p)) -> bytes_at rsegs m (q + 8) (le8 (Z_to_bv 64 (text + len))) ->
  bytes_at rsegs m (q + 16) (le4 (Z_to_bv 64 d)) -> wr_at rsegs m q 24 -> q mod 8 = 0 -> 0 < text ->
  text + len < 2 ^ 62 -> text <= p <= text + len -> Z.of_nat (length tb) = len -> bytes_at rsegs m text tb ->
  q + 24 <= text \/ text + len <= q -> 0 <= d <= 32 -> pj_in_ok rsegs m q text len p d tb.
Proof.
  intros m q text len p d tb H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj (conj H11 I) H12))))))))))).
Qed.

Lemma pip_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d v : Z) (tb : list byte) (o : bool),
  pj_in_ok rsegs m q text len p d tb -> p < text + len -> 0 < v -> v mod 8 = 0 ->
  wr_at rsegs m v 4 -> wr_at rsegs m (bv_unsigned sp - 96) 96 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 4 ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 4)] (bv_unsigned sp - 96) 96 ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
       (31 < d /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
        chg [(bv_unsigned sp - 96, bv_unsigned sp); (v, v + 4); (q + 16, q + 20)] m m' /\
        bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) /\ pi_q m' q text len p (d + 1) tb)
    \/ (d <= 31 /\
        ms' = MS (mkR (Z_to_bv 64 0x16d70) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 q)
                   (Z_to_bv 64 v) (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 (if o then 1 else 0))
                   (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x162e0) fc None m' (seg_rom rsegs) /\
        chg [(bv_unsigned sp - 96, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m m' /\
        bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) /\
        pj_in_ok rsegs m' q text len (p + 1) (d + 1) tb /\
        pi_frame m' (bv_unsigned sp - 96) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 (if o then 1 else 0)) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16cdc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len p d v
    tb o HP Hp V0 V8 WV WF DV DF.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DV, DF, DQ.
  pose proof WV as (WV0 & WV1 & _). pose proof WF as (WF0 & WF1 & _).
  pose proof (chg_refl [(bv_unsigned sp - 96, bv_unsigned sp); (v, v + 4); (q + 16, q + 20)] m) as CHr.
  pose proof (chg_refl [(bv_unsigned sp - 96, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m) as CH.
  step.
  replace (Z_to_bv 64 (bv_unsigned sp + -96)) with (Z_to_bv 64 (bv_unsigned sp - 96)) by (f_equal; lia).
  sok (bv_unsigned sp - 96 + 88) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 80) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 72) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 64) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 56) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 48) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 40) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 32) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 24) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 16) 8%nat. step. mst.
  sok (bv_unsigned sp - 96 + 8) 8%nat. step. mst.
  step. if_cases H0; [pip_trap H0|].
  step. step. step. step. if_cases H1; [pip_trap H1|].
  step. step. rewrite pip_snez. step. step.
  sok v 4%nat. step. mst.
  lazymatch goal with H : bytes_at rsegs ?mm v (le4 ?w) |- _ =>
    assert (TY : bytes_at rsegs mm v (le4 (Z_to_bv 64 (if o then 6 else 5)))) by (destruct o; exact H); clear H end.
  step. if_cases H2; [pip_trap H2|].
  pose proof (pip_rd4 _ _ _ Q16) as RD.
  step. rewrite (pip_sx32 d) by lia.
  step. rewrite (pip_addiw d 1) by lia.
  step. if_cases H3; [rewrite pip_lts in H3 by lia; apply Z.ltb_lt in H3; lia|].
  sok (q + 16) 4%nat. step. mst.
  step. step. step.
  if_cases HD; rewrite pip_lts in HD by lia.
  - apply Z.ltb_lt in HD.
    eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    rewrite pip_sp_back.
    apply evt_done. do 6 eexists. left. split; [lia|]. split; [reflexivity|].
    split; [exact CHr|]. split; [exact TY|].
    unfold pi_q. repeat (split; [eassumption|]). eassumption.
  - apply Z.ltb_ge in HD.
    pose proof (pip_rd8 _ _ _ Q0) as R0.
    step. step. step. step. if_cases H4; [pip_trap H4|].
    sok q 8%nat. step. mst.
    step. step.
    apply evt_done. do 6 eexists. right. split; [lia|]. split; [reflexivity|].
    split; [exact CH|]. split; [exact TY|]. split; [apply pip_mk_in; first [ eassumption | lia ] | frame_pack].
Qed.

Ltac w1_ret q d :=
  let HN := fresh "HN" in let HO := fresh "HO" in let RD := fresh "RD" in
  step; step; if_cases HN; [ first [ pip_trap HN | rewrite pip_ne_m1 in HN by lia; discriminate ] | ];
  lazymatch goal with Q : bytes_at rsegs _ (q + 16) (le4 _) |- _ => pose proof (pip_rd4 _ _ _ Q) as RD end;
  step; rewrite (pip_sx32 d) by lia;
  step; step; rewrite (pip_addiw d (-1)) by lia;
  sok q 8%nat; step; mst;
  step; if_cases HO;
  [ first [ rewrite pip_lts in HO by lia; apply negb_true_iff, Z.ltb_ge in HO; lia | pip_trap HO ] | ];
  step; sok (q + 16) 4%nat; step; mst; step;
  eapply evt_cut; [ eapply pip_epi; frame_pack | ];
  let ms' := fresh "ms'" in intros ms' ->;
  apply evt_done; do 3 eexists; left;
  split; [lia|];
  split; [ lazymatch goal with RC : ReaderRes.rest_at _ _ _ = _ :: _, HE : _ = bv_unsigned _ |- _ =>
             rewrite RC, <- HE; reflexivity end |];
  split; [reflexivity|]; split; [eassumption|];
  apply pip_mk_in; first [ eassumption | lia ].

Ltac w1_call :=
  step; step;
  apply evt_done; do 3 eexists; right;
  split; [ lazymatch goal with RC : ReaderRes.rest_at _ _ _ = _ :: _, HE : _ <> bv_unsigned _ |- _ =>
             let c := fresh "c" in let r := fresh "r" in let Hc := fresh "Hc" in
             intros c r Hc; rewrite RC in Hc; injection Hc as <- _; cbn [closer]; lia end |];
  split; reflexivity.

Lemma pip_w1 : forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len x d v : Z) (tb : list byte) (o : bool)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len x d tb -> 1 <= d -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  (f + 96 <= q \/ q + 24 <= f) ->
  evt rsegs
    (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
       (x < text + len /\ ReaderRes.rest_at tb text x = closer o :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
        chg [(q, q + 8); (q + 16, q + 20)] m m' /\ pj_in_ok rsegs m' q text len (x + 1) (d - 1) tb)
       \/ ((forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> closer o) /\
        ms' = MS (mkR (Z_to_bv 64 0x16dcc) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v)
                   (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) s3
                   s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1670c) fc None m' (seg_rom rsegs) /\
        m' = m))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (if o then 1 else 0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16d70) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len x d v
    tb o r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP Hd FR DF.
  pose proof (pj_in_ok_bounds rsegs m q text len x d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ.
  destruct FR as (FP & F9 & F8 & F7 & F6 & F5 & F4 & F3 & F2 & F1 & F0 & FRa).
  pose proof (bytes_at_bound rsegs m _ _ FRa) as FBR. rewrite length_le8 in FBR. cbn in FBR.
  pose proof WQ as (WQ0 & WQ1 & _).
  pose proof (chg_refl [(q, q + 8); (q + 16, q + 20)] m) as CH.
  pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
  step. step. step.
  if_cases H1; rewrite pip_ltu in H1 by lia.
  - apply negb_true_iff, Z.ltb_ge in H1.
    step. step. apply evt_done. do 3 eexists. right.
    split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
    split; reflexivity.
  - apply negb_false_iff, Z.ltb_lt in H1.
    step. if_cases H2; [pip_trap H2|].
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB).
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
    destruct o.
    + step. step. if_false. step. step.
      if_cases H3; rewrite pip_eqb_byte in H3 by lia.
      * apply Z.eqb_eq in H3. w1_ret q d.
      * apply Z.eqb_neq in H3. step. w1_call.
    + step. step. if_true. step. step.
      if_cases H3; rewrite pip_eqb_byte in H3 by lia.
      * apply negb_true_iff, Z.eqb_neq in H3. w1_call.
      * apply negb_false_iff, Z.eqb_eq in H3. w1_ret q d.
Qed.

Lemma pip_g1 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  evt rsegs
    (fun ms' =>
       (bv_unsigned a0 <> 0 /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 s3 a1 a2 a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
       \/ (bv_unsigned a0 = 0 /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                   (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 56) (Z_to_bv 64 44) (Z_to_bv 64 (-1))
                   (Z_to_bv 64 34) (Z_to_bv 64 58) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16e24) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16dcc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 FR.
  step. if_cases H1; zify_cond H1.
  - do 7 step. apply evt_done. right. split; [lia|reflexivity].
  - eapply evt_mono; [apply pip_epi; exact FR|]. intros ms' ->. left. split; [lia|reflexivity].
Qed.

Lemma pip_mset : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v vals n : Z),
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  0 < vals -> 0 <= n -> vals + 56 * n < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists a3' a4' a5' : word,
       ms' = MS (mkR (Z_to_bv 64 0x16f04) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) (Z_to_bv 64 (vals + 56 * n))
                  (Z_to_bv 64 0) (Z_to_bv 64 56) a3' a4' a5' a6 a7 s2 s3 s4 (Z_to_bv 64 56) s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (Z_to_bv 64 0x22924) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 56) s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v vals n
    HV HN Hv Hn Hb.
  pose proof (bytes_at_bound rsegs m _ _ HV) as BV. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in BV, BN. cbn in BV, BN.
  apply pip_rd8 in HV, HN.
  step. step. step. rewrite (pip_shl n 3) by lia.
  step. rewrite (pip_shl n 6) by lia.
  step.
  lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 6)) - bv_unsigned (Z_to_bv 64 (n * 2 ^ 3)))] =>
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 6)) - bv_unsigned (Z_to_bv 64 (n * 2 ^ 3))))
      with (Z_to_bv 64 (56 * n)) by (rewrite !unsigned_lit by lia; f_equal; lia)
  end.
  step. step. step.
  step. if_cases F1; [pip_trap F1|].
  step. if_cases F2; [pip_trap F2|].
  do 5 step. if_cases F3.
  { zify_cond F3. rewrite !pip_signed in F3 by lia. rewrite !Z.shiftr_div_pow2 in F3 by lia.
    rewrite !Z.div_small in F3 by lia. rewrite !Z.mod_0_l in F3 by lia. rewrite Z.lxor_0_l in F3. lia. }
  apply negb_false_iff, pip_eqb0 in F3. rewrite F3.
  step. step. replace (56 * n + vals) with (vals + 56 * n) by lia.
  apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma pip_head : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (o : bool),
  evt rsegs
    (fun ms' =>
       (o = false /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0))
                   s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16ec0) fc None m (seg_rom rsegs))
       \/ (o = true /\
        ms' = MS (mkR (Z_to_bv 64 0x16e30) sp gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (if o then 1 else 0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x162e0) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0))
           s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16e24) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q o.
  destruct o.
  - step. if_false. step. step. apply evt_done. right. split; reflexivity.
  - step. if_true. apply evt_done. left. split; reflexivity.
Qed.

Lemma pip_w2 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len x d : Z) (tb : list byte)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len x d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  evt rsegs
    (fun ms' =>
       ((forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 34) /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (text + len))
                   a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
       \/ (x < text + len /\ ReaderRes.rest_at tb text x = 34 :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR (Z_to_bv 64 0x16e54) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 q)
                   (Z_to_bv 64 (text + len)) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 (Z_to_bv 64 34)
                   s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16ff8) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
           (Z_to_bv 64 34) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16e30) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len x d
    tb r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP FR.
  pose proof (pj_in_ok_bounds rsegs m q text len x d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
  step. step. step. step.
  if_cases H1; rewrite pip_ltu in H1 by lia.
  - apply negb_true_iff, Z.ltb_ge in H1.
    eapply evt_cut; [eapply pip_epi; exact FR | intros ms' ->].
    apply evt_done. left.
    split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate | reflexivity].
  - apply negb_false_iff, Z.ltb_lt in H1.
    step. if_cases H2; [pip_trap H2|].
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB).
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
    step. step. if_cases H3; rewrite pip_eqb_byte_r in H3 by lia.
    + apply negb_true_iff, Z.eqb_neq in H3.
      eapply evt_cut; [eapply pip_epi; exact FR | intros ms' ->].
      apply evt_done. left.
      split; [intros c r Hc; rewrite RC in Hc; injection Hc as <- _; lia | reflexivity].
    + apply negb_false_iff, Z.eqb_eq in H3.
      step. step. apply evt_done. right.
      split; [lia|]. split; [rewrite RC, H3; reflexivity | reflexivity].
Qed.

Lemma pip_ps : forall (ra gp tp t0 t1 t2 k a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len p d v keys n : Z) (tb : list byte)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len p d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  wr_at rsegs m (keys + 8 * n) 8 -> 0 < keys -> keys mod 8 = 0 -> 0 <= n < 2 ^ 60 ->
  disjoint_from [(q, q + 24); (text, text + len); (f, f + 96)] (keys + 8 * n) 8 ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
       chg [(keys + 8 * n, keys + 8 * n + 8)] m m' /\ bytes_at rsegs m' (keys + 8 * n) (le8 k) /\
       pj_in_ok rsegs m' q text len p d tb /\
       ((bv_unsigned k = 0 /\
         ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 s3 a1' a2' a3' a4' a5' a6 a7
                    c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs))
        \/ (bv_unsigned k <> 0 /\
         ms' = MS (mkR (Z_to_bv 64 0x16e9c) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v)
                    (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6 a7 s2 s3 (Z_to_bv 64 1152921504606846976) s5 s6 s7 s8 s9
                    s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x162e0) fc None m' (seg_rom rsegs) /\
         pi_frame m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) k a1 a2 a3 a4 a5 a6 a7 s2 s3
           (Z_to_bv 64 1152921504606846976) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16e54) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 k a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len p d v
    keys n tb r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP FR HK HN WK K0 K8 Hn DK.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ, DK.
  destruct FR as (FP & F9 & F8 & F7 & F6 & F5 & F4 & F3 & F2 & F1 & F0 & FRa).
  pose proof (bytes_at_bound rsegs m _ _ FRa) as FBR. pose proof (bytes_at_bound rsegs m _ _ HK) as BK.
  pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in FBR, BK, BN. cbn in FBR, BK, BN.
  pose proof WQ as (WQ0 & WQ1 & _). pose proof WK as (WK0 & WK1 & _).
  pose proof (pip_rd8 _ _ _ HN) as RN. pose proof (pip_rd8 _ _ _ HK) as RK.
  pose proof (chg_refl [(keys + 8 * n, keys + 8 * n + 8)] m) as CH.
  step. step. step. rewrite pip_sh3 by lia. step. step. step.
  step. if_cases G1; [pip_trap G1|].
  step. step. step. if_cases G2; [pip_trap G2|].
  step. if_cases G3; [pip_trap G3|].
  step. if_cases G4; [pip_trap G4|].
  step. step. if_cases G5; [pip_trap G5|].
  sok (keys + 8 * n) 8%nat. step. mst.
  step. if_cases HZ; zify_cond HZ.
  - eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. do 6 eexists. split; [exact CH|]. split; [eassumption|].
    split; [apply pip_mk_in; first [ eassumption | lia ]|].
    left. split; [lia | reflexivity].
  - step. step. apply evt_done. do 6 eexists. split; [exact CH|]. split; [eassumption|].
    split; [apply pip_mk_in; first [ eassumption | lia ]|].
    right. split; [lia|]. split; [reflexivity | frame_pack].
Qed.

Lemma pip_w3 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len x d : Z) (tb : list byte)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len x d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  (f + 96 <= q \/ q + 24 <= f) ->
  evt rsegs
    (fun ms' => exists (a1' : word) (m' : word -> option byte),
       ((forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 58) /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 x) a1' a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 58) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16f98) fc None m' (seg_rom rsegs) /\ m' = m)
       \/ (x < text + len /\ ReaderRes.rest_at tb text x = 58 :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 (x + 1)) a1' a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 58) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16ec0) fc None m' (seg_rom rsegs) /\
        chg [(q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len (x + 1) d tb /\
        pi_frame m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
           (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 58) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16e9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 s11 t3 t4 t5 t6 F fc m f q text len x d
    tb r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP FR DF.
  pose proof (pj_in_ok_bounds rsegs m q text len x d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ.
  destruct FR as (FP & F9 & F8 & F7 & F6 & F5 & F4 & F3 & F2 & F1 & F0 & FRa).
  pose proof (bytes_at_bound rsegs m _ _ FRa) as FBR. rewrite length_le8 in FBR. cbn in FBR.
  pose proof WQ as (WQ0 & WQ1 & _).
  pose proof (chg_refl [(q, q + 8)] m) as CH.
  pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
  step. step. step.
  if_cases H1; rewrite pip_ltu in H1 by lia.
  - apply negb_true_iff, Z.ltb_ge in H1.
    apply evt_done. do 2 eexists. left.
    split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
    split; reflexivity.
  - apply negb_false_iff, Z.ltb_lt in H1.
    step. if_cases H2; [pip_trap H2|].
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB).
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
    step. step. if_cases H3; rewrite pip_eqb_byte_r in H3 by lia.
    + apply negb_true_iff, Z.eqb_neq in H3.
      apply evt_done. do 2 eexists. left.
      split; [intros c r Hc; rewrite RC in Hc; injection Hc as <- _; lia|].
      split; reflexivity.
    + apply negb_false_iff, Z.eqb_eq in H3.
      step. if_cases H4; [ first [ pip_trap H4 | rewrite pip_ne_m1 in H4 by lia; discriminate ] | ].
      step. sok q 8%nat. step. mst.
      apply evt_done. do 2 eexists. right.
      split; [lia|]. split; [rewrite RC, H3; reflexivity|].
      split; [reflexivity|]. split; [eassumption|].
      split; [apply pip_mk_in; first [ eassumption | lia ] | frame_pack].
Qed.

Lemma pip_fk : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 k : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v keys n : Z),
  bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  bytes_at rsegs m (keys + 8 * n) (le8 k) -> 0 < keys -> keys mod 8 = 0 -> 0 <= n < 2 ^ 60 ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' : word),
       ms' = MS (mkR (Z_to_bv 64 0x16fd8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) k a1' a2' a3' a4' a5 a6 a7 s2 s3
                  (Z_to_bv 64 1152921504606846976) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15ea8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1152921504606846976)
           s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16f98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 k F fc m v keys n
    HK HN HS K0 K8 Hn.
  pose proof (bytes_at_bound rsegs m _ _ HK) as BK. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  pose proof (bytes_at_bound rsegs m _ _ HS) as BS.
  rewrite length_le8 in BK, BN, BS. cbn in BK, BN, BS.
  apply pip_rd8 in HK, HN, HS.
  step. step. step. rewrite pip_sh3 by lia. step. step. step.
  step. if_cases G1; [pip_trap G1|].
  step. step. step. if_cases G2; [pip_trap G2|].
  step. if_cases G3; [pip_trap G3|].
  step. if_cases G4; [pip_trap G4|].
  step. step. if_cases G5; [pip_trap G5|].
  step. step. apply evt_done. do 4 eexists. reflexivity.
Qed.

Lemma pip_ff : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 s3 a1 a2 a3 a4 a5 a6 a7
                          c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16fd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 FR.
  step. apply pip_epi. exact FR.
Qed.

Lemma pip_ms : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q v vals n : Z),
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  0 < vals -> 0 <= n -> vals + 56 * n < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists a2' a3' a4' a5' : word,
       ms' = MS (mkR (Z_to_bv 64 0x16f48) sp gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 q)
                  (Z_to_bv 64 (vals + 56 * n)) a2' a3' a4' a5' a6 a7 s2 s3 s4 (Z_to_bv 64 56) s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (Z_to_bv 64 0x16044) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 56)
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16f04) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q v vals n
    HV HN Hv Hn Hb.
  pose proof (bytes_at_bound rsegs m _ _ HV) as BV. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in BV, BN. cbn in BV, BN.
  apply pip_rd8 in HV, HN.
  step. step. step. rewrite (pip_shl n 3) by lia.
  step. rewrite (pip_shl n 6) by lia.
  step.
  lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 6)) - bv_unsigned (Z_to_bv 64 (n * 2 ^ 3)))] =>
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 6)) - bv_unsigned (Z_to_bv 64 (n * 2 ^ 3))))
      with (Z_to_bv 64 (56 * n)) by (rewrite !unsigned_lit by lia; f_equal; lia)
  end.
  step. step. step.
  step. if_cases F1; [pip_trap F1|].
  step. if_cases F2; [pip_trap F2|].
  do 5 step. if_cases F3.
  { zify_cond F3. rewrite !pip_signed in F3 by lia. rewrite !Z.shiftr_div_pow2 in F3 by lia.
    rewrite !Z.div_small in F3 by lia. rewrite !Z.mod_0_l in F3 by lia. rewrite Z.lxor_0_l in F3. lia. }
  step. step. replace (56 * n + vals) with (vals + 56 * n) by lia.
  apply evt_done. do 4 eexists. reflexivity.
Qed.

Lemma pip_pv : forall (ra gp tp t0 t1 t2 w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len p d v n : Z) (tb : list byte)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len p d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) -> wr_at rsegs m (v + 40) 8 -> 0 <= n -> n + 1 < 2 ^ 64 ->
  disjoint_from [(q, q + 24); (text, text + len); (f, f + 96)] (v + 40) 8 ->
  evt rsegs
    (fun ms' => exists m' : word -> option byte,
       chg [(v + 40, v + 48)] m m' /\ bytes_at rsegs m' (v + 40) (le8 (Z_to_bv 64 (n + 1))) /\
       pj_in_ok rsegs m' q text len p d tb /\
       ((bv_unsigned w <> 0 /\
         ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 1))
                    a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs))
        \/ (bv_unsigned w = 0 /\
         ms' = MS (mkR (Z_to_bv 64 0x16f64) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 q)
                    (Z_to_bv 64 (n + 1)) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x162e0) fc None m' (seg_rom rsegs) /\
         pi_frame m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16f48) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len p d
    v n tb r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP FR HN WN Hn Hn1 DN.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ, DN.
  destruct FR as (FP & F9 & F8 & F7 & F6 & F5 & F4 & F3 & F2 & F1 & F0 & FRa).
  pose proof (bytes_at_bound rsegs m _ _ FRa) as FBR. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in FBR, BN. cbn in FBR, BN.
  pose proof WQ as (WQ0 & WQ1 & _). pose proof WN as (WN0 & WN1 & _).
  pose proof (pip_rd8 _ _ _ HN) as RN.
  pose proof (chg_refl [(v + 40, v + 48)] m) as CH.
  step. step. sok (v + 40) 8%nat. step. mst.
  step. step. if_cases H1; zify_cond H1.
  - eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. eexists. split; [exact CH|]. split; [eassumption|].
    split; [apply pip_mk_in; first [ eassumption | lia ]|].
    left. split; [lia | reflexivity].
  - step. step. apply evt_done. eexists. split; [exact CH|]. split; [eassumption|].
    split; [apply pip_mk_in; first [ eassumption | lia ]|].
    right. split; [lia|]. split; [reflexivity | frame_pack].
Qed.

Ltac w4_ret :=
  eapply evt_cut; [ eapply pip_epi; frame_pack | ];
  let ms' := fresh "ms'" in intros ms' ->;
  apply evt_done; do 3 eexists; right; left;
  split; [ lazymatch goal with RC : ReaderRes.rest_at _ _ _ = _ :: _ |- _ =>
             let c := fresh "c" in let r := fresh "r" in let Hc := fresh "Hc" in
             intros c r Hc; rewrite RC in Hc; injection Hc as <- _; cbn [closer]; split; lia end |];
  split; reflexivity.

Lemma pip_w4 : forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len x d v : Z) (tb : list byte) (o : bool)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pj_in_ok rsegs m q text len x d tb -> 1 <= d -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  (f + 96 <= q \/ q + 24 <= f) ->
  evt rsegs
    (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
       (x < text + len /\ ReaderRes.rest_at tb text x = closer o :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
        chg [(q, q + 8); (q + 16, q + 20)] m m' /\ pj_in_ok rsegs m' q text len (x + 1) (d - 1) tb)
       \/ ((forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 44 /\ c <> closer o) /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (-1)) a1' a2' a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\ m' = m)
       \/ (x < text + len /\ ReaderRes.rest_at tb text x = 44 :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR (Z_to_bv 64 0x16f90) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 v)
                   a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 (-1)) s4 s5 (Z_to_bv 64 44)
                   (Z_to_bv 64 (-1)) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1670c) fc None m' (seg_rom rsegs) /\
        chg [(q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len (x + 1) d tb /\
        pi_frame m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 (-1)) s4 s5 (Z_to_bv 64 44) (Z_to_bv 64 (-1)) s8 s9
           s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16f64) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len x d v tb o
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 HP Hd FR DF.
  pose proof (pj_in_ok_bounds rsegs m q text len x d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ.
  destruct FR as (FP & F9 & F8 & F7 & F6 & F5 & F4 & F3 & F2 & F1 & F0 & FRa).
  pose proof (bytes_at_bound rsegs m _ _ FRa) as FBR. rewrite length_le8 in FBR. cbn in FBR.
  pose proof WQ as (WQ0 & WQ1 & _).
  pose proof (chg_refl [(q, q + 8); (q + 16, q + 20)] m) as CH.
  pose proof (chg_refl [(q, q + 8)] m) as CHc.
  pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
  step. step. step.
  if_cases H1; rewrite pip_ltu in H1 by lia.
  - apply negb_true_iff, Z.ltb_ge in H1.
    eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. do 3 eexists. right. left.
    split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
    split; reflexivity.
  - apply negb_false_iff, Z.ltb_lt in H1.
    step. if_cases H2; [pip_trap H2|].
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB).
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
    step. step. if_cases H3; rewrite pip_eqb_byte_r in H3 by lia.
    + apply negb_true_iff, Z.eqb_neq in H3.
      destruct o.
      * step. if_false. step. step. step.
        if_cases H4; rewrite pip_eqb_byte in H4 by lia.
        -- apply Z.eqb_eq in H4. w1_ret q d.
        -- apply Z.eqb_neq in H4. step. w4_ret.
      * step. if_true. step. step.
        if_cases H4; rewrite pip_eqb_byte in H4 by lia.
        -- apply Z.eqb_eq in H4. w1_ret q d.
        -- apply Z.eqb_neq in H4. step. w4_ret.
    + apply negb_false_iff, Z.eqb_eq in H3.
      step. if_cases H4; [ first [ pip_trap H4 | rewrite pip_ne_m1 in H4 by lia; discriminate ] | ].
      step. sok q 8%nat. step. mst. step. step.
      apply evt_done. do 3 eexists. right. right.
      split; [lia|]. split; [rewrite RC, H3; reflexivity|].
      split; [reflexivity|]. split; [eassumption|].
      split; [apply pip_mk_in; first [ eassumption | lia ] | frame_pack].
Qed.

Lemma pip_g2 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
  evt rsegs
    (fun ms' =>
       (bv_unsigned a0 = 0 /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                   s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16e24) fc None m (seg_rom rsegs))
       \/ (bv_unsigned a0 <> 0 /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 96)) gp tp t0 t1 t2 c0 c1 s3 a1 a2 a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16f90) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 FR.
  step. if_cases H1; zify_cond H1.
  - apply evt_done. left. split; [lia|reflexivity].
  - step. eapply evt_mono; [apply pip_epi; exact FR|]. intros ms' ->. right. split; [lia|reflexivity].
Qed.
