From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
Import ListNotations.
Open Scope Z_scope.

Definition WSM : Z := 4294977024.

Definition pres (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Definition chg (W : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  munch W m m' /\ wmono rsegs m m' /\ pres m m'.

Definition ws_out (m : word -> option byte) (q text len : Z) (tb : list byte) (x x' : Z)
    (m' : word -> option byte) : Prop :=
  x <= x' <= text + len /\ ReaderRes.rest_at tb text x' = skip (ReaderRes.rest_at tb text x) /\
  bytes_at rsegs m' q (le8 (Z_to_bv 64 x')) /\ chg [(q, q + 8)] m m'.

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

Lemma chg_trans : forall W m1 m2 m3, chg W m1 m2 -> chg W m2 m3 -> chg W m1 m3.
Proof.
  intros W m1 m2 m3 (A1 & A2 & A3) (B1 & B2 & B3). split; [eapply munch_trans; eassumption|].
  split; [eapply wmono_trans; eassumption|]. intros x Hx. apply B3, A3, Hx.
Qed.

Lemma chg_weaken : forall W W' m m', sub_fp W W' -> chg W m m' -> chg W' m m'.
Proof. intros W W' m m' Hs (H1 & H2 & H3). split; [eapply munch_weaken; eassumption|]. split; assumption. Qed.

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

Lemma pip_rest_end : forall tb text len, Z.of_nat (length tb) = len -> ReaderRes.rest_at tb text (text + len) = [].
Proof.
  intros tb text len H. unfold ReaderRes.rest_at, ReaderRes.zb.
  replace (Z.to_nat (text + len - text)) with (length tb) by lia. rewrite skipn_all. reflexivity.
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

Lemma pip_ltu32 : forall b : byte, bv_ltu (Z_to_bv 64 32) (zxb b) = (32 <? bv_unsigned b).
Proof.
  intros b. pose proof (pip_byte b). unfold bv_ltu, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma pip_ws_big : forall c, 32 < c -> ws c = false.
Proof.
  intros c H. unfold ws.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)), (proj2 (Z.eqb_neq c 13)) by lia.
  reflexivity.
Qed.

Lemma pip_wsbit : forall b : byte, bv_unsigned b <= 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (zxb b) mod 64)))) 1))
    (Z_to_bv 64 0) = negb (ws (bv_unsigned b)).
Proof.
  intros b H. pose proof (pip_byte b) as HB. unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  remember (bv_unsigned b) as c eqn:Ec. clear Ec.
  assert (C : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/
              c = 31 \/ c = 32) by lia.
  repeat destruct C as [C|C]; subst c; vm_compute; reflexivity.
Qed.

Lemma pip_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

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

Ltac ws_nows :=
  lazymatch goal with
  | RC : ReaderRes.rest_at ?tb ?text ?x = bv_unsigned ?b :: _, HW : ws (bv_unsigned ?b) = false,
    HQ : bytes_at rsegs ?m ?q (le8 (Z_to_bv 64 ?x)) |- _ =>
      apply evt_done; do 3 eexists; split; [reflexivity|];
      split; [lia|]; split; [rewrite RC; cbn [skip]; rewrite HW; reflexivity|];
      split; [exact HQ | apply chg_refl]
  end.

Ltac ws_body IH :=
  lazymatch goal with
  | HT : bytes_at rsegs ?m ?text ?tb, Hx : ?text <= ?x < _, HQ : bytes_at rsegs ?m ?q (le8 (Z_to_bv 64 ?x)) |- _ =>
    let b := fresh "b" in let Hb := fresh "Hb" in let RB := fresh "RB" in
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB);
    let RC := fresh "RC" in
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC;
    pose proof (pip_byte b);
    pose proof (chg_refl [(q, q + 8)] m) as CH;
    unfold WSM; step; step;
    let H1 := fresh "H1" in
    if_cases H1; rewrite pip_ltu32 in H1;
    [ apply Z.ltb_lt in H1;
      let HW := fresh "HW" in pose proof (pip_ws_big (bv_unsigned b) H1) as HW; ws_nows
    | apply Z.ltb_ge in H1; step; step; step;
      let H2 := fresh "H2" in
      if_cases H2; rewrite pip_wsbit in H2 by lia;
      [ apply negb_true_iff in H2; ws_nows
      | apply negb_false_iff in H2; step; sok q 8%nat; step; mst; step;
        let H3 := fresh "H3" in
        if_cases H3; rewrite pip_eqb in H3 by lia;
        [ apply negb_true_iff, Z.eqb_neq in H3;
          eapply evt_mono; [ eapply (IH (x + 1)); [ lia | eassumption | eassumption | eassumption | lia ] | ];
          let ms' := fresh "ms'" in let x' := fresh "x'" in let r' := fresh "r'" in let m' := fresh "m'" in
          let E := fresh "E" in let O1 := fresh "O" in let O2 := fresh "O" in let O3 := fresh "O" in
          let O4 := fresh "O" in
          intros ms' (x' & r' & m' & E & O1 & O2 & O3 & O4);
          exists x', r', m'; split; [exact E|];
          split; [lia|]; split; [rewrite O2, RC; cbn [skip]; rewrite H2; reflexivity|];
          split; [exact O3 | eapply chg_trans; eassumption]
        | apply negb_false_iff, Z.eqb_eq in H3;
          apply evt_done; do 3 eexists; split; [reflexivity|];
          split; [lia|];
          split; [rewrite RC; cbn [skip]; rewrite H2;
                  lazymatch goal with HL : Z.of_nat (length tb) = ?len |- _ =>
                    rewrite H3, (pip_rest_end tb text len HL); reflexivity end|];
          split; [eassumption | eassumption] ] ] ]
  end.

Lemma pip_wsA : forall (ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len x : Z) (tb : list byte),
  Z.of_nat (length tb) = len -> 0 < text -> text + len < 2 ^ 62 -> (q + 8 <= text \/ text + len <= q) ->
  text <= x < text + len ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 x)) -> wr_at rsegs m q 8 -> bytes_at rsegs m text tb ->
  evt rsegs
    (fun ms' => exists x' a5' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 (Z_to_bv 64 x') (Z_to_bv 64 (text + len))
                  (Z_to_bv 64 32) (Z_to_bv 64 WSM) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x163e0) fc None m' (seg_rom rsegs) /\
       ws_out m q text len tb x x' m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 (Z_to_bv 64 x) (Z_to_bv 64 (text + len))
           (Z_to_bv 64 32) (Z_to_bv 64 WSM) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x163c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len x tb
    HL HT0 HT1 HD Hx HQ WQ HT.
  pose proof WQ as (WQ0 & WQ1 & _).
  unfold ws_out.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a5 m Hx HQ WQ HT Hn.
  induction n as [|n IH]; intros x a5 m Hx HQ WQ HT Hn; [lia|].
  ws_body IH.
Qed.

Lemma pip_wsB : forall (ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len x : Z) (tb : list byte),
  Z.of_nat (length tb) = len -> 0 < text -> text + len < 2 ^ 62 -> (q + 8 <= text \/ text + len <= q) ->
  text <= x < text + len ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 x)) -> wr_at rsegs m q 8 -> bytes_at rsegs m text tb ->
  evt rsegs
    (fun ms' => exists x' a2' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x') (Z_to_bv 64 (text + len)) a2' a3 a4 a5
                  a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1644c) fc None m' (seg_rom rsegs) /\
       ws_out m q text len tb x x' m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x) (Z_to_bv 64 (text + len)) a2 a3 a4 a5
           a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x1642c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len x tb
    HL HT0 HT1 HD Hx HQ WQ HT.
  pose proof WQ as (WQ0 & WQ1 & _).
  unfold ws_out.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a2 m Hx HQ WQ HT Hn.
  induction n as [|n IH]; intros x a2 m Hx HQ WQ HT Hn; [lia|].
  ws_body IH.
Qed.

Lemma pip_wsC : forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len x : Z) (tb : list byte),
  Z.of_nat (length tb) = len -> 0 < text -> text + len < 2 ^ 62 -> (q + 8 <= text \/ text + len <= q) ->
  text <= x < text + len ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 x)) -> wr_at rsegs m q 8 -> bytes_at rsegs m text tb ->
  evt rsegs
    (fun ms' => exists x' a4' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x') a1 a2 (Z_to_bv 64 (text + len)) a4' a5
                  a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x164a4) fc None m' (seg_rom rsegs) /\
       ws_out m q text len tb x x' m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x) a1 a2 (Z_to_bv 64 (text + len)) a4 a5
           a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16484) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len x tb
    HL HT0 HT1 HD Hx HQ WQ HT.
  pose proof WQ as (WQ0 & WQ1 & _).
  unfold ws_out.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a4 m Hx HQ WQ HT Hn.
  induction n as [|n IH]; intros x a4 m Hx HQ WQ HT Hn; [lia|].
  ws_body IH.
Qed.

Lemma pip_wsD : forall (ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len x : Z) (tb : list byte),
  Z.of_nat (length tb) = len -> 0 < text -> text + len < 2 ^ 62 -> (q + 8 <= text \/ text + len <= q) ->
  text <= x < text + len ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 x)) -> wr_at rsegs m q 8 -> bytes_at rsegs m text tb ->
  evt rsegs
    (fun ms' => exists x' a2' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x') (Z_to_bv 64 (text + len)) a2' a3 a4 a5
                  a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1653c) fc None m' (seg_rom rsegs) /\
       ws_out m q text len tb x x' m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 x) (Z_to_bv 64 (text + len)) a2 a3 a4 a5
           a6 a7 s2 s3 (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x1651c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len x tb
    HL HT0 HT1 HD Hx HQ WQ HT.
  pose proof WQ as (WQ0 & WQ1 & _).
  unfold ws_out.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a2 m Hx HQ WQ HT Hn.
  induction n as [|n IH]; intros x a2 m Hx HQ WQ HT Hn; [lia|].
  ws_body IH.
Qed.

Definition pi_frame (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word) : Prop :=
  bytes_at rsegs m f (le8 c8) /\ bytes_at rsegs m (f + 8) (le8 c7) /\ bytes_at rsegs m (f + 16) (le8 c6) /\
  bytes_at rsegs m (f + 24) (le8 c5) /\ bytes_at rsegs m (f + 32) (le8 c4) /\ bytes_at rsegs m (f + 40) (le8 c3) /\
  bytes_at rsegs m (f + 48) (le8 c2) /\ bytes_at rsegs m (f + 56) (le8 c1) /\ bytes_at rsegs m (f + 64) (le8 c0) /\
  bytes_at rsegs m (f + 72) (le8 r0).

Lemma pip_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                          c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16578) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof (bytes_at_bound rsegs m _ _ P0) as B0. pose proof (bytes_at_bound rsegs m _ _ P9) as B9.
  rewrite length_le8 in B0, B9. cbn in B0, B9.
  apply pip_rd8 in P0, P1, P2, P3, P4, P5, P6, P7, P8, P9.
  do 13 step. apply evt_done. reflexivity.
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

Lemma pip_rest_ge : forall tb text len x, Z.of_nat (length tb) = len -> text + len <= x ->
  ReaderRes.rest_at tb text x = [].
Proof.
  intros tb text len x H Hx. unfold ReaderRes.rest_at, ReaderRes.zb. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma pip_sx32 : forall d, 0 <= d < 2 ^ 31 -> sx32 (Z_to_bv 64 d) = Z_to_bv 64 d.
Proof.
  intros d H. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

Lemma pip_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))), (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma pip_snez : forall o : bool, v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (if o then 1 else 0)) = Z_to_bv 64 (if o then 1 else 0).
Proof. intros [|]; first [ reflexivity | apply bv_eq; vm_compute; reflexivity ]. Qed.

Lemma pip_eqb_byte : forall c (b : byte), 0 <= c < 2 ^ 64 -> bv_eqb (Z_to_bv 64 c) (zxb b) = (c =? bv_unsigned b).
Proof. intros c b H. pose proof (pip_byte b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_wr_sub : forall m a n k n', wr_at rsegs m a n -> 0 <= k -> k + n' <= n -> 0 <= n' -> wr_at rsegs m (a + k) n'.
Proof.
  intros m a n k n' (H1 & H2 & H3) Hk Hn Hn'. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H3. lia.
Qed.

Ltac frame_pack := unfold pi_frame; repeat (split; [eassumption|]); eassumption.

Ltac t98_ret q :=
  step; step; sok q 8%nat; step; mst; sok (q + 16) 4%nat; step; mst;
  eapply evt_cut; [ eapply pip_epi; frame_pack | ];
  let ms' := fresh "ms'" in intros ms' ->;
  apply evt_done; do 4 eexists; left;
  split; [lia|]; split; [ lazymatch goal with RC : ReaderRes.rest_at _ _ _ = _ :: _, HE : _ = bv_unsigned _ |- _ =>
                            rewrite RC, <- HE; reflexivity end |];
  split; [reflexivity|]; split; [eassumption|]; split; eassumption.

Ltac t98_call :=
  step; step;
  apply evt_done; do 4 eexists; right;
  split; [ lazymatch goal with RC : ReaderRes.rest_at _ _ _ = _ :: _, HE : _ <> bv_unsigned _ |- _ =>
             let c := fresh "c" in let r := fresh "r" in let Hc := fresh "Hc" in
             intros c r Hc; rewrite RC in Hc; injection Hc as <- _; cbn [closer]; lia end |];
  split; reflexivity.

Lemma pip_t98 : forall (ra gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len x d v : Z) (tb : list byte) (o : bool)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  Z.of_nat (length tb) = len -> 0 < text -> text + len < 2 ^ 62 -> text <= x <= text + len -> 0 <= d <= 31 ->
  (q + 24 <= text \/ text + len <= q) -> (f + 80 <= q \/ q + 24 <= f) ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 x)) -> wr_at rsegs m q 24 -> bytes_at rsegs m text tb ->
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
       (x < text + len /\ ReaderRes.rest_at tb text x = closer o :: ReaderRes.rest_at tb text (x + 1) /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
        chg [(q, q + 8); (q + 16, q + 20)] m m' /\ bytes_at rsegs m' q (le8 (Z_to_bv 64 (x + 1))) /\
        bytes_at rsegs m' (q + 16) (le4 (Z_to_bv 64 d)))
       \/ ((forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> closer o) /\
        ms' = MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 q)
                   (Z_to_bv 64 v) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v)
                   s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15e4c) fc None m' (seg_rom rsegs) /\
        m' = m))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (Z_to_bv 64 d) (Z_to_bv 64 x)
           (Z_to_bv 64 (text + len)) a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v)
           s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x163e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len x d v tb o
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 HL HT0 HT1 Hx Hd DQ DF HQ WQ HT FR.
  pose proof WQ as (WQ0 & WQ1 & _).
  destruct FR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (bytes_at_bound rsegs m _ _ F0) as FB0. pose proof (bytes_at_bound rsegs m _ _ F9) as FB9.
  rewrite length_le8 in FB0, FB9. cbn in FB0, FB9.
  pose proof (chg_refl [(q, q + 8); (q + 16, q + 20)] m) as CH.
  step.
  if_cases H1; rewrite pip_ltu in H1 by lia.
  - apply negb_true_iff, Z.ltb_ge in H1.
    step. step. apply evt_done. do 4 eexists. right.
    split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
    split; reflexivity.
  - apply negb_false_iff, Z.ltb_lt in H1.
    destruct (pip_rdt m text tb x HT ltac:(lia)) as (b & Hb & RB).
    pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
    destruct o.
    + step. step. if_false. step. step.
      if_cases H2; rewrite pip_eqb_byte in H2 by lia.
      * apply Z.eqb_eq in H2. t98_ret q.
      * apply Z.eqb_neq in H2. t98_call.
    + step. step. if_true. step. step.
      if_cases H2; rewrite pip_eqb_byte in H2 by lia.
      * apply negb_true_iff, Z.eqb_neq in H2. t98_call.
      * apply negb_false_iff, Z.eqb_eq in H2. t98_ret q.
Qed.

Lemma pip_sp_back : forall sp : word, Z_to_bv 64 (bv_unsigned sp - 80 + 80) = sp.
Proof. intros sp. rewrite Z.sub_add. apply Z_to_bv_bv_unsigned. Qed.

Lemma pip_wr_pre : forall m a n n', wr_at rsegs m a n -> 0 <= n' <= n -> wr_at rsegs m a n'.
Proof. intros m a n n' (H1 & H2 & H3) Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H3. lia. Qed.

Lemma pip_sub4 : forall a b c d, sub_fp [(a, b); (c, d)] [(a, b); (c, d)].
Proof. intros a b c d x H. exact H. Qed.

Ltac entry_fin tb x WSO CHX :=
  eapply evt_cut;
  [ eapply pip_t98 with (tb := tb); [ lia | lia | lia | lia | lia | lia | lia | eassumption | eassumption | eassumption | frame_pack ]
  | ];
  let ms' := fresh "ms'" in let a1' := fresh "a1'" in let a2' := fresh "a2'" in let a3' := fresh "a3'" in
  let m' := fresh "m'" in
  let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in let E4 := fresh "E" in
  let E5 := fresh "E" in let E6 := fresh "E" in
  intros ms' (a1' & a2' & a3' & m' & [(E1 & E2 & E3 & E4 & E5 & E6) | (E1 & E2 & E3)]);
  [ apply evt_done; do 6 eexists; right; left; split; [lia|]; exists x;
    split; [rewrite E3, pip_sp_back; reflexivity|];
    split; [lia|]; split; [rewrite <- WSO; exact E2|];
    split; [ eapply chg_trans; [exact CHX | eapply chg_weaken; [|exact E4]];
             intros z Hz; cbn [outside] in Hz |- *; tauto |];
    let MU := fresh "MU" in let WM := fresh "WM" in let PR := fresh "PR" in
    destruct E4 as (MU & WM & PR);
    lazymatch type of MU with munch _ ?m0 _ => transport_after_call rsegs m0 m' MU WM end;
    split; [eassumption|];
    apply pip_mk_in; first [ eassumption | lia ]
  | subst m'; apply evt_done; do 6 eexists; right; right; split; [lia|]; exists x;
    split; [rewrite E2; reflexivity|];
    split; [lia|]; split; [exact WSO|]; split; [exact E1|]; split; [exact CHX|];
    split; [eassumption|]; split; [apply pip_mk_in; first [ eassumption | lia ] | frame_pack ] ].

Lemma pip_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d v : Z) (tb : list byte) (o : bool),
  pj_in_ok rsegs m q text len p d tb -> p < text + len ->
  wr_at rsegs m v 4 -> wr_at rsegs m (bv_unsigned sp - 80) 80 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 4 ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 4)] (bv_unsigned sp - 80) 80 ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
       (31 < d /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
        chg [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q + 16, q + 20)] m m' /\
        bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) /\ pi_q m' q text len p (d + 1) tb)
    \/ (d <= 31 /\ exists x,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
        p + 1 <= x < text + len /\
        skip (ReaderRes.rest_at tb text (p + 1)) = closer o :: ReaderRes.rest_at tb text (x + 1) /\
        chg [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m m' /\
        bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) /\ pj_in_ok rsegs m' q text len (x + 1) d tb)
    \/ (d <= 31 /\ exists x,
        ms' = MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 (-1))
                   (Z_to_bv 64 q) (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 (if o then 1 else 0))
                   (Z_to_bv 64 v) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15e4c) fc None m' (seg_rom rsegs) /\
        p + 1 <= x <= text + len /\
        ReaderRes.rest_at tb text x = skip (ReaderRes.rest_at tb text (p + 1)) /\
        (forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> closer o) /\
        chg [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m m' /\
        bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) /\ pj_in_ok rsegs m' q text len x (d + 1) tb /\
        pi_frame m' (bv_unsigned sp - 80) ra s0 s1 s2 s3 s4 s5 s6 s7 s8))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 (if o then 1 else 0)) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len p d v
    tb o HP Hp WV WF DV DF.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DV, DF, DQ.
  pose proof WV as (WV0 & WV1 & _). pose proof WF as (WF0 & WF1 & _).
  pose proof (chg_refl [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q + 16, q + 20)] m) as CHr.
  pose proof (chg_refl [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m) as CH.
  step.
  replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (bv_unsigned sp - 80)) by (f_equal; lia).
  sok (bv_unsigned sp - 80 + 72) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 64) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 56) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 48) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 40) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 32) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 24) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 16) 8%nat. step. mst.
  sok (bv_unsigned sp - 80 + 8) 8%nat. step. mst.
  sok (bv_unsigned sp - 80) 8%nat. step. mst.
  step. step. step. step. rewrite pip_snez.
  pose proof (pip_rd4 _ _ _ Q16) as RD.
  step. rewrite (pip_sx32 d) by lia.
  step. step.
  sok v 4%nat. step. mst.
  lazymatch goal with H : bytes_at rsegs ?mm v (le4 ?w) |- _ =>
    assert (TY : bytes_at rsegs mm v (le4 (Z_to_bv 64 (if o then 6 else 5)))) by (destruct o; exact H); clear H end.
  step.
  sok (q + 16) 4%nat. step. mst.
  step. step.
  if_cases HD; rewrite pip_lts in HD by lia.
  - apply Z.ltb_lt in HD.
    eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    rewrite pip_sp_back.
    apply evt_done. do 6 eexists. left. split; [lia|]. split; [reflexivity|].
    split; [exact CHr|]. split; [exact TY|].
    unfold pi_q. repeat (split; [eassumption|]). eassumption.
  - apply Z.ltb_ge in HD.
    pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
    step. step. step.
    sok q 8%nat. step. mst.
    step.
    if_cases H2; rewrite pip_ltu in H2 by lia.
    + apply negb_true_iff, Z.ltb_ge in H2.
      assert (WSO : ReaderRes.rest_at tb text (p + 1) = skip (ReaderRes.rest_at tb text (p + 1)))
        by (rewrite (pip_rest_ge tb text len (p + 1) HL ltac:(lia)); reflexivity).
      entry_fin tb (p + 1) WSO CH.
    + apply negb_false_iff, Z.ltb_lt in H2.
      step. step. step. step.
      eapply evt_cut;
        [ eapply pip_wsA with (tb := tb); [ lia | lia | lia | lia | lia | eassumption | apply (pip_wr_pre _ _ 24 8 WQ); lia | eassumption ]
        | ].
      intros ms' (x & a5' & mw & -> & WX1 & WSO & WX3 & WX4).
      lazymatch type of WX4 with chg _ ?m0 _ =>
        assert (CHX : chg [(bv_unsigned sp - 80, bv_unsigned sp); (v, v + 4); (q, q + 8); (q + 16, q + 20)] m mw)
          by (eapply chg_trans; [exact CH | eapply chg_weaken; [|exact WX4]];
              intros z Hz; cbn [outside] in Hz |- *; tauto);
        let MU := fresh "MU" in let WM := fresh "WM" in let PR := fresh "PR" in
        destruct WX4 as (MU & WM & PR);
        transport_after_call rsegs m0 mw MU WM; clear MU WM PR
      end.
      entry_fin tb x WSO CHX.
Qed.

Lemma pip_wrap_sub : forall a b c,
  Z_to_bv 64 (c + (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b))) = Z_to_bv 64 (c + (a - b)).
Proof.
  intros a b c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite (Zplus_mod c (a mod bv_modulus 64 - b mod bv_modulus 64)), (Zplus_mod c (a - b)), (Zminus_mod a b).
  reflexivity.
Qed.

Lemma pip_sh : forall n k, 0 <= n < 2 ^ 64 -> 0 <= k -> Z.shiftl (bv_unsigned (Z_to_bv 64 n)) k = n * 2 ^ k.
Proof. intros n k H Hk. rewrite unsigned_lit by lia. apply Z.shiftl_mul_pow2. exact Hk. Qed.

Lemma pip_m56 : forall vals n, 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (vals + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 6)) -
                      bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 3)))) =
  Z_to_bv 64 (vals + 56 * n).
Proof.
  intros vals n H. rewrite pip_wrap_sub, !pip_sh by lia. f_equal.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
Qed.

Lemma pip_sh3 : forall n, 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 3) = Z_to_bv 64 (8 * n).
Proof. intros n H. rewrite pip_sh by lia. f_equal. change (2 ^ 3) with 8. lia. Qed.

Lemma pip_eqb_byte_r : forall c (b : byte), 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof. intros c b H. pose proof (pip_byte b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pip_ff : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                          c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x165b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 FR.
  step. apply pip_epi. exact FR.
Qed.

Lemma pip_g2 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  evt rsegs
    (fun ms' =>
       (bv_unsigned a0 = 0 /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                   s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1641c) fc None m (seg_rom rsegs))
       \/ (bv_unsigned a0 <> 0 /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16558) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 FR.
  step. if_cases H1; zify_cond H1.
  - apply evt_done. left. split; [lia|reflexivity].
  - step. eapply evt_mono; [apply pip_epi; exact FR|]. intros ms' ->. right. split; [lia|reflexivity].
Qed.

Lemma pip_g1 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  evt rsegs
    (fun ms' =>
       (bv_unsigned a0 <> 0 /\
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m (seg_rom rsegs))
       \/ (bv_unsigned a0 = 0 /\
        ms' = MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 8388627) a1 a2 a3 a4 a5 a6 a7 s2 s3
                   (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 34) (Z_to_bv 64 WSM) (Z_to_bv 64 58)
                   s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1641c) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x163fc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 FR.
  step. if_cases H1; zify_cond H1.
  - eapply evt_mono; [apply pip_epi; exact FR|]. intros ms' ->. left. split; [lia|reflexivity].
  - do 7 step. apply evt_done. right. split; [lia|reflexivity].
Qed.

Lemma pip_mset : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v vals n : Z),
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> 0 <= n -> 0 <= vals -> vals + 56 * n < 2 ^ 64 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x164e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (vals + 56 * n)) (Z_to_bv 64 0)
                          (Z_to_bv 64 56) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x21e6c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v) s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x164c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v vals n
    HV Hn Hv Hb.
  pose proof (bytes_at_bound rsegs m _ _ HV) as BV. rewrite length_le8 in BV. cbn in BV.
  apply pip_rd8 in HV.
  do 8 step. rewrite pip_m56 by lia. apply evt_done. reflexivity.
Qed.

Lemma pip_ms : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q v vals n : Z),
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  0 <= n -> 0 <= vals -> vals + 56 * n < 2 ^ 64 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16500) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 q)
                          (Z_to_bv 64 (vals + 56 * n)) (Z_to_bv 64 (8 * n)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v)
                          s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15994) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v) s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x164e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q v vals n
    HV HN Hn Hv Hb.
  pose proof (bytes_at_bound rsegs m _ _ HV) as BV. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in BV, BN. cbn in BV, BN.
  apply pip_rd8 in HV, HN.
  do 8 step. rewrite pip_m56, pip_sh3 by lia. apply evt_done. reflexivity.
Qed.

Lemma pip_head : forall (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len p d v vals n : Z) (tb : list byte)
    (o : bool) (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pj_in_ok rsegs m q text len p d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 -> (f + 80 <= q \/ q + 24 <= f) ->
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  0 <= n -> 0 <= vals -> vals + 56 * n < 2 ^ 64 ->
  evt rsegs
    (fun ms' =>
       (o = false /\
        ms' = MS (mkR (Z_to_bv 64 0x164e0) (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q)
                   (Z_to_bv 64 (vals + 56 * n)) (Z_to_bv 64 0) (Z_to_bv 64 56) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v) (Z_to_bv 64 32) s5 (Z_to_bv 64 34)
                   (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x21e6c) fc None m (seg_rom rsegs))
       \/ (o = true /\ exists x (a2' : word) (m' : word -> option byte),
        ms' = MS (mkR (Z_to_bv 64 0x16460) (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 q)
                   (Z_to_bv 64 (text + len)) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v)
                   (Z_to_bv 64 32) s5 (Z_to_bv 64 34) (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x165e8) fc None m' (seg_rom rsegs) /\
        p <= x < text + len /\ skip (ReaderRes.rest_at tb text p) = 34 :: ReaderRes.rest_at tb text (x + 1) /\
        chg [(q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len x d tb)
       \/ (o = true /\ exists x (a2' : word) (m' : word -> option byte),
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 (Z_to_bv 64 (text + len)) a2' a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
        p <= x <= text + len /\ ReaderRes.rest_at tb text x = skip (ReaderRes.rest_at tb text p) /\
        (forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 34) /\
        chg [(q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len x d tb))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v) (Z_to_bv 64 32) s5 (Z_to_bv 64 34) (Z_to_bv 64 WSM) s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1641c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len p d v vals n tb o
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 HP FR DF HV HN Hn Hv Hvn.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ.
  pose proof FR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (bytes_at_bound rsegs m _ _ F0) as FB0. pose proof (bytes_at_bound rsegs m _ _ F9) as FB9.
  rewrite length_le8 in FB0, FB9. cbn in FB0, FB9.
  pose proof WQ as (WQ0 & WQ1 & _).
  destruct o.
  - step. if_false.
    pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
    step. step. step.
    if_cases H1; rewrite pip_ltu in H1 by lia.
    + apply negb_true_iff, Z.ltb_ge in H1.
      step. if_cases H2; rewrite pip_ltu in H2 by lia; [ | apply negb_false_iff, Z.ltb_lt in H2; lia ].
      eapply evt_cut; [eapply pip_epi; exact FR | intros ms' ->].
      apply evt_done. right. right. split; [reflexivity|]. exists p, a2, m.
      split; [reflexivity|]. split; [lia|].
      rewrite (pip_rest_ge tb text len p HL ltac:(lia)).
      split; [reflexivity|]. split; [intros c r Hc; discriminate|].
      split; [apply chg_refl|]. apply pip_mk_in; first [ eassumption | lia ].
    + apply negb_false_iff, Z.ltb_lt in H1.
      eapply evt_cut;
        [ eapply pip_wsB with (tb := tb);
          [ lia | lia | lia | lia | lia | eassumption | apply (pip_wr_pre _ _ 24 8 WQ); lia | eassumption ]
        | ].
      intros ms' (x & a2' & mw & -> & WX1 & WSO & WX3 & WX4).
      pose proof WX4 as CHX.
      lazymatch type of WX4 with chg _ ?m0 _ =>
        let MU := fresh "MU" in let WM := fresh "WM" in let PR := fresh "PR" in
        destruct WX4 as (MU & WM & PR);
        transport_after_call rsegs m0 mw MU WM; clear MU WM PR
      end.
      step. if_cases H2; rewrite pip_ltu in H2 by lia.
      * apply negb_true_iff, Z.ltb_ge in H2.
        eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
        apply evt_done. right. right. split; [reflexivity|]. exists x, a2', mw.
        split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
        split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
        split; [exact CHX|]. apply pip_mk_in; first [ eassumption | lia ].
      * apply negb_false_iff, Z.ltb_lt in H2.
        destruct (pip_rdt mw text tb x HT ltac:(lia)) as (b & Hb & RB).
        pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
        step. step. if_cases H3; rewrite pip_eqb_byte_r in H3 by lia.
        -- apply negb_true_iff, Z.eqb_neq in H3.
           eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
           apply evt_done. right. right. split; [reflexivity|]. exists x, a2', mw.
           split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
           split; [intros c r Hc; rewrite RC in Hc; injection Hc as <- _; lia|].
           split; [exact CHX|]. apply pip_mk_in; first [ eassumption | lia ].
        -- apply negb_false_iff, Z.eqb_eq in H3.
           step. step. apply evt_done. right. left. split; [reflexivity|]. exists x, a2', mw.
           split; [reflexivity|]. split; [lia|]. split; [rewrite <- WSO, RC, H3; reflexivity|].
           split; [exact CHX|]. apply pip_mk_in; first [ eassumption | lia ].
  - step. if_true.
    pose proof (pip_rd8 _ _ _ HN) as RN. pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
    rewrite length_le8 in BN. cbn in BN.
    step.
    eapply evt_mono; [ apply pip_mset; [ exact HV | lia | lia | lia ] | ].
    intros ms' ->. left. split; reflexivity.
Qed.

Lemma pip_ps : forall (ra gp tp t0 t1 t2 s0 k a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len p d v keys vals n : Z) (tb : list byte)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pj_in_ok rsegs m q text len p d tb -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 -> (f + 80 <= q \/ q + 24 <= f) ->
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) -> wr_at rsegs m (keys + 8 * n) 8 ->
  0 <= n -> 0 <= vals -> vals + 56 * n < 2 ^ 64 ->
  disjoint_from [(q, q + 24); (text, text + len); (f, f + 80); (v + 24, v + 32)] (keys + 8 * n) 8 ->
  disjoint_from [(q, q + 8)] (v + 24) 8 ->
  evt rsegs
    (fun ms' =>
       (bv_unsigned k = 0 /\ exists m' : word -> option byte,
        ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 (Z_to_bv 64 n) (Z_to_bv 64 (keys + 8 * n))
                   (Z_to_bv 64 (8 * n)) a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc r0) fc None m' (seg_rom rsegs) /\
        chg [(keys + 8 * n, keys + 8 * n + 8)] m m' /\ bytes_at rsegs m' (keys + 8 * n) (le8 k) /\
        pj_in_ok rsegs m' q text len p d tb)
       \/ (bv_unsigned k <> 0 /\ exists x (a3' a4' : word) (m' : word -> option byte),
        ms' = MS (mkR (Z_to_bv 64 0x165b4) (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) k (Z_to_bv 64 n)
                   (Z_to_bv 64 (keys + 8 * n)) a3' a4' a5 a6 a7 s2 (Z_to_bv 64 v) (Z_to_bv 64 32) s5 s6
                   (Z_to_bv 64 WSM) (Z_to_bv 64 58) s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x157f8) fc None m' (seg_rom rsegs) /\
        p <= x <= text + len /\ ReaderRes.rest_at tb text x = skip (ReaderRes.rest_at tb text p) /\
        (forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 58) /\
        chg [(keys + 8 * n, keys + 8 * n + 8); (q, q + 8)] m m' /\ bytes_at rsegs m' (keys + 8 * n) (le8 k) /\
        pj_in_ok rsegs m' q text len x d tb)
       \/ (bv_unsigned k <> 0 /\ exists x (a3' a4' : word) (m' : word -> option byte),
        ms' = MS (mkR (Z_to_bv 64 0x164e0) (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 (vals + 56 * n))
                   (Z_to_bv 64 0) (Z_to_bv 64 56) a3' a4' a5 a6 a7 s2 (Z_to_bv 64 v) (Z_to_bv 64 32) s5 s6
                   (Z_to_bv 64 WSM) (Z_to_bv 64 58) s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x21e6c) fc None m' (seg_rom rsegs) /\
        p <= x < text + len /\ skip (ReaderRes.rest_at tb text p) = 58 :: ReaderRes.rest_at tb text (x + 1) /\
        chg [(keys + 8 * n, keys + 8 * n + 8); (q, q + 8)] m m' /\ bytes_at rsegs m' (keys + 8 * n) (le8 k) /\
        pj_in_ok rsegs m' q text len (x + 1) d tb))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) k a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v)
           (Z_to_bv 64 32) s5 s6 (Z_to_bv 64 WSM) (Z_to_bv 64 58) s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16460) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 k a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len p d v keys vals n
    tb r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 HP FR DF HV HK HN WK Hn Hv Hvn DK DV.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ, DK, DV.
  pose proof FR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (bytes_at_bound rsegs m _ _ F0) as FB0. pose proof (bytes_at_bound rsegs m _ _ F9) as FB9.
  pose proof (bytes_at_bound rsegs m _ _ HV) as BV. pose proof (bytes_at_bound rsegs m _ _ HK) as BK.
  pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in FB0, FB9, BV, BK, BN. cbn in FB0, FB9, BV, BK, BN.
  pose proof WQ as (WQ0 & WQ1 & _). pose proof WK as (WK0 & WK1 & _).
  pose proof (pip_rd8 _ _ _ HN) as RN. pose proof (pip_rd8 _ _ _ HK) as RK.
  pose proof (chg_refl [(keys + 8 * n, keys + 8 * n + 8)] m) as CH1.
  pose proof (chg_refl [(keys + 8 * n, keys + 8 * n + 8); (q, q + 8)] m) as CH.
  step. step. step. rewrite pip_sh3 by lia. step.
  sok (keys + 8 * n) 8%nat. step. mst.
  step. if_cases H1; zify_cond H1.
  - eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. left. split; [lia|]. eexists. split; [reflexivity|].
    split; [exact CH1|]. split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
  - pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
    step. step. step. if_cases H2; rewrite pip_ltu in H2 by lia.
    + apply negb_true_iff, Z.ltb_ge in H2.
      step. if_cases H3; rewrite pip_ltu in H3 by lia; [ | apply negb_false_iff, Z.ltb_lt in H3; lia ].
      lazymatch goal with H : bytes_at rsegs _ (keys + 8 * n) _ |- _ => pose proof (pip_rd8 _ _ _ H) as RKk end.
      step. step. apply evt_done. right. left. split; [lia|]. exists p. do 3 eexists.
      split; [reflexivity|]. split; [lia|].
      rewrite (pip_rest_ge tb text len p HL ltac:(lia)).
      split; [reflexivity|]. split; [intros c r Hc; discriminate|].
      split; [exact CH|]. split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
    + apply negb_false_iff, Z.ltb_lt in H2.
      eapply evt_cut;
        [ eapply pip_wsC with (tb := tb);
          [ lia | lia | lia | lia | lia | eassumption | apply (pip_wr_pre _ _ 24 8 WQ); lia | eassumption ]
        | ].
      intros ms' (x & a4' & mw & -> & WX1 & WSO & WX3 & WX4).
      lazymatch type of WX4 with chg _ ?m0 _ =>
        assert (CHX : chg [(keys + 8 * n, keys + 8 * n + 8); (q, q + 8)] m mw)
          by (eapply chg_trans; [exact CH | eapply chg_weaken; [|exact WX4]];
              intros z Hz; cbn [outside] in Hz |- *; tauto);
        let MU := fresh "MU" in let WM := fresh "WM" in let PR := fresh "PR" in
        destruct WX4 as (MU & WM & PR);
        transport_after_call rsegs m0 mw MU WM; clear MU WM PR
      end.
      clear CH CH1.
      step. if_cases H3; rewrite pip_ltu in H3 by lia.
      * apply negb_true_iff, Z.ltb_ge in H3.
        lazymatch goal with H : bytes_at rsegs _ (keys + 8 * n) _ |- _ => pose proof (pip_rd8 _ _ _ H) as RKk end.
        step. step. apply evt_done. right. left. split; [lia|]. exists x. do 3 eexists.
        split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
        split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
        split; [exact CHX|]. split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
      * apply negb_false_iff, Z.ltb_lt in H3.
        destruct (pip_rdt mw text tb x HT ltac:(lia)) as (b & Hb & RB).
        pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
        step. step. if_cases H4; rewrite pip_eqb_byte_r in H4 by lia.
        -- apply negb_true_iff, Z.eqb_neq in H4.
           lazymatch goal with H : bytes_at rsegs _ (keys + 8 * n) _ |- _ => pose proof (pip_rd8 _ _ _ H) as RKk end.
           step. step. apply evt_done. right. left. split; [lia|]. exists x. do 3 eexists.
           split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
           split; [intros c r Hc; rewrite RC in Hc; injection Hc as <- _; lia|].
           split; [exact CHX|]. split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
        -- apply negb_false_iff, Z.eqb_eq in H4.
           step. sok q 8%nat. step. mst. step.
           eapply evt_mono; [ apply pip_mset; [ eassumption | lia | lia | lia ] | ].
           intros ms' ->. right. right. split; [lia|]. exists x. do 3 eexists.
           split; [reflexivity|]. split; [lia|]. split; [rewrite <- WSO, RC, H4; reflexivity|].
           split; [eassumption|]. split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
Qed.

Lemma pip_cl : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o : bool),
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (closer o)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 (if o then 1 else 0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x165c8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x165b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o.
  destruct o; step; [ if_false; step; step | if_true; step ]; apply evt_done; reflexivity.
Qed.

Lemma pip_pv : forall (ra gp tp t0 t1 t2 s0 w a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q text len p d v n : Z) (tb : list byte) (o : bool)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  pj_in_ok rsegs m q text len p d tb -> 1 <= d -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  (f + 80 <= q \/ q + 24 <= f) ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) -> wr_at rsegs m (v + 40) 8 -> 0 <= n -> n + 1 < 2 ^ 64 ->
  disjoint_from [(q, q + 24); (text, text + len); (f, f + 80)] (v + 40) 8 ->
  evt rsegs
    (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
       ((bv_unsigned w <> 0 /\
         ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 (Z_to_bv 64 (n + 1)) a2 a3 a4 a5 a6 a7
                    c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
         chg [(v + 40, v + 48)] m m' /\ pj_in_ok rsegs m' q text len p d tb)
        \/ (bv_unsigned w = 0 /\ exists x,
         ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 a1' a2' a3 a4 a5 a6 a7
                    c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
         p <= x <= text + len /\ ReaderRes.rest_at tb text x = skip (ReaderRes.rest_at tb text p) /\
         (forall c r, ReaderRes.rest_at tb text x = c :: r -> c <> 44 /\ c <> closer o) /\
         chg [(v + 40, v + 48); (q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len x d tb)
        \/ (bv_unsigned w = 0 /\ exists x,
         ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                    c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
         p <= x < text + len /\ skip (ReaderRes.rest_at tb text p) = closer o :: ReaderRes.rest_at tb text (x + 1) /\
         chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] m m' /\
         pj_in_ok rsegs m' q text len (x + 1) (d - 1) tb)
        \/ (bv_unsigned w = 0 /\ exists x,
         ms' = MS (mkR (Z_to_bv 64 0x16558) (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 v) a1' a2'
                    a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v) (Z_to_bv 64 32) (Z_to_bv 64 44) s6
                    (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15e4c) fc None m' (seg_rom rsegs) /\
         p <= x < text + len /\ skip (ReaderRes.rest_at tb text p) = 44 :: ReaderRes.rest_at tb text (x + 1) /\
         chg [(v + 40, v + 48); (q, q + 8)] m m' /\ pj_in_ok rsegs m' q text len (x + 1) d tb))
       /\ bytes_at rsegs m' (v + 40) (le8 (Z_to_bv 64 (n + 1))))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) w a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0))
           (Z_to_bv 64 v) (Z_to_bv 64 32) (Z_to_bv 64 44) s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x16500) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 w a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q text len p d v n tb o
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 HP Hd1 FR DF HN WN Hn Hn1 DN.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb HP) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  destruct HP as (Q0 & Q8 & Q16 & WQ & Qm & T0 & T1 & Tp & HL & HT & DQ & Dd).
  cbn [disjoint_from] in DQ, DN.
  pose proof FR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (bytes_at_bound rsegs m _ _ F0) as FB0. pose proof (bytes_at_bound rsegs m _ _ F9) as FB9.
  pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in FB0, FB9, BN. cbn in FB0, FB9, BN.
  pose proof WQ as (WQ0 & WQ1 & _). pose proof WN as (WN0 & WN1 & _).
  pose proof (pip_rd8 _ _ _ HN) as RN.
  pose proof (chg_refl [(v + 40, v + 48)] m) as CH1.
  pose proof (chg_refl [(v + 40, v + 48); (q, q + 8)] m) as CH2.
  pose proof (chg_refl [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] m) as CH3.
  step. step. sok (v + 40) 8%nat. step. mst.
  step. if_cases H1; zify_cond H1.
  - eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. exists a1, a2. eexists. split; [|eassumption]. left. split; [lia|]. split; [reflexivity|].
    split; [exact CH1|]. apply pip_mk_in; first [ eassumption | lia ].
  - pose proof (pip_rd8 _ _ _ Q0) as R0. pose proof (pip_rd8 _ _ _ Q8) as R8.
    step. step. step. if_cases H2; rewrite pip_ltu in H2 by lia.
    + apply negb_true_iff, Z.ltb_ge in H2.
      step. if_cases H3; rewrite pip_ltu in H3 by lia; [ | apply negb_false_iff, Z.ltb_lt in H3; lia ].
      eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
      apply evt_done. do 3 eexists. split; [|eassumption]. right. left. split; [lia|]. exists p.
      split; [reflexivity|]. split; [lia|]. rewrite (pip_rest_ge tb text len p HL ltac:(lia)).
      split; [reflexivity|]. split; [intros c r Hc; discriminate|].
      split; [exact CH2|]. apply pip_mk_in; first [ eassumption | lia ].
    + apply negb_false_iff, Z.ltb_lt in H2.
      eapply evt_cut;
        [ eapply pip_wsD with (tb := tb);
          [ lia | lia | lia | lia | lia | eassumption | apply (pip_wr_pre _ _ 24 8 WQ); lia | eassumption ]
        | ].
      intros ms' (x & a2' & mw & -> & WX1 & WSO & WX3 & WX4).
      lazymatch type of WX4 with chg _ ?m0 _ =>
        assert (CHX2 : chg [(v + 40, v + 48); (q, q + 8)] m mw)
          by (eapply chg_trans; [exact CH2 | eapply chg_weaken; [|exact WX4]];
              intros z Hz; cbn [outside] in Hz |- *; tauto);
        assert (CHX3 : chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] m mw)
          by (eapply chg_trans; [exact CH3 | eapply chg_weaken; [|exact WX4]];
              intros z Hz; cbn [outside] in Hz |- *; tauto);
        let MU := fresh "MU" in let WM := fresh "WM" in let PR := fresh "PR" in
        destruct WX4 as (MU & WM & PR);
        transport_after_call rsegs m0 mw MU WM; clear MU WM PR
      end.
      clear CH1 CH2 CH3.
      step. if_cases H3; rewrite pip_ltu in H3 by lia.
      * apply negb_true_iff, Z.ltb_ge in H3.
        eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
        apply evt_done. do 3 eexists. split; [|eassumption]. right. left. split; [lia|]. exists x.
        split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
        split; [intros c r Hc; rewrite (pip_rest_ge tb text len x HL ltac:(lia)) in Hc; discriminate|].
        split; [exact CHX2|]. apply pip_mk_in; first [ eassumption | lia ].
      * apply negb_false_iff, Z.ltb_lt in H3.
        destruct (pip_rdt mw text tb x HT ltac:(lia)) as (b & Hb & RB).
        pose proof (pip_rest_cons tb text x b ltac:(lia) Hb) as RC. pose proof (pip_byte b) as HB.
        step. step. if_cases H4; rewrite pip_eqb_byte_r in H4 by lia.
        -- apply negb_true_iff, Z.eqb_neq in H4.
           eapply evt_cut; [apply pip_cl | intros ms' ->].
           step. if_cases H5; rewrite pip_eqb_byte in H5 by (unfold closer; destruct o; lia).
           ++ apply negb_true_iff, Z.eqb_neq in H5.
              eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
              apply evt_done. do 3 eexists. split; [|eassumption]. right. left. split; [lia|]. exists x.
              split; [reflexivity|]. split; [lia|]. split; [exact WSO|].
              split; [intros c r Hc; rewrite RC in Hc; injection Hc as <- _; split; lia|].
              split; [exact CHX2|]. apply pip_mk_in; first [ eassumption | lia ].
           ++ apply negb_false_iff, Z.eqb_eq in H5.
              pose proof (pip_rd4 _ _ _ Q16) as RD. pose proof (pip_rd8 _ _ _ WX3) as RX.
              step. step. rewrite (pip_sx32 d) by lia. step. step.
              sok q 8%nat. step. mst. sok (q + 16) 4%nat. step. mst. step.
              eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
              apply evt_done. do 3 eexists. split; [|eassumption]. right. right. left. split; [lia|]. exists x.
              split; [reflexivity|]. split; [lia|]. split; [rewrite <- WSO, RC, <- H5; reflexivity|].
              split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
        -- apply negb_false_iff, Z.eqb_eq in H4.
           step. sok q 8%nat. step. mst. step. step.
           apply evt_done. do 3 eexists. split; [|eassumption]. right. right. right. split; [lia|]. exists x.
           split; [reflexivity|]. split; [lia|]. split; [rewrite <- WSO, RC, H4; reflexivity|].
           split; [eassumption|]. apply pip_mk_in; first [ eassumption | lia ].
Qed.
