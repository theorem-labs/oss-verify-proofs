(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 276 of its 307 lines of code are new or changed and 670 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Ledger.
Import ListNotations.
Open Scope Z_scope.

Lemma le1_one : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Definition pmono (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Lemma pmono_write : forall m0 m a bs, pmono m0 m -> pmono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. specialize (H x Hx). clear Hx m0. revert m a H.
  induction bs as [|b bs IH]; intros m a H; cbn; [exact H|].
  apply IH. cbv beta. destruct (bv_eqb x a); [discriminate | exact H].
Qed.

Ltac my_mas :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          try lazymatch goal with
          | HM : munch ?W ?m0 m |- _ =>
              apply (munch_write W m0 m (A + Z.of_nat kn) (cbytes c')) in HM;
              [ | lia | simpl_sizes; lia | simpl_sizes; cbn [inside]; lia ]
          end;
          try lazymatch goal with
          | HW : wmono segs ?m0 m |- _ => apply (wmono_write segs m0 m (wa (A + Z.of_nat kn)) (cbytes c')) in HW
          end;
          try lazymatch goal with
          | HP : pmono ?m0 m |- _ => apply (pmono_write m0 m (wa (A + Z.of_nat kn)) (cbytes c')) in HP
          end;
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.mem_after_store_opt ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => rewrite ?le1_one; fix_lit_store; my_mas
  | _ => idtac
  end.

Lemma rwc8 : forall m A v, bytes_at rsegs m A (le8 v) -> wr_at rsegs m A 8 -> rw_cells rsegs m A [C8 v].
Proof.
  intros m A v HB HW. split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | exact HW].
Qed.

Lemma carve8 : forall m lo hi a, stk rsegs m lo hi -> lo <= hi - 8 -> a = hi - 8 ->
  stk rsegs m lo a /\ exists j, rw_cells rsegs m a [CB 8 j].
Proof.
  intros m lo hi a H Hl ->. destruct (stk_carve rsegs m lo hi 8 H ltac:(lia)) as (H1 & j & H2).
  split; [exact H1|]. exists j. exact H2.
Qed.

Lemma rwc8_bytes : forall m A v v', rw_cells rsegs m A [C8 v] -> v = v' -> bytes_at rsegs m A (le8 v').
Proof.
  intros m A v v' ((_ & HB) & _) <-. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Definition seg1_post (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n cnt fail : Z) (ms' : machine_state) : Prop :=
  exists (a1' a2' a3' : word) (m' : word -> option byte),
    munch [(S + -32, S); (0x33460, 0x33468); (0x231e0, 0x231e8)] m m' /\ wmono rsegs m m' /\
    bytes_at rsegs m' 0x33460 (le8 (Z_to_bv 64 (cnt + 1))) /\
    ( (cnt = fail /\ bytes_at rsegs m' 0x231e0 (le8 (Z_to_bv 64 (2 ^ 64 - 1))) /\
       ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))
    \/ (cnt <> fail /\ 2 ^ 64 - 17 < n /\ bytes_at rsegs m' 0x231e0 (le8 (Z_to_bv 64 fail)) /\
       ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))
    \/ (cnt <> fail /\ n <= 2 ^ 64 - 17 /\ bytes_at rsegs m' 0x231e0 (le8 (Z_to_bv 64 fail)) /\
       bytes_at rsegs m' (S + -8) (le8 ra) /\ bytes_at rsegs m' (S + -16) (le8 s0) /\ bytes_at rsegs m' (S + -24) (le8 s1) /\
       ms' = MS (mkR (Z_to_bv 64 0x13f2c) (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 0x33450)
                     (Z_to_bv 64 (n + 16)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16594) fc None m' (seg_rom rsegs))).

Lemma seg1 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n cnt fail : Z),
  0 <= n < 2 ^ 64 -> 0x33468 <= S + -32 -> S <= 2 ^ 63 -> 0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  stk rsegs m (S + -32) S ->
  bytes_at rsegs m 0x33460 (le8 (Z_to_bv 64 cnt)) -> wr_at rsegs m 0x33460 8 ->
  bytes_at rsegs m 0x231e0 (le8 (Z_to_bv 64 fail)) -> wr_at rsegs m 0x231e0 8 ->
  evt rsegs (seg1_post ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n cnt fail)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ed8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n cnt fail
    Hn HS1 HS2 Hc Hf HK HC HCw HF HFw.
  destruct (carve8 m (S + -32) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (carve8 m (S + -32) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (carve8 m (S + -32) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  clear HK HK1 HK2 HK3.
  apply rwc8 in HC; [|exact HCw]. apply rwc8 in HF; [|exact HFw]. clear HCw HFw.
  assert (HM : munch [(S + -32, S); (0x33460, 0x33468); (0x231e0, 0x231e8)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 13 step.
  if_cases HB; zify_cond HB.
  - step. step. if_cases HB2; zify_cond HB2.
    + do 6 step. apply evt_done. do 4 eexists.
      split; [exact HM|]. split; [exact HW|]. split; [eapply rwc8_bytes; [exact HC | reflexivity]|].
      right; left. split; [lia|]. split; [lia|]. split; [eapply rwc8_bytes; [exact HF | reflexivity]|]. reflexivity.
    + do 2 step. apply evt_done. do 4 eexists.
      split; [exact HM|]. split; [exact HW|]. split; [eapply rwc8_bytes; [exact HC | reflexivity]|].
      right; right. split; [lia|]. split; [lia|]. split; [eapply rwc8_bytes; [exact HF | reflexivity]|].
      split; [eapply rwc8_bytes; [exact K1 | reflexivity]|].
      split; [eapply rwc8_bytes; [exact K2 | reflexivity]|].
      split; [eapply rwc8_bytes; [exact K3 | reflexivity]|]. reflexivity.
  - do 9 step. apply evt_done. do 4 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [eapply rwc8_bytes; [exact HC | reflexivity]|].
    left. split; [lia|]. split; [eapply rwc8_bytes; [exact HF | apply bv_eq; vm_compute; reflexivity]|]. reflexivity.
Qed.

Lemma shr_range : forall n k, 0 <= n < 2 ^ 64 -> 0 <= k -> 0 <= Z.shiftr n k < 2 ^ 64.
Proof.
  intros n k Hn Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ n); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]|lia].
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia.
Qed.

Lemma byte_shr : forall n k, 0 <= n < 2 ^ 64 -> 0 <= k ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 n)) k))) = Z_to_bv 8 (Z.shiftr n k).
Proof.
  intros n k Hn Hk. rewrite (unsigned_lit n) by lia. rewrite unsigned_lit by (apply shr_range; lia). reflexivity.
Qed.

Lemma byte_0 : forall n, 0 <= n < 2 ^ 64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 n)) = Z_to_bv 8 n.
Proof. intros n Hn. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma head_le8 : forall m b n (x0 x1 x2 x3 x4 x5 x6 x7 : byte), 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m b [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
  x0 = Z_to_bv 8 n -> x1 = Z_to_bv 8 (Z.shiftr n 8) -> x2 = Z_to_bv 8 (Z.shiftr n 16) -> x3 = Z_to_bv 8 (Z.shiftr n 24) ->
  x4 = Z_to_bv 8 (Z.shiftr n 32) -> x5 = Z_to_bv 8 (Z.shiftr n 40) -> x6 = Z_to_bv 8 (Z.shiftr n 48) ->
  x7 = Z_to_bv 8 (Z.shiftr n 56) ->
  bytes_at rsegs m b (le8 (Z_to_bv 64 n)).
Proof.
  intros m b n x0 x1 x2 x3 x4 x5 x6 x7 Hn ((_ & HB) & _) -> -> -> -> -> -> -> ->.
  cbn [cells_bytes cbytes app] in HB.
  change (le8 (Z_to_bv 64 n)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 n))).
  rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. exact HB.
Qed.

Definition seg2_post (gp tp t0 t1 t2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n b live peak : Z) (rav s0v s1v : word)
    (ms' : machine_state) : Prop :=
  exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
    munch [(S + -32, S); (b, b + 8); (0x33450, 0x33460)] m m' /\ wmono rsegs m m' /\ pmono m m' /\
    bytes_at rsegs m' b (le8 (Z_to_bv 64 n)) /\
    bytes_at rsegs m' 0x33450 (le8 (Z_to_bv 64 ((live + n) mod 2 ^ 64))) /\
    bytes_at rsegs m' 0x33458 (le8 (Z_to_bv 64 (Z.max peak ((live + n) mod 2 ^ 64)))) /\
    ms' = MS (mkR rav (Z_to_bv 64 S) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (b + 16)) a1' a2' a3' a4' a5' a6' a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom rsegs).

Lemma seg2 : forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n b live peak : Z) (rav s0v s1v : word),
  0 <= n < 2 ^ 64 -> 0x33460 <= S + -32 -> S <= 2 ^ 63 -> 0 < b -> b + 8 <= S + -32 ->
  (b + 8 <= 0x33450 \/ 0x33460 <= b) -> 0 <= live < 2 ^ 64 -> 0 <= peak < 2 ^ 64 ->
  stk rsegs m b (b + 8) ->
  bytes_at rsegs m (S + -8) (le8 rav) -> wr_at rsegs m (S + -8) 8 ->
  bytes_at rsegs m (S + -16) (le8 s0v) -> wr_at rsegs m (S + -16) 8 ->
  bytes_at rsegs m (S + -24) (le8 s1v) -> wr_at rsegs m (S + -24) 8 ->
  bytes_at rsegs m 0x33450 (le8 (Z_to_bv 64 live)) -> wr_at rsegs m 0x33450 8 ->
  bytes_at rsegs m 0x33458 (le8 (Z_to_bv 64 peak)) -> wr_at rsegs m 0x33458 8 ->
  evt rsegs (seg2_post gp tp t0 t1 t2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n b live peak rav s0v s1v)
    (MS (mkR ra (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 0x33450) (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f2c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n b live peak rav s0v s1v
    Hn HS1 HS2 Hb0 Hb1 Hb2 Hl Hp HH K1 K1w K2 K2w K3 K3w HL HLw HP HPw.
  apply rwc8 in K1; [|exact K1w]. apply rwc8 in K2; [|exact K2w]. apply rwc8 in K3; [|exact K3w].
  apply rwc8 in HL; [|exact HLw]. apply rwc8 in HP; [|exact HPw]. clear K1w K2w K3w HLw HPw.
  destruct (stk_bytes rsegs m b (b + 8) HH ltac:(lia)) as (hb & Hlen & Hhb).
  destruct hb as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|? ?]]]]]]]]]; cbn in Hlen; try lia.
  assert (HB : rw_cells rsegs m b [CB 1 [h0]; CB 1 [h1]; CB 1 [h2]; CB 1 [h3]; CB 1 [h4]; CB 1 [h5]; CB 1 [h6]; CB 1 [h7]]).
  { split; [split; [cbn; tauto | exact Hhb] |].
    destruct HH as (_ & _ & HH). split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    exact (proj1 (HH (b + i) ltac:(lia))). }
  clear HH Hhb Hlen.
  assert (HM : munch [(S + -32, S); (b, b + 8); (0x33450, 0x33460)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  assert (HPm : pmono m m) by (intros x Hx; exact Hx).
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 b) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 20 step.
  if_cases HG; zify_cond HG.
  - do 7 step. apply evt_done. do 7 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [exact HPm|].
    split; [eapply head_le8; [exact Hn | exact HB | apply byte_0; lia | apply byte_shr; lia ..]|].
    split; [eapply rwc8_bytes; [exact HL | symmetry; apply Z_to_bv_mod64]|].
    split; [eapply rwc8_bytes; [exact HP | f_equal; lia]|]. reflexivity.
  - do 8 step. apply evt_done. do 7 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [exact HPm|].
    split; [eapply head_le8; [exact Hn | exact HB | apply byte_0; lia | apply byte_shr; lia ..]|].
    split; [eapply rwc8_bytes; [exact HL | symmetry; apply Z_to_bv_mod64]|].
    split; [eapply rwc8_bytes; [exact HP | rewrite Z.max_r by lia; symmetry; apply Z_to_bv_mod64]|]. reflexivity.
Qed.

Fixpoint lsz (l : list (Z * Z)) : Z := match l with [] => 0 | x :: t => snd x + lsz t end.

Lemma lsz_split : forall (f : Z * Z -> bool) l, lsz l = lsz (List.filter f l) + lsz (List.filter (fun y => negb (f y)) l).
Proof.
  intros f l; induction l as [|x t IH]; [reflexivity|].
  cbn [List.filter]. destruct (f x); cbn [negb lsz]; rewrite IH; ring.
Qed.

Lemma filter_len : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros A f l; induction l as [|x t IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma pairwise_filter : forall {A} (R : A -> A -> Prop) f l, YO0f.pairwise R l -> YO0f.pairwise R (List.filter f l).
Proof.
  intros A R f l; induction l as [|x t IH]; cbn; [tauto|]. intros [H1 H2]. destruct (f x); cbn.
  - split; [|apply IH, H2]. intros y Hy. apply filter_In in Hy. apply H1, Hy.
  - apply IH, H2.
Qed.

Lemma disj_sum : forall N l lo hi, (length l <= N)%nat -> YO0f.pairwise YO0f.ranges_disjoint l ->
  (forall x, In x l -> lo <= fst x /\ fst x + snd x <= hi /\ 0 < snd x) -> lo <= hi -> lsz l <= hi - lo.
Proof.
  induction N as [|N IH]; intros l lo hi Hlen Hp Hb Hlh.
  - destruct l; cbn in *; lia.
  - destruct l as [|x t]; cbn [lsz]; [lia|]. cbn [length] in Hlen. destruct Hp as [Hx Ht].
    pose proof (Hb x (or_introl eq_refl)) as (Bx1 & Bx2 & Bx3).
    rewrite (lsz_split (fun y => fst y + snd y <=? fst x) t).
    assert (HL : lsz (List.filter (fun y => fst y + snd y <=? fst x) t) <= fst x - lo).
    { apply IH.
      - pose proof (filter_len (fun y => fst y + snd y <=? fst x) t). lia.
      - apply pairwise_filter, Ht.
      - intros y Hy. apply filter_In in Hy. destruct Hy as (Hy & Hf). apply Z.leb_le in Hf.
        pose proof (Hb y (or_intror Hy)). lia.
      - lia. }
    assert (HR : lsz (List.filter (fun y => negb (fst y + snd y <=? fst x)) t) <= hi - (fst x + snd x)).
    { apply IH.
      - pose proof (filter_len (fun y => negb (fst y + snd y <=? fst x)) t). lia.
      - apply pairwise_filter, Ht.
      - intros y Hy. apply filter_In in Hy. destruct Hy as (Hy & Hf).
        apply Bool.negb_true_iff, Z.leb_gt in Hf.
        pose proof (Hb y (or_intror Hy)). pose proof (Hx y Hy) as Hd. unfold YO0f.ranges_disjoint in Hd. lia.
      - lia. }
    lia.
Qed.

Lemma pairwise_mid : forall {A} (R : A -> A -> Prop) b1 z b2, YO0f.pairwise R (b1 ++ z :: b2) ->
  (forall y, In y (b1 ++ b2) -> R z y \/ R y z) /\ YO0f.pairwise R (b1 ++ b2).
Proof.
  intros A R b1; induction b1 as [|x t IH]; intros z b2 H; cbn in *.
  - destruct H as [H1 H2]. split; [intros y Hy; left; apply H1, Hy | exact H2].
  - destruct H as [H1 H2]. destruct (IH z b2 H2) as [I1 I2]. split.
    + intros y [<-|Hy]; [right; apply H1; apply in_or_app; right; left; reflexivity | apply I1, Hy].
    + split; [|exact I2]. intros y Hy. apply H1. apply in_app_or in Hy. apply in_or_app.
      destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy].
Qed.

Lemma pairwise_In : forall {A} (R : A -> A -> Prop) l u v, YO0f.pairwise R l -> In u l -> In v l -> u <> v ->
  R u v \/ R v u.
Proof.
  intros A R l; induction l as [|x t IH]; intros u v H Hu Hv Hne; [destruct Hu|]. destruct H as [H1 H2].
  destruct Hu as [<-|Hu]; destruct Hv as [<-|Hv].
  - congruence.
  - left; apply H1, Hv.
  - right; apply H1, Hu.
  - apply IH; assumption.
Qed.

Definition shift16 (ak : Z * Z) : Z * Z := (fst ak - 16, snd ak + 16).

Lemma lsz_shift : forall Lam, lsz (map shift16 Lam) = Ledger.lsum Lam + 16 * Z.of_nat (length Lam).
Proof. induction Lam as [|[a k] t IH]; cbn [map lsz Ledger.lsum length shift16 fst snd]; [reflexivity|]. lia. Qed.

Lemma lam_room : forall (b1 b2 : list (Z * Z)) p n Lam lo hi,
  YO0f.pairwise YO0f.ranges_disjoint (b1 ++ (p, n + 16) :: b2) ->
  (forall x, In x (b1 ++ (p, n + 16) :: b2) -> lo <= fst x /\ fst x + snd x <= hi) -> lo <= hi ->
  0 <= n -> NoDup (map fst Lam) ->
  Forall (fun ak => 0 <= snd ak /\ In (fst ak - 16, snd ak + 16) (b1 ++ b2)) Lam ->
  Ledger.lsum Lam + n + 16 <= hi - lo /\ ~ In (p + 16) (map fst Lam).
Proof.
  intros b1 b2 p n Lam lo hi HP HB Hlh Hn HN HF. apply NoDup_ListNoDup in HN.
  destruct (pairwise_mid _ b1 (p, n + 16) b2 HP) as (Hz & Hp12).
  rewrite Forall_forall in HF.
  split.
  - assert (HL : YO0f.pairwise YO0f.ranges_disjoint ((p, n + 16) :: map shift16 Lam)).
    { split.
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as ([a k] & <- & Hin).
        destruct (HF _ Hin) as (Hk & Hy). cbn [fst snd] in Hk, Hy.
        destruct (Hz _ Hy) as [Hd|Hd]; unfold YO0f.ranges_disjoint, shift16 in *; cbn [fst snd] in *; lia.
      - clear HP HB Hz. induction Lam as [|[a k] t IH]; cbn [map]; [exact I|].
        cbn [map fst] in HN. apply NoDup_cons_iff in HN. destruct HN as (Hna & HN).
        split.
        + intros y Hy. apply in_map_iff in Hy. destruct Hy as ([a' k'] & <- & Hin).
          destruct (HF (a, k) (or_introl eq_refl)) as (_ & H1). destruct (HF (a', k') (or_intror Hin)) as (_ & H2).
          cbn [fst snd] in H1, H2.
          assert (Ha : a <> a') by (intros ->; apply Hna; apply in_map_iff; exists (a', k'); split; [reflexivity | exact Hin]).
          destruct (pairwise_In _ _ _ _ Hp12 H1 H2 ltac:(intros E; injection E; lia)) as [Hd|Hd];
            unfold YO0f.ranges_disjoint, shift16 in *; cbn [fst snd] in *; lia.
        + apply IH; [exact HN | intros x Hx; apply HF; right; exact Hx]. }
    pose proof (disj_sum (length ((p, n + 16) :: map shift16 Lam)) _ lo hi (Nat.le_refl _) HL) as HS.
    cbn [lsz fst snd] in HS. rewrite lsz_shift in HS.
    assert (HS' : n + 16 + (Ledger.lsum Lam + 16 * Z.of_nat (length Lam)) <= hi - lo).
    { apply HS; [|exact Hlh]. intros x [<-|Hx].
      - pose proof (HB (p, n + 16) ltac:(apply in_or_app; right; left; reflexivity)). cbn [fst snd] in *. lia.
      - apply in_map_iff in Hx. destruct Hx as ([a k] & <- & Hin). destruct (HF _ Hin) as (Hk & Hy).
        cbn [fst snd] in Hk, Hy.
        assert (Hy' : In (a - 16, k + 16) (b1 ++ (p, n + 16) :: b2)).
        { apply in_app_or in Hy. apply in_or_app. destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy]. }
        pose proof (HB _ Hy'). unfold shift16. cbn [fst snd] in *. lia. }
    lia.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as ([a k] & Ea & Hin). cbn [fst] in Ea. subst a.
    destruct (HF _ Hin) as (Hk & Hy). cbn [fst snd] in Hk, Hy.
    destruct (Hz _ Hy) as [Hd|Hd]; unfold YO0f.ranges_disjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.
