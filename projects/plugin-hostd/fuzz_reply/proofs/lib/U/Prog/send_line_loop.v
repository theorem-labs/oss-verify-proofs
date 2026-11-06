From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c __errno_location_c.
Import ListNotations.
Open Scope Z_scope.

(* send_line of the UBSAN build (0x13328, 112-byte frame saving ra, s0..s11). The loop head is 0x1339c, with
   s0 = len, s1 = line, s5 = 0x21368 (g_client - 700), s6 = 0x318a0 (g_thread_up), s7 = sent, s8 = (line <> 0),
   s9 = 3, s10 = 4. The UBSAN checks (pointer overflow of line + sent and of out + nout, null pointer, errno
   alignment) branch to the trap at 0x134b4; each is shown not taken. *)

Lemma sl_wr_at_app : forall segs m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros segs m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hn & H). split; (split; [lia| split; [lia|]]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hn & Ha') (Hb & Hm & Hb')]. split; [lia| split; [lia|]].
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply Ha'. lia.
    + replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hb'. lia.
Qed.

Lemma sl_cells_app_l : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hw. apply sl_wr_at_app in Hw; [|lia|lia]. destruct Hw as [H1 H2].
  exact (conj (conj (conj W1 B1) H1) (conj (conj W2 B2) H2)).
Qed.

Lemma sl_cells_app_r : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] H1] [[W2 B2] H2].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite cells_bytes_length by exact W1. split; assumption.
  - rewrite cells_size_app, Nat2Z.inj_add. apply sl_wr_at_app; [lia|lia|]. split; assumption.
Qed.

Lemma sl_cb_split : forall segs m A (n1 n2 : nat) bs,
  rw_cells segs m A [CB (n1 + n2) bs] -> rw_cells segs m A [CB n1 (firstn n1 bs); CB n2 (skipn n1 bs)].
Proof.
  intros segs m A n1 n2 bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite app_nil_r, firstn_skipn. exact Hb.
  - cbn [cells_size csize] in *. replace (Z.of_nat (n1 + (n2 + 0))) with (Z.of_nat (n1 + n2 + 0)) by lia. exact Hw.
Qed.

Lemma sl_cb_merge : forall segs m A (n1 n2 : nat) bs1 bs2,
  rw_cells segs m A [CB n1 bs1; CB n2 bs2] -> rw_cells segs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros segs m A n1 n2 bs1 bs2 [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [H1 [H2 _]].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_app. split; [lia|exact I].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb |- *. exact Hb.
  - cbn [cells_size csize] in *. replace (Z.of_nat (n1 + n2 + 0)) with (Z.of_nat (n1 + (n2 + 0))) by lia. exact Hw.
Qed.

Lemma sl_cb_nil : forall segs m A, 0 <= A <= 2^64 -> rw_cells segs m A [CB 0 []].
Proof.
  intros segs m A HA. split; [split|].
  - cbn. split; [reflexivity|exact I].
  - cbn. apply bytes_at_nil. exact HA.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma sl_firstn_add : forall (bs : list byte) (k c : nat), firstn k bs ++ firstn c (skipn k bs) = firstn (k + c) bs.
Proof.
  intros bs k. revert bs. induction k as [|k IH]; intros bs c.
  - reflexivity.
  - destruct bs as [|b bs]; cbn.
    + destruct c; reflexivity.
    + f_equal. apply IH.
Qed.

Lemma sl_bytes_slice : forall segs m A bs (k n : nat), bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Ltac sl_fold_sx :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.

(* The values of sltu / sltiu 1 (snez, seqz) from the bounds in the context. *)
Ltac sl_cmp :=
  repeat match goal with
  | |- context [v_sltu ?a ?b] =>
      first
        [ replace (v_sltu a b) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite ?unsigned_lit by lia; fold_lit_ux;
                rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity)
        | replace (v_sltu a b) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite ?unsigned_lit by lia; fold_lit_ux;
                rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) ]
  | |- context [v_sltiu ?a 1] =>
      first
        [ replace (v_sltiu a 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite ?unsigned_lit by lia; change (bv_wrap 64 1) with 1; fold_lit_ux;
                rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity)
        | replace (v_sltiu a 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite ?unsigned_lit by lia; change (bv_wrap 64 1) with 1; fold_lit_ux;
                rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) ]
  end.

(* errno & 3 = 0 from the alignment of errno. *)
Ltac sl_land3 :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) with 0
        by (rewrite unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones by lia;
            change (2 ^ 2) with 4; lia)
  end.

Ltac if_f :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Ltac if_t :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Lemma sl_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) lo jb
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    m1,
  lo + 112 <= bv_unsigned sp ->
  stk rsegs m1 lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m1 (bv_unsigned sp + -112)
    [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word,
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom rsegs) /\ stk rsegs m1 lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x134c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo jb
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1
    HLO ST FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (stk_release rsegs m1 lo _ _ ST FR ltac:(lia)) as STR.
  change (cells_size _) with 112%nat in STR.
  replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in STR by lia.
  do 15 step.
  apply evt_done. do 15 eexists. split; [reflexivity|exact STR].
Qed.

Section Loop.
Set Default Proof Using "All".
Variables (sp gp tp wline wlen mx cap out : word) (F : bvmap 5 word) (fc : bv 32) (B : list byte).
Hypothesis MC : memcpy_contract.
Hypothesis EL : __errno_location_contract.
Hypothesis HLB : Z.of_nat (length B) = bv_unsigned wlen.
Hypothesis HRE : 203000 <= bv_unsigned tp + -164.
Hypothesis HEM : (bv_unsigned tp + -164) mod 4 = 0.
Hypothesis HL0 : 0 < bv_unsigned wline.
Hypothesis HOP : 0 < bv_unsigned cap -> 0 < bv_unsigned out.
Hypothesis HLG : bv_unsigned wline + bv_unsigned wlen <= 202912 \/ 203000 <= bv_unsigned wline.
Hypothesis HLE : bv_unsigned wline + bv_unsigned wlen <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= bv_unsigned wline.

Local Abbreviation HEAD x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 k m1 :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 wlen wline x10 x11 x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 136040) (Z_to_bv 64 202912) (Z_to_bv 64 k) (Z_to_bv 64 1) (Z_to_bv 64 3)
           (Z_to_bv 64 4) x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x1339c) fc None m1 (seg_rom rsegs)).

Definition sl_inv (dd e k : Z) (ev nk : word) (r : Z) (junk : list byte) (m1 : word -> option byte) : Prop :=
  0 <= k < bv_unsigned wlen /\ (dd = 0 \/ dd = 1) /\ (e = 0 \/ e = 1) /\ 0 <= r /\
  (dd = 0 -> bv_unsigned nk + (bv_unsigned wlen - k) < 2^64) /\
  Z.min (bv_unsigned wlen - k) (bv_unsigned cap - bv_unsigned nk) <= r /\
  mem_inv rsegs m1 /\ bytes_at rsegs m1 (bv_unsigned wline) B /\
  rw_cells rsegs m1 136740 [C4 (Z_to_bv 64 3)] /\
  rw_cells rsegs m1 202916 [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m1 202924 [C1 (Z_to_bv 8 dd)] /\
  rw_cells rsegs m1 202928 [C1 (Z_to_bv 8 e)] /\
  rw_cells rsegs m1 202968 [C8 mx; C8 nk; C8 cap; C8 out] /\
  rw_cells rsegs m1 (bv_unsigned tp + -164) [C4 ev] /\
  (dd = 0 ->
     bv_unsigned wlen < 2^63 /\
     ((bv_unsigned out + bv_unsigned nk + r <= 202912 \/ 203000 <= bv_unsigned out + bv_unsigned nk - k) /\
      (bv_unsigned out + bv_unsigned nk + r <= 136740 \/ 136744 <= bv_unsigned out + bv_unsigned nk - k)) /\
     (bv_unsigned out + bv_unsigned nk + r <= bv_unsigned tp + -164 \/
      bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nk - k) /\
     (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nk - k \/
      bv_unsigned out + bv_unsigned nk + r <= bv_unsigned wline) /\
     rw_cells rsegs m1 (bv_unsigned out + bv_unsigned nk - k)
       [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat r) junk]).

Definition sl_wit (live : bool) (P T : Z) : list (Z * Z) :=
  [(bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (202916, 202917); (202928, 202929); (202976, 202984)]
  ++ (if live then [(P, P + T)] else []).

Definition sl_more (dd e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte) (ms : machine_state) : Prop :=
  exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 : word) k' nk' r' junk' m2,
    ms = HEAD x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 k' m2 /\
    sl_inv dd 0 k' (if e =? 1 then Z_to_bv 64 4 else ev) nk' r' junk' m2 /\
    munch (sl_wit (dd =? 0) (bv_unsigned out + bv_unsigned nk - k) (k + r)) m1 m2 /\ wmono rsegs m1 m2 /\
    2 * (bv_unsigned wlen - k') < 2 * (bv_unsigned wlen - k) + e /\
    bv_unsigned nk' - k' = bv_unsigned nk - k /\ k' + r' = k + r /\ (dd = 1 -> nk' = nk) /\
    (exists t, k' = k + t * bv_unsigned mx).

Definition sl_done (dd e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte) (ms : machine_state) : Prop :=
  exists (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
          : word) m2,
    ms = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x134c0) fc None m2 (seg_rom rsegs) /\
    munch (sl_wit (dd =? 0) (bv_unsigned out + bv_unsigned nk - k) (k + r)) m1 m2 /\ wmono rsegs m1 m2 /\
    mem_inv rsegs m2 /\ bytes_at rsegs m2 (bv_unsigned wline) B /\
    rw_cells rsegs m2 202916 [C1 (Z_to_bv 8 dd)] /\
    rw_cells rsegs m2 202924 [C1 (Z_to_bv 8 dd)] /\
    rw_cells rsegs m2 202928 [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs m2 202968
      [C8 mx; C8 (if dd =? 0 then Z_to_bv 64 (bv_unsigned nk + (bv_unsigned wlen - k)) else nk); C8 cap; C8 out] /\
    rw_cells rsegs m2 (bv_unsigned tp + -164)
      [C4 (if dd =? 0 then (if e =? 1 then Z_to_bv 64 4 else ev) else Z_to_bv 64 32)] /\
    (dd = 0 -> bv_unsigned wlen <= k + r /\ exists junk', rw_cells rsegs m2 (bv_unsigned out + bv_unsigned nk - k)
       [CB (Z.to_nat (bv_unsigned wlen)) (firstn (Z.to_nat (bv_unsigned wlen)) B);
        CB (Z.to_nat (k + r - bv_unsigned wlen)) junk']).

Definition sl_grow (dd e k : Z) (nk : word) (m1 : word -> option byte) (ms : machine_state) : Prop :=
  exists (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) c,
    ms = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 wlen wline
                 out (Z_to_bv 64 (2 * (bv_unsigned nk + c))) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (k + bv_unsigned wline)) (Z_to_bv 64 c) (Z_to_bv 64 (2 * (bv_unsigned nk + c)))
                 (Z_to_bv 64 136040) (Z_to_bv 64 202912) (Z_to_bv 64 k) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 4)
                 nk x28 x29 x30 x31)
            F (Z_to_bv 64 0x13450) fc None m1 (seg_rom rsegs) /\
    e = 0 /\ dd = 0 /\ 1 <= c <= bv_unsigned wlen - k /\ bv_unsigned cap < bv_unsigned nk + c /\
    c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k else Z.min (bv_unsigned wlen - k) (bv_unsigned mx)).

Definition sl_post (dd e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte) : machine_state -> Prop :=
  fun ms => sl_more dd e k ev nk r m1 ms \/ sl_done dd e k ev nk r m1 ms \/ sl_grow dd e k nk m1 ms.

Lemma sl_tail : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) k ev nk r junk m1 c,
  0 < bv_unsigned out ->
  sl_inv 0 0 k ev nk r junk m1 -> 1 <= c <= bv_unsigned wlen - k -> c <= r ->
  c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k else Z.min (bv_unsigned wlen - k) (bv_unsigned mx)) ->
  evt rsegs (sl_post 0 0 k ev nk r m1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 wlen wline out x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (k + bv_unsigned wline)) (Z_to_bv 64 c) x20 (Z_to_bv 64 136040) (Z_to_bv 64 202912)
             (Z_to_bv 64 k) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 4) nk x28 x29 x30 x31)
        F (Z_to_bv 64 0x13464) fc None m1 (seg_rom rsegs)).
Proof using All.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 k ev nk r junk m1 c HOUT INV Hc Hcr Hcd.
  destruct INV as (Hk & _ & _ & Hr0 & Hnw & Hmin & MI & BL & CCL & CBR & CDD & CEI & COV & CER & HO).
  destruct (HO eq_refl) as (H63 & HP & HPE & HPL & CO). clear HO. specialize (Hnw eq_refl).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word out) as Rout. pose proof (zr_word cap) as Rcap.
  pose proof (zr_word mx) as Rmx. pose proof (zr_word wlen) as Rlen. pose proof (zr_word wline) as Rline.
  pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof (rw_cells_bound rsegs m1 _ _ CO) as BCO. cbn [cells_size csize] in BCO.
  pose proof (rw_cells_bound rsegs m1 _ _ CER) as BCE. cbn [cells_size csize] in BCE.
  pose proof (bytes_at_bound rsegs m1 _ _ BL) as BBL.
  assert (U1 : bv_unsigned (Z_to_bv 64 (c + bv_unsigned nk)) = c + bv_unsigned nk) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (bv_unsigned nk + bv_unsigned out)) = bv_unsigned out + bv_unsigned nk)
    by (rewrite unsigned_lit; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 (k + bv_unsigned wline)) = bv_unsigned wline + k)
    by (rewrite unsigned_lit; lia).
  step. step. if_f.
  step. sl_cmp. step. sl_cmp. step. step. if_f.
  step. step. step. step.
  change [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat r) junk]
    with ([CB (Z.to_nat k) (firstn (Z.to_nat k) B)] ++ [CB (Z.to_nat r) junk]) in CO.
  apply sl_cells_app_l in CO. destruct CO as [CO1 CO2]. cbn [cells_size csize] in CO2.
  replace (bv_unsigned out + bv_unsigned nk - k + Z.of_nat (Z.to_nat k + 0))
    with (bv_unsigned out + bv_unsigned nk) in CO2 by lia.
  replace (Z.to_nat r) with (Z.to_nat c + Z.to_nat (r - c))%nat in CO2 by lia.
  apply sl_cb_split in CO2.
  change [CB (Z.to_nat c) (firstn (Z.to_nat c) junk); CB (Z.to_nat (r - c)) (skipn (Z.to_nat c) junk)]
    with ([CB (Z.to_nat c) (firstn (Z.to_nat c) junk)] ++ [CB (Z.to_nat (r - c)) (skipn (Z.to_nat c) junk)]) in CO2.
  apply sl_cells_app_l in CO2. destruct CO2 as [CD CR]. cbn [cells_size csize] in CR.
  replace (bv_unsigned out + bv_unsigned nk + Z.of_nat (Z.to_nat c + 0))
    with (bv_unsigned out + bv_unsigned nk + c) in CR by lia.
  pose proof (sl_bytes_slice rsegs m1 _ B (Z.to_nat k) (Z.to_nat c) BL ltac:(lia)) as BS.
  rewrite Z2Nat.id in BS by lia.
  eapply evt_cut.
  { unfold memcpy_contract in MC.
    eapply (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
               (firstn (Z.to_nat c) (skipn (Z.to_nat k) B)) (firstn (Z.to_nat c) junk)).
    - rewrite U4. exact BS.
    - rewrite U3, length_firstn, length_skipn. lia.
    - rewrite U2, U3. exact CD.
    - rewrite U2, U3, U4. lia.
    - exact MI. }
  intros ms' POST. unfold memcpy_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                    & E & MUc & WMc & MI2 & CD2 & BS2).
  subst ms'. clear BS2 CD MI BS.
  replace (ret_pc (Z_to_bv 64 78988)) with (Z_to_bv 64 78988) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  rewrite U2, U3 in MUc, CD2.
  transport_after_call rsegs m1 m2 MUc WMc.
  assert (MU : munch
    [(bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (202916, 202917); (202928, 202929); (202976, 202984);
     (bv_unsigned out + bv_unsigned nk - k, bv_unsigned out + bv_unsigned nk - k + (k + r))] m1 m2).
  { eapply munch_weaken; [|exact MUc]. unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
  clear MUc. rename WMc into WM.
  assert (CO3 : rw_cells rsegs m2 (bv_unsigned out + bv_unsigned nk - k)
      [CB (Z.to_nat (c + k)) (firstn (Z.to_nat (c + k)) B); CB (Z.to_nat (r - c)) (skipn (Z.to_nat c) junk)]).
  { change [CB (Z.to_nat (c + k)) (firstn (Z.to_nat (c + k)) B); CB (Z.to_nat (r - c)) (skipn (Z.to_nat c) junk)]
      with ([CB (Z.to_nat (c + k)) (firstn (Z.to_nat (c + k)) B)] ++ [CB (Z.to_nat (r - c)) (skipn (Z.to_nat c) junk)]).
    apply sl_cells_app_r.
    - replace (Z.to_nat (c + k)) with (Z.to_nat k + Z.to_nat c)%nat by lia.
      rewrite <- sl_firstn_add. apply sl_cb_merge.
      change [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat c) (firstn (Z.to_nat c) (skipn (Z.to_nat k) B))]
        with ([CB (Z.to_nat k) (firstn (Z.to_nat k) B)] ++ [CB (Z.to_nat c) (firstn (Z.to_nat c) (skipn (Z.to_nat k) B))]).
      apply sl_cells_app_r; [exact CO1|]. cbn [cells_size csize].
      replace (bv_unsigned out + bv_unsigned nk - k + Z.of_nat (Z.to_nat k + 0))
        with (bv_unsigned out + bv_unsigned nk) by lia.
      exact CD2.
    - cbn [cells_size csize].
      replace (bv_unsigned out + bv_unsigned nk - k + Z.of_nat (Z.to_nat (c + k) + 0))
        with (bv_unsigned out + bv_unsigned nk + c) by lia.
      exact CR. }
  clear CO1 CD2 CR.
  step.
  try replace (Z_to_bv 64 (bv_unsigned nk + c)) with (Z_to_bv 64 (c + bv_unsigned nk)) by (f_equal; lia).
  step.
  assert (S1 : bv_signed (Z_to_bv 64 c) = c)
    by (rewrite zb_signed, U3; destruct (Z.ltb_spec c (2^63)); lia).
  step. if_false.
  step. if_false.
  step. step.
  assert (U5 : bv_unsigned (Z_to_bv 64 (c + k)) = c + k) by (apply unsigned_lit; lia).
  step.
  destruct (Z_lt_le_dec (c + k) (bv_unsigned wlen)) as [L|L].
  + if_t.
    apply evt_done. left.
    do 20 eexists. exists (c + k), (Z_to_bv 64 (c + bv_unsigned nk)), (r - c), (skipn (Z.to_nat c) junk). eexists.
    split; [reflexivity|].
    split.
    { unfold sl_inv. rewrite U1.
      replace (bv_unsigned out + (c + bv_unsigned nk) - (c + k)) with (bv_unsigned out + bv_unsigned nk - k) by lia.
      change (if 0 =? 1 then Z_to_bv 64 4 else ev) with ev.
      split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. split; [lia|].
      split; [intros _; lia|].
      split; [lia|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      intros _. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact CO3. }
    split; [exact MU|]. split; [exact WM|]. split; [lia|]. split; [rewrite U1; lia|]. split; [lia|].
    split; [intros D; discriminate|].
    exists 1. revert Hcd. destruct (Z.eqb_spec (bv_unsigned mx) 0); intros Hcd; lia.
  + if_f. step.
    apply evt_done. right; left.
    do 28 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    split.
    { change (if 0 =? 0 then Z_to_bv 64 (bv_unsigned nk + (bv_unsigned wlen - k)) else nk)
        with (Z_to_bv 64 (bv_unsigned nk + (bv_unsigned wlen - k))).
      replace (bv_unsigned nk + (bv_unsigned wlen - k)) with (c + bv_unsigned nk) by lia. assumption. }
    split.
    { change (if 0 =? 0 then (if 0 =? 1 then Z_to_bv 64 4 else ev) else Z_to_bv 64 32) with ev. assumption. }
    intros _. split; [lia|]. exists (skipn (Z.to_nat c) junk).
    replace (k + r - bv_unsigned wlen) with (r - c) by lia.
    replace (bv_unsigned wlen) with (c + k) by lia.
    exact CO3.
Qed.

Lemma sl_copy : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31 : word)
    dd k ev nk r junk m1 c,
  dd = 0 -> sl_inv dd 0 k ev nk r junk m1 -> 1 <= c <= bv_unsigned wlen - k ->
  c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k else Z.min (bv_unsigned wlen - k) (bv_unsigned mx)) ->
  evt rsegs (sl_post dd 0 k ev nk r m1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 wlen wline x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (k + bv_unsigned wline)) (Z_to_bv 64 c) x20 (Z_to_bv 64 136040) (Z_to_bv 64 202912)
             (Z_to_bv 64 k) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 4) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13434) fc None m1 (seg_rom rsegs)).
Proof using All.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31 dd k ev nk r junk m1 c -> INV Hc Hcd.
  pose proof INV as INV0.
  destruct INV as (Hk & _ & _ & Hr0 & Hnw & Hmin & MI & BL & CCL & CBR & CDD & CEI & COV & CER & HO).
  destruct (HO eq_refl) as (H63 & HP & HPE & HPL & CO). clear HO. specialize (Hnw eq_refl).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word out) as Rout. pose proof (zr_word cap) as Rcap.
  pose proof (zr_word mx) as Rmx. pose proof (zr_word wlen) as Rlen. pose proof (zr_word wline) as Rline.
  pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof (rw_cells_bound rsegs m1 _ _ CO) as BCO. cbn [cells_size csize] in BCO.
  pose proof (rw_cells_bound rsegs m1 _ _ CER) as BCE. cbn [cells_size csize] in BCE.
  pose proof (bytes_at_bound rsegs m1 _ _ BL) as BBL.
  assert (U1 : bv_unsigned (Z_to_bv 64 (c + bv_unsigned nk)) = c + bv_unsigned nk) by (apply unsigned_lit; lia).
  step. step. step. step.
  try replace (Z_to_bv 64 (bv_unsigned nk + c)) with (Z_to_bv 64 (c + bv_unsigned nk)) by (f_equal; lia).
  step.
  destruct (Z_lt_le_dec (bv_unsigned cap) (c + bv_unsigned nk)) as [G|G].
  - if_f.
    step. step.
    rewrite ?U1, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    replace ((c + bv_unsigned nk) * 2) with (2 * (bv_unsigned nk + c)) by lia.
    apply evt_done. right; right.
    exists x1, x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, c.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hcd.
  - if_t.
    eapply sl_tail; [apply HOP; lia | exact INV0 | lia | lia | exact Hcd].
Qed.

Lemma sl_w4 : forall live P T,
  sub_fp [(bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (202916, 202917); (202928, 202929); (202976, 202984)]
    (sl_wit live P T).
Proof using All.
  intros live P T. unfold sub_fp, sl_wit. intros x Hx. destruct live; cbn [app outside] in *; tauto.
Qed.

Lemma sl_out_transport : forall dd k (nk : word) r junk m1 m2,
  (dd = 0 ->
     bv_unsigned wlen < 2^63 /\
     ((bv_unsigned out + bv_unsigned nk + r <= 202912 \/ 203000 <= bv_unsigned out + bv_unsigned nk - k) /\
      (bv_unsigned out + bv_unsigned nk + r <= 136740 \/ 136744 <= bv_unsigned out + bv_unsigned nk - k)) /\
     (bv_unsigned out + bv_unsigned nk + r <= bv_unsigned tp + -164 \/
      bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nk - k) /\
     (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nk - k \/
      bv_unsigned out + bv_unsigned nk + r <= bv_unsigned wline) /\
     rw_cells rsegs m1 (bv_unsigned out + bv_unsigned nk - k)
       [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat r) junk]) ->
  0 <= k -> 0 <= r ->
  munch [(bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (202916, 202917); (202928, 202929); (202976, 202984)]
    m1 m2 ->
  wmono rsegs m1 m2 ->
  (dd = 0 ->
     bv_unsigned wlen < 2^63 /\
     ((bv_unsigned out + bv_unsigned nk + r <= 202912 \/ 203000 <= bv_unsigned out + bv_unsigned nk - k) /\
      (bv_unsigned out + bv_unsigned nk + r <= 136740 \/ 136744 <= bv_unsigned out + bv_unsigned nk - k)) /\
     (bv_unsigned out + bv_unsigned nk + r <= bv_unsigned tp + -164 \/
      bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nk - k) /\
     (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nk - k \/
      bv_unsigned out + bv_unsigned nk + r <= bv_unsigned wline) /\
     rw_cells rsegs m2 (bv_unsigned out + bv_unsigned nk - k)
       [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat r) junk]).
Proof using All.
  intros dd k nk r junk m1 m2 H Hk Hr MU WM D. destruct (H D) as (H1 & H2 & H3 & H4 & H5).
  pose proof (rw_cells_bound rsegs m1 _ _ H5) as BC. cbn [cells_size csize] in BC.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  eapply rw_cells_transport; [exact H5|exact MU|exact WM|].
  cbn [disjoint_from cells_size csize]. lia.
Qed.

Lemma sl_iter : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 : word)
    dd e k ev nk r junk m1,
  sl_inv dd e k ev nk r junk m1 ->
  evt rsegs (sl_post dd e k ev nk r m1)
    (HEAD x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 k m1).
Proof using All.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 dd e k ev nk r junk m1 INV.
  pose proof INV as INV0.
  destruct INV as (Hk & Hdd & He & Hr0 & Hnw & Hmin & MI & BL & CCL & CBR & CDD & CEI & COV & CER & HO).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word out) as Rout. pose proof (zr_word cap) as Rcap.
  pose proof (zr_word mx) as Rmx. pose proof (zr_word wlen) as Rlen. pose proof (zr_word wline) as Rline.
  pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof (rw_cells_bound rsegs m1 _ _ CER) as BCE. cbn [cells_size csize] in BCE.
  pose proof (bytes_at_bound rsegs m1 _ _ BL) as BBL.
  assert (U0 : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  pose proof (munch_refl
    [(bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (202916, 202917); (202928, 202929); (202976, 202984)] m1) as MU.
  pose proof (wmono_refl rsegs m1) as WM.
  step. rewrite ?U0.
  step. if_f.
  step. sl_cmp.
  step.
  step. if_f.
  step. sl_fold_sx.
  step. if_f.
  step.
  destruct He as [-> | ->].
  - step. if_t.
    step.
    destruct Hdd as [-> | ->].
    + step. if_t.
      clear MU WM.
      step. step. rewrite ?U0.
      step.
      assert (U6 : bv_unsigned (Z_to_bv 64 (bv_unsigned wlen - k)) = bv_unsigned wlen - k) by (apply unsigned_lit; lia).
      step.
      destruct (Z_lt_le_dec (bv_unsigned wlen - k) (bv_unsigned mx)) as [Lm|Lm].
      * if_t. step. if_f. step.
        eapply sl_copy; [reflexivity|exact INV0|lia|].
        destruct (Z.eqb_spec (bv_unsigned mx) 0); lia.
      * if_f. step. step.
        destruct (Z.eq_dec (bv_unsigned mx) 0) as [M0|M0].
        -- if_t.
           eapply sl_copy; [reflexivity|exact INV0|lia|].
           rewrite M0. reflexivity.
        -- if_f. step.
           rewrite <- (Z_to_bv_lit_self mx).
           eapply sl_copy; [reflexivity|exact INV0|lia|].
           destruct (Z.eqb_spec (bv_unsigned mx) 0); lia.
    + step. if_f.
      step.
      eapply evt_cut; [apply EL|]. intros ms' E. cbv beta in E. subst ms'. unfold ERRNO_TP_OFF.
      replace (ret_pc (Z_to_bv 64 78824)) with (Z_to_bv 64 78824) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      step. if_f.
      step. sl_land3.
      step. if_f.
      step. step.
      step.
      step. if_f.
      step. if_f.
      step. sl_fold_sx.
      step. if_t.
      step. step.
      change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))). mem_after_store.
      apply evt_done. right; left.
      do 28 eexists. eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [apply sl_w4|exact MU]|]. split; [exact WM|].
      split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [change (if 1 =? 0 then Z_to_bv 64 (bv_unsigned nk + (bv_unsigned wlen - k)) else nk) with nk; assumption|].
      split; [change (if 1 =? 0 then (if 0 =? 1 then Z_to_bv 64 4 else ev) else Z_to_bv 64 32) with (Z_to_bv 64 32);
              assumption|].
      intros D; discriminate.
  - step. if_f.
    step.
    change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))). mem_after_store.
    step.
    eapply evt_cut; [apply EL|]. intros ms' E. cbv beta in E. subst ms'. unfold ERRNO_TP_OFF.
    replace (ret_pc (Z_to_bv 64 78792)) with (Z_to_bv 64 78792) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    step. if_f.
    step. sl_land3.
    step. if_f.
    step. step.
    step.
    step. if_f.
    step. if_f.
    step. sl_fold_sx.
    step. if_f.
    step. if_t.
    apply evt_done. left.
    do 20 eexists. exists k, nk, r, junk. eexists.
    split; [reflexivity|].
    split.
    { change (if 1 =? 1 then Z_to_bv 64 4 else ev) with (Z_to_bv 64 4).
      unfold sl_inv.
      split; [lia|]. split; [exact Hdd|]. split; [left; reflexivity|]. split; [lia|]. split; [exact Hnw|].
      split; [lia|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      eapply sl_out_transport; [exact HO|lia|lia|exact MU|exact WM]. }
    split; [eapply munch_weaken; [apply sl_w4|exact MU]|]. split; [exact WM|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|]. exists 0. lia.
Qed.

Variables (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (jb : list byte).

Definition sl_frame (m : word -> option byte) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -112)
    [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -112).

Definition sl_fin (dd e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte) (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2,
    ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3' t4' t5' t6')
            F (ret_pc ra) fc None m2 (seg_rom rsegs) /\
    munch (sl_wit (dd =? 0) (bv_unsigned out + bv_unsigned nk - k) (k + r)) m1 m2 /\ wmono rsegs m1 m2 /\
    stk rsegs m2 lo (bv_unsigned sp) /\
    mem_inv rsegs m2 /\ bytes_at rsegs m2 (bv_unsigned wline) B /\
    rw_cells rsegs m2 202916 [C1 (Z_to_bv 8 dd)] /\
    rw_cells rsegs m2 202924 [C1 (Z_to_bv 8 dd)] /\
    rw_cells rsegs m2 202928 [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs m2 202968
      [C8 mx; C8 (if dd =? 0 then Z_to_bv 64 (bv_unsigned nk + (bv_unsigned wlen - k)) else nk); C8 cap; C8 out] /\
    rw_cells rsegs m2 (bv_unsigned tp + -164)
      [C4 (if dd =? 0 then (if e =? 1 then Z_to_bv 64 4 else ev) else Z_to_bv 64 32)] /\
    (dd = 0 -> bv_unsigned wlen <= k + r /\ exists junk', rw_cells rsegs m2 (bv_unsigned out + bv_unsigned nk - k)
       [CB (Z.to_nat (bv_unsigned wlen)) (firstn (Z.to_nat (bv_unsigned wlen)) B);
        CB (Z.to_nat (k + r - bv_unsigned wlen)) junk']).

Definition sl_call (dd e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte) (ms : machine_state) : Prop :=
  exists (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) k' ev' nk' r' junk' m2 c,
    ms = MS (mkR (Z_to_bv 64 0x13454) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 wlen wline
                 out (Z_to_bv 64 (2 * (bv_unsigned nk' + c))) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (k' + bv_unsigned wline)) (Z_to_bv 64 c) (Z_to_bv 64 (2 * (bv_unsigned nk' + c)))
                 (Z_to_bv 64 136040) (Z_to_bv 64 202912) (Z_to_bv 64 k') (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 4)
                 nk' x28 x29 x30 x31)
            F (Z_to_bv 64 0x178f8) fc None m2 (seg_rom rsegs) /\
    sl_inv 0 0 k' ev' nk' r' junk' m2 /\ sl_frame m2 /\
    munch (sl_wit (dd =? 0) (bv_unsigned out + bv_unsigned nk - k) (k + r)) m1 m2 /\ wmono rsegs m1 m2 /\
    dd = 0 /\ k <= k' /\ bv_unsigned nk' - k' = bv_unsigned nk - k /\ k' + r' = k + r /\
    1 <= c <= bv_unsigned wlen - k' /\ bv_unsigned cap < bv_unsigned nk' + c /\
    c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k' else Z.min (bv_unsigned wlen - k') (bv_unsigned mx)) /\
    (exists t, k' = k + t * bv_unsigned mx).

Lemma sl_frame_transport : forall live P T m1 m2,
  sl_frame m1 -> munch (sl_wit live P T) m1 m2 -> wmono rsegs m1 m2 ->
  bv_unsigned tp + -164 + 4 <= lo -> 203000 <= lo -> lo + 112 <= bv_unsigned sp ->
  (live = true -> 0 <= T /\ P + T <= lo) -> sl_frame m2.
Proof using All.
  intros live P T m1 m2 [FR ST] MU WM H1 H2 H3 HL.
  pose proof (rw_cells_bound rsegs m1 _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  split.
  - eapply rw_cells_transport; [exact FR|exact MU|exact WM|].
    unfold sl_wit. destruct live; cbn [app disjoint_from cells_size csize Nat.add];
      [specialize (HL eq_refl)|]; lia.
  - eapply stk_transport_disjoint; [exact ST|exact MU|exact WM|].
    unfold sl_wit. destruct live; cbn [app disjoint_from]; [specialize (HL eq_refl)|]; lia.
Qed.

Lemma sl_run : forall (n : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 : word)
    dd e k ev nk r junk m1,
  (Z.to_nat (2 * (bv_unsigned wlen - k) + e) < n)%nat ->
  sl_inv dd e k ev nk r junk m1 -> sl_frame m1 ->
  bv_unsigned tp + -164 + 4 <= lo -> 203000 <= lo -> lo + 112 <= bv_unsigned sp ->
  (dd = 0 -> bv_unsigned out + bv_unsigned nk + r <= lo) ->
  evt rsegs (fun ms => sl_fin dd e k ev nk r m1 ms \/ sl_call dd e k ev nk r m1 ms)
    (HEAD x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 k m1).
Proof using All.
  induction n as [|n IH];
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x27 x28 x29 x30 x31 dd e k ev nk r junk m1 Hn INV
      FRM H1 H2 H3 HLO;
    [lia|].
  pose proof INV as INV'. destruct INV' as (Hk & Hdd & He & Hr0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word out) as Rout. pose proof (zr_word wlen) as Rlen.
  unfold inr64 in *.
  assert (HW : dd = 0 -> 0 <= k + r /\ bv_unsigned out + bv_unsigned nk - k + (k + r) <= lo).
  { intros D. destruct (HO D) as (_ & _ & _ & _ & CO). pose proof (rw_cells_bound rsegs m1 _ _ CO).
    specialize (HLO D). lia. }
  assert (HWb : (dd =? 0) = true -> 0 <= k + r /\ bv_unsigned out + bv_unsigned nk - k + (k + r) <= lo).
  { intros D. apply Z.eqb_eq in D. exact (HW D). }
  eapply evt_cut; [eapply sl_iter; exact INV|].
  intros ms [Hm | [Hd | Hg]].
  - destruct Hm as (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y27 & y28
                    & y29 & y30 & y31 & k' & nk' & r' & junk' & m2 & -> & INV2 & MU & WM & Hms & Hnk & Hkr & Hdd1
                    & [t1 Ht1]).
    pose proof (sl_frame_transport _ _ _ m1 m2 FRM MU WM H1 H2 H3 HWb) as FRM2.
    pose proof INV2 as INV2'. destruct INV2' as (Hk2 & _).
    eapply evt_mono.
    + eapply (IH y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y27 y28 y29 y30 y31 dd 0 k' _ nk' r' junk' m2);
        [lia | exact INV2 | exact FRM2 | lia | lia | lia | intros D; specialize (HLO D); lia].
    + intros ms' [Hf | Hc].
      * left. unfold sl_fin in Hf |- *.
        destruct Hf as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MU2
                        & WM2 & ST3 & MI3 & BL3 & C1 & C2 & C3 & C4 & C5 & C6).
        exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m3.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in MU2 by lia.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in C6 by lia.
        replace (k' + r') with (k + r) in MU2 by lia.
        replace (k' + r') with (k + r) in C6 by lia.
        split; [reflexivity|]. split; [eapply munch_trans; [exact MU|exact MU2]|].
        split; [eapply wmono_trans; [exact WM|exact WM2]|].
        split; [exact ST3|]. split; [exact MI3|]. split; [exact BL3|]. split; [exact C1|]. split; [exact C2|].
        split; [exact C3|].
        split.
        { destruct Hdd as [-> | ->].
          - replace (bv_unsigned nk + (bv_unsigned wlen - k)) with (bv_unsigned nk' + (bv_unsigned wlen - k')) by lia.
            exact C4.
          - rewrite <- (Hdd1 eq_refl). exact C4. }
        split; [exact C5|]. exact C6.
      * right. unfold sl_call in Hc |- *.
        destruct Hc as (z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & k2 & ev2 & nk2 & r2
                        & junk2 & m3 & c & -> & INV3 & FRM3 & MU2 & WM2 & D0 & Hk3 & Hnk3 & Hkr3 & Hc & Hcap & Hcd
                        & [t2 Ht2]).
        exists z5, z6, z7, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, k2, ev2, nk2, r2, junk2, m3, c.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in MU2 by lia.
        replace (k' + r') with (k + r) in MU2 by lia.
        split; [reflexivity|]. split; [exact INV3|]. split; [exact FRM3|].
        split; [eapply munch_trans; [exact MU|exact MU2]|].
        split; [eapply wmono_trans; [exact WM|exact WM2]|].
        split; [exact D0|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [exact Hc|]. split; [exact Hcap|]. split; [exact Hcd|]. exists (t1 + t2). rewrite Ht2, Ht1. ring.
  - destruct Hd as (z1 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20
                    & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m2 & -> & MU & WM & MI2 & BL2
                    & C1 & C2 & C3 & C4 & C5 & C6).
    destruct (sl_frame_transport _ _ _ m1 m2 FRM MU WM H1 H2 H3 HWb) as [FR2 ST2].
    eapply evt_mono; [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo jb);
                      [exact H3 | exact ST2 | exact FR2] |].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
    left. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact STR|].
    split; [exact MI2|]. split; [exact BL2|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [exact C4|]. split; [exact C5|]. exact C6.
  - destruct Hg as (g1 & g5 & g6 & g7 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & c & -> & -> & D0
                    & Hc & Hcap & Hcd).
    subst dd.
    step.
    apply evt_done. right.
    exists g5, g6, g7, g12, g13, g14, g15, g16, g17, g28, g29, g30, g31, k, ev, nk, r, junk, m1, c.
    split; [reflexivity|]. split; [exact INV|]. split; [exact FRM|].
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Hc|]. split; [exact Hcap|]. split; [exact Hcd|]. exists 0. lia.
Qed.

Lemma sl_post_out : forall dd e k ev nk r junk m1 ms,
  sl_post dd e k ev nk r m1 ms -> sl_inv dd e k ev nk r junk m1 -> sl_frame m1 ->
  bv_unsigned tp + -164 + 4 <= lo -> 203000 <= lo -> lo + 112 <= bv_unsigned sp ->
  (dd = 0 -> bv_unsigned out + bv_unsigned nk + r <= lo) ->
  evt rsegs (fun ms' => sl_fin dd e k ev nk r m1 ms' \/ sl_call dd e k ev nk r m1 ms') ms.
Proof using All.
  intros dd e k ev nk r junk m1 ms POST INV FRM H1 H2 H3 HLO.
  pose proof INV as INV'. destruct INV' as (Hk & Hdd & He & Hr0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word out) as Rout. pose proof (zr_word wlen) as Rlen.
  unfold inr64 in *.
  assert (HW : dd = 0 -> 0 <= k + r /\ bv_unsigned out + bv_unsigned nk - k + (k + r) <= lo).
  { intros D. destruct (HO D) as (_ & _ & _ & _ & CO). pose proof (rw_cells_bound rsegs m1 _ _ CO).
    specialize (HLO D). lia. }
  assert (HWb : (dd =? 0) = true -> 0 <= k + r /\ bv_unsigned out + bv_unsigned nk - k + (k + r) <= lo).
  { intros D. apply Z.eqb_eq in D. exact (HW D). }
  destruct POST as [Hm | [Hd | Hg]].
  - destruct Hm as (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y27 & y28
                    & y29 & y30 & y31 & k' & nk' & r' & junk' & m2 & -> & INV2 & MU & WM & Hms & Hnk & Hkr & Hdd1
                    & [t1 Ht1]).
    pose proof (sl_frame_transport _ _ _ m1 m2 FRM MU WM H1 H2 H3 HWb) as FRM2.
    pose proof INV2 as INV2'. destruct INV2' as (Hk2 & _).
    eapply evt_mono.
    + eapply (sl_run (S (Z.to_nat (2 * (bv_unsigned wlen - k') + 0)))
               y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y27 y28 y29 y30 y31 dd 0 k' _ nk' r' junk' m2);
        [lia | exact INV2 | exact FRM2 | lia | lia | lia | intros D; specialize (HLO D); lia].
    + intros ms' [Hf | Hc].
      * left. unfold sl_fin in Hf |- *.
        destruct Hf as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MU2
                        & WM2 & ST3 & MI3 & BL3 & C1 & C2 & C3 & C4 & C5 & C6).
        exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m3.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in MU2 by lia.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in C6 by lia.
        replace (k' + r') with (k + r) in MU2 by lia.
        replace (k' + r') with (k + r) in C6 by lia.
        split; [reflexivity|]. split; [eapply munch_trans; [exact MU|exact MU2]|].
        split; [eapply wmono_trans; [exact WM|exact WM2]|].
        split; [exact ST3|]. split; [exact MI3|]. split; [exact BL3|]. split; [exact C1|]. split; [exact C2|].
        split; [exact C3|].
        split.
        { destruct Hdd as [-> | ->].
          - replace (bv_unsigned nk + (bv_unsigned wlen - k)) with (bv_unsigned nk' + (bv_unsigned wlen - k')) by lia.
            exact C4.
          - rewrite <- (Hdd1 eq_refl). exact C4. }
        split; [exact C5|]. exact C6.
      * right. unfold sl_call in Hc |- *.
        destruct Hc as (z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & k2 & ev2 & nk2 & r2
                        & junk2 & m3 & c & -> & INV3 & FRM3 & MU2 & WM2 & D0 & Hk3 & Hnk3 & Hkr3 & Hc & Hcap & Hcd
                        & [t2 Ht2]).
        exists z5, z6, z7, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, k2, ev2, nk2, r2, junk2, m3, c.
        replace (bv_unsigned out + bv_unsigned nk' - k') with (bv_unsigned out + bv_unsigned nk - k) in MU2 by lia.
        replace (k' + r') with (k + r) in MU2 by lia.
        split; [reflexivity|]. split; [exact INV3|]. split; [exact FRM3|].
        split; [eapply munch_trans; [exact MU|exact MU2]|].
        split; [eapply wmono_trans; [exact WM|exact WM2]|].
        split; [exact D0|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [exact Hc|]. split; [exact Hcap|]. split; [exact Hcd|]. exists (t1 + t2). rewrite Ht2, Ht1. ring.
  - destruct Hd as (z1 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20
                    & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m2 & -> & MU & WM & MI2 & BL2
                    & C1 & C2 & C3 & C4 & C5 & C6).
    destruct (sl_frame_transport _ _ _ m1 m2 FRM MU WM H1 H2 H3 HWb) as [FR2 ST2].
    eapply evt_mono; [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo jb);
                      [exact H3 | exact ST2 | exact FR2] |].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
    left. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact STR|].
    split; [exact MI2|]. split; [exact BL2|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [exact C4|]. split; [exact C5|]. exact C6.
  - destruct Hg as (g1 & g5 & g6 & g7 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & c & -> & -> & D0
                    & Hc & Hcap & Hcd).
    subst dd.
    step.
    apply evt_done. right.
    exists g5, g6, g7, g12, g13, g14, g15, g16, g17, g28, g29, g30, g31, k, ev, nk, r, junk, m1, c.
    split; [reflexivity|]. split; [exact INV|]. split; [exact FRM|].
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Hc|]. split; [exact Hcap|]. split; [exact Hcd|]. exists 0. lia.
Qed.

End Loop.
