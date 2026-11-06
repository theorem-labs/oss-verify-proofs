(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame: module paths, DgnLibBodyCheck (now in DgnLib) dropped from the imports, every pc by +0x168 (entry 0x13b84 -> 0x13cec), the header's image. *)
(* Walk of diginet_body_check (src/diginet_codec.c:47-64 at 835f336c) in fuzz_decode.plain,
   0x13cec..0x13df8, against diginet_body_check_contract.
   The frame of 144 bytes holds the message at sp - 136 (40 bytes), the cursor at sp - 96
   (25 bytes) and ra, s0..s6 at sp - 8 .. sp - 64. The cursor loop (0x13d4c..0x13d80) calls
   diginet_msg_next until it answers 0; each step moves the cursor forward
   (the libdiginet model msg_step_progress), so the loop ends. A sysex F0 13 xx 70 .. F7 that the loop finds
   starts the prefix F0 13 xx 70 (the libdiginet model refused_hit), and the prefix scan (0x13d84..0x13dc0)
   tests every index i with i + 3 < len. So the answer is -10 exactly when system_at bb, which is
   body_check bb (the libdiginet model body_check_spec).
   The contract allows body = 2^64 with an empty body; then a0 is NULL, diginet_cursor_init gets
   body 0 and length 0, and the first diginet_msg_next answers 0 (bc_main, second case).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  diginet_body_check_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * Cells and bytes *)

Lemma bc_wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma bc_rw_split : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] Hw] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply bc_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma bc_rw_cons : forall m A B c cs, rw_cells rsegs m A (c :: cs) -> B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs.
Proof.
  intros m A B c cs H E. apply (bc_rw_split m A B [c] cs H).
  cbn [cells_size]. rewrite Nat.add_0_r. exact E.
Qed.

(* The 80 bytes below the saved registers: 8 unused bytes, the message (40), the cursor (25) and
   the 7 bytes after it. *)
Lemma bc_frame_split : forall m A J rest A8 A48 A73 A80,
  rw_cells rsegs m A (CB 80 J :: rest) ->
  A8 = A + 8 -> A48 = A + 48 -> A73 = A + 73 -> A80 = A + 80 ->
  exists j0 jm jc j7, rw_cells rsegs m A [CB 8 j0] /\ rw_cells rsegs m A8 [CB 40 jm] /\
    rw_cells rsegs m A48 [CB 25 jc] /\ rw_cells rsegs m A73 [CB 7 j7] /\ rw_cells rsegs m A80 rest.
Proof.
  intros m A J rest A8 A48 A73 A80 H E8 E48 E73 E80.
  pose proof (rw_cells_split_CB rsegs m A [] 80 J rest [8; 40; 25; 7]%nat H eq_refl) as H1.
  cbn [app mk_CB_cells] in H1.
  destruct (bc_rw_cons m A A8 _ _ H1 ltac:(cbn; lia)) as [P0 H2].
  destruct (bc_rw_cons m A8 A48 _ _ H2 ltac:(cbn; lia)) as [P1 H3].
  destruct (bc_rw_cons m A48 A73 _ _ H3 ltac:(cbn; lia)) as [P2 H4].
  destruct (bc_rw_cons m A73 A80 _ _ H4 ltac:(cbn; lia)) as [P3 P4].
  do 4 eexists. exact (conj P0 (conj P1 (conj P2 (conj P3 P4)))).
Qed.

Lemma bc_forget40 : forall m A cs, rw_cells rsegs m A cs -> cells_size cs = 40%nat ->
  exists j, rw_cells rsegs m A [CB 40 j].
Proof.
  intros m A cs H E. destruct (rw_cells_forget rsegs m A cs H) as [j Hj]. rewrite E in Hj.
  exists j. exact Hj.
Qed.

Lemma bc_forget25 : forall m A cs, rw_cells rsegs m A cs -> cells_size cs = 25%nat ->
  exists j, rw_cells rsegs m A [CB 25 j].
Proof.
  intros m A cs H E. destruct (rw_cells_forget rsegs m A cs H) as [j Hj]. rewrite E in Hj.
  exists j. exact Hj.
Qed.

Lemma bc_msg_size : forall body mj r, cells_size (msg_cells body mj r) = 40%nat.
Proof.
  intros body mj r. unfold msg_cells. destruct (is_end r); [reflexivity|].
  destruct (writes_len (mr_kind r)); reflexivity.
Qed.

Lemma bc_firstn1 : forall (l : list byte) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros [|i] d Hi; cbn in Hi |- *; try lia; [reflexivity | apply IH; lia].
Qed.

(* A byte load from the body. *)
Lemma bc_rd : forall m a l (i : nat) a', bytes_at rsegs m a l -> (i < length l)%nat -> a' = a + Z.of_nat i ->
  ov_read_bytes rsegs m (wa a') 1 = Some [nth i l (b8 0)].
Proof.
  intros m a l i a' BL Hi ->.
  rewrite (bytes_at_ov_read rsegs m a l i 1 BL ltac:(lia)).
  rewrite (bc_firstn1 l i (b8 0) Hi). reflexivity.
Qed.

Lemma bc_zxb : forall l i, bv_unsigned (zxb (nth i l (b8 0))) = at8 l i.
Proof.
  intros l i. pose proof (bz_range (nth i l (b8 0))) as R. unfold bz in R.
  unfold zxb, at8, bz. apply unsigned_lit. lia.
Qed.

Lemma bc_zxb_b8 : forall s, 0 <= s < 2^8 -> bv_unsigned (zxb (b8 s)) = s.
Proof.
  intros s Hs. pose proof (bz_b8 s Hs) as E. unfold bz in E.
  unfold zxb. rewrite E. apply unsigned_lit. lia.
Qed.

(** * Tactics *)

(* Decide a branch whose condition is a closed term. *)
Ltac bc_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* Decide a branch to v from the facts in the context. *)
Ltac bc_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [ cbv iota
      | symmetry; unfold_cond; rewrite ?bc_zxb; rewrite ?bc_zxb_b8 by lia; fold_lit_ux;
        rewrite ?unsigned_lit by lia; solve_cond_rec ]
  end.

(* The message and the cursor as blocks of 40 and 25 bytes. *)
Ltac bc_forget_mc :=
  repeat match goal with
  | H : rw_cells _ _ _ (msg_cells _ _ _) |- _ =>
      let j := fresh "jm" in let H' := fresh "RM" in
      destruct (bc_forget40 _ _ _ H (bc_msg_size _ _ _)) as [j H']; clear H
  | H : rw_cells _ _ _ (cursor_cells _ _ _ _) |- _ =>
      let j := fresh "jc" in let H' := fresh "RC" in
      destruct (bc_forget25 _ _ _ H eq_refl) as [j H']; clear H
  end.

(** * The walk *)

Section Walk.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (body lo : Z) (bb : list byte).
Hypothesis CI : diginet_cursor_init_contract.
Hypothesis MN : diginet_msg_next_contract.
Hypothesis HB0 : 0 < body.
Hypothesis HBE : body + Z.of_nat (length bb) <= 2^64.
Hypothesis LO0 : 0 <= lo.
Hypothesis LO : lo + 144 <= bv_unsigned sp.
Hypothesis DJ : body + Z.of_nat (length bb) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= body.

Local Notation SPZ := (bv_unsigned sp).

(* The post of the contract. *)
Definition bcQ : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Lemma bc_ci_fix : forall m A len,
  rw_cells rsegs m A (cursor_cells body (if body =? 0 then 0 else len) 0 0) ->
  rw_cells rsegs m A (cursor_cells body len 0 0).
Proof.
  intros m A len H. replace (body =? 0) with false in H; [exact H|]. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma bc_stk_step : forall m A B cs n, stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A ->
  Z.of_nat (cells_size cs) = n -> B = A + n -> stk rsegs m lo B.
Proof. intros m A B cs n S R L E ->. rewrite <- E. exact (stk_release rsegs m lo A cs S R L). Qed.

Lemma bc_stk_close : forall m j0 jm jc j7,
  stk rsegs m lo (SPZ + -144) ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo SPZ.
Proof.
  intros m j0 jm jc j7 ST R0 RM RC R7 RS.
  eapply (bc_stk_step m (SPZ + -64) SPZ _ 64); [ | exact RS | lia | reflexivity | lia ].
  eapply (bc_stk_step m (SPZ + -71) (SPZ + -64) _ 7); [ | exact R7 | lia | reflexivity | lia ].
  eapply (bc_stk_step m (SPZ + -96) (SPZ + -71) _ 25); [ | exact RC | lia | reflexivity | lia ].
  eapply (bc_stk_step m (SPZ + -136) (SPZ + -96) _ 40); [ | exact RM | lia | reflexivity | lia ].
  eapply (bc_stk_step m (SPZ + -144) (SPZ + -136) _ 8); [ exact ST | exact R0 | lia | reflexivity | lia ].
Qed.

(* 0x13dd0..0x13df4: the epilogue with a0 = v. *)
Lemma bc_epi : forall (v : Z) (m : word -> option byte)
    (ra' t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 : word) (j0 jm jc j7 : list byte),
  v = body_check bb ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
                         s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13dd0) fc None m (seg_rom rsegs)).
Proof.
  intros v m ra' t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 j0 jm jc j7
    -> R0 RM RC R7 RS ST MU WM MI.
  pose proof (u64_range sp) as Rsp.
  do 10 step.
  apply evt_done. unfold bcQ.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  exact (bc_stk_close m j0 jm jc j7 ST R0 RM RC R7 RS).
Qed.

(* 0x13dcc: a0 = -10 (REFUSED) when system_at bb. *)
Lemma bc_hit : forall (m : word -> option byte)
    (ra' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 : word) (j0 jm jc j7 : list byte),
  system_at bb = true ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
                         s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13dcc) fc None m (seg_rom rsegs)).
Proof.
  intros m ra' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 j0 jm jc j7
    SA R0 RM RC R7 RS ST MU WM MI.
  step.
  eapply bc_epi; [ | eassumption .. ].
  rewrite body_check_spec, SA. reflexivity.
Qed.

(* 0x13da0..0x13db4: the tests of index i of the prefix scan; s1 = body + 1 + i. *)
Lemma bc_scan_body : forall i (v0 v1 : Z) m
    (ra' t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 : word) (j0 jm jc j7 : list byte),
  (i + 3 < length bb)%nat -> v1 = body + 1 + Z.of_nat i ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  (sys_hit bb i = false -> forall a3' : word,
     evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 v0) (Z_to_bv 64 v1)
                            (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) a3' a4 a5 a6 a7
                            s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13db8) fc None m (seg_rom rsegs))) ->
  evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 v0) (Z_to_bv 64 v1)
                         (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) a3 a4 a5 a6 a7
                         s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs)).
Proof.
  intros i v0 v1 m ra' t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 j0 jm jc j7
    HI E1 BB R0 RM RC R7 RS ST MU WM MI K.
  pose proof (bc_rd m body bb i (v1 + -1) BB ltac:(lia) ltac:(lia)) as HR. step. clear HR.
  step.
  destruct (Z.eqb_spec (at8 bb i) 240) as [A0|A0].
  - bc_br false.
    pose proof (bc_rd m body bb (S i) v1 BB ltac:(lia) ltac:(lia)) as HR. step. clear HR.
    step.
    destruct (Z.eqb_spec (at8 bb (S i)) 19) as [A1|A1].
    + bc_br false.
      pose proof (bc_rd m body bb (S (S (S i))) (v1 + 2) BB ltac:(lia) ltac:(lia)) as HR. step. clear HR.
      step.
      destruct (Z.eqb_spec (at8 bb (S (S (S i)))) 112) as [A3|A3].
      * bc_br true.
        eapply bc_hit; [ | eassumption .. ].
        apply system_at_true. exists i. split; [lia|].
        unfold sys_hit. rewrite A0, A1, A3. reflexivity.
      * bc_br false. apply K.
        unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) A3). apply andb_false_r.
    + bc_br true. apply K.
      unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) A1). rewrite andb_false_r. reflexivity.
  - bc_br true. apply K.
    unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) A0). reflexivity.
Qed.

(* 0x13da0..0x13dc0: the prefix scan from index i; s0 = len - 3 - i = S k. *)
Lemma bc_scan_loop : forall k i (v0 v1 : Z) m
    (ra' t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 : word) (j0 jm jc j7 : list byte),
  (i + S k + 3 = length bb)%nat ->
  (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  v0 = Z.of_nat (S k) -> v1 = body + 1 + Z.of_nat i ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 v0) (Z_to_bv 64 v1)
                         (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) a3 a4 a5 a6 a7
                         s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros i v0 v1 m ra' t0 t1 t2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 j0 jm jc j7
      HL HP E0 E1 BB R0 RM RC R7 RS ST MU WM MI;
    (eapply bc_scan_body with (i := i); [ lia | exact E1 | eassumption .. | ]);
    intros SH a3'; step; step; step.
  - bc_br false. step. step.
    eapply bc_epi; [ | eassumption .. ].
    rewrite body_check_spec. replace (system_at bb) with false; [reflexivity|].
    symmetry. apply system_at_false. intros j Hj.
    destruct (Nat.eq_dec j i) as [->|NE]; [exact SH | apply HP; lia].
  - bc_br true.
    eapply (IH (S i)); [ lia | | lia | lia | eassumption .. ].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [exact SH | apply HP; lia].
Qed.

(* 0x13d84: the prefix scan (src/diginet_codec.c:59-62), then the epilogue. *)
Lemma bc_scan : forall m (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 : word)
    (j0 jm jc j7 : list byte),
  bytes_at rsegs m body bb ->
  rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
  rw_cells rsegs m (SPZ + -96) [CB 25 jc] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
  rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length bb)))
                         (Z_to_bv 64 body) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13d84) fc None m (seg_rom rsegs)).
Proof.
  intros m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' t3 t4 t5 t6 j0 jm jc j7
    BB R0 RM RC R7 RS ST MU WM MI.
  step. step.
  destruct (Nat.lt_ge_cases (length bb) 4) as [L4|L4].
  - bc_br true. step. step.
    eapply bc_epi; [ | eassumption .. ].
    rewrite body_check_spec. replace (system_at bb) with false; [reflexivity|].
    symmetry. apply system_at_false. intros j Hj. lia.
  - bc_br false. do 5 step.
    eapply (bc_scan_loop (length bb - 4) O); [ lia | intros j Hj; lia | lia | lia | eassumption .. ].
Qed.

(* The cursor loop at 0x13d4c, after diginet_msg_next answered code for the cursor (pos, st), with
   at most k steps left. *)
Definition bc_loop_at (k : nat) : Prop :=
  forall pos st code m (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jm j0 j7 : list byte),
    (length bb - pos <= k)%nat -> (pos < length bb)%nat -> st_ok st ->
    code = mr_code (msg_step bb pos st) ->
    rw_cells rsegs m (SPZ + -136) (msg_cells body jm (msg_step bb pos st)) ->
    rw_cells rsegs m (SPZ + -96) (cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                                    (mr_st (msg_step bb pos st))) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
    rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length bb)))
                           (Z_to_bv 64 body) (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 240)
                           (Z_to_bv 64 3) (Z_to_bv 64 19) (Z_to_bv 64 112) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x13d4c) fc None m (seg_rom rsegs)).

(* 0x13d74..0x13d80: the next call of diginet_msg_next from the cursor (pos, st). *)
Lemma bc_next : forall k, bc_loop_at k ->
  forall pos st m (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jm j0 j7 : list byte),
    (length bb - pos <= k)%nat -> (pos <= length bb)%nat -> st_ok st ->
    rw_cells rsegs m (SPZ + -136) [CB 40 jm] ->
    rw_cells rsegs m (SPZ + -96) (cursor_cells body (Z.of_nat (length bb)) pos st) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m (SPZ + -144) [CB 8 j0] -> rw_cells rsegs m (SPZ + -71) [CB 7 j7] ->
    rw_cells rsegs m (SPZ + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m lo (SPZ + -144) -> munch [(SPZ + -144, SPZ)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length bb)))
                           (Z_to_bv 64 body) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 240)
                           (Z_to_bv 64 3) (Z_to_bv 64 19) (Z_to_bv 64 112) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x13d74) fc None m (seg_rom rsegs)).
Proof.
  intros k IH pos st m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 jm j0 j7
    HK HP HS MSG CUR BB R0 R7 RS ST MU WM MI.
  unfold bc_loop_at in IH.
  pose proof (u64_range sp) as Rsp.
  do 3 step.
  eapply evt_cut;
    [ eapply MN with (c := SPZ + -96) (mp := SPZ + -136) (body := body) (bb := bb) (mj := jm) (pos := pos) (st := st);
      first [ eassumption | lia ]
    | post_call rsegs m ].
  destruct (Nat.le_gt_cases (length bb) pos) as [END|NE].
  - rewrite (bcs_code_end bb pos st END). step. bc_brc.
    bc_forget_mc. eapply bc_scan; eassumption.
  - destruct (bcs_code_cases _ (bcs_code_nz bb pos st NE)) as [C|[C|[C|C]]]; rewrite C; step; bc_brc;
      (eapply IH with (pos := pos) (st := st); [ lia | exact NE | exact HS | symmetry; exact C | eassumption .. ]).
Qed.

(* 0x13d4c..0x13d70: the test of src/diginet_codec.c:54-55 on the message, then the next call. *)
Lemma bc_loop : forall k, bc_loop_at k.
Proof.
  induction k as [|k IH]; unfold bc_loop_at;
    intros pos st code m ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 jm j0 j7
      HK HP HS HC MSG CUR BB R0 R7 RS ST MU WM MI.
  { exfalso. lia. }
  pose proof (u64_range sp) as Rsp.
  pose proof (msg_step_progress bb pos st HP) as PR.
  pose proof (msg_step_st_ok bb pos st HS) as SO.
  assert (NX : forall (a0' a1' : word) (mj' : list byte), rw_cells rsegs m (SPZ + -136) [CB 40 mj'] ->
    evt rsegs bcQ (MS (mkR ra' (Z_to_bv 64 (SPZ + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length bb)))
                           (Z_to_bv 64 body) a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 240)
                           (Z_to_bv 64 3) (Z_to_bv 64 19) (Z_to_bv 64 112) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x13d74) fc None m (seg_rom rsegs))).
  { intros a0' a1' mj' MSG'.
    eapply (bc_next k IH (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) with (jm := mj');
      first [ eassumption | lia ]. }
  subst code.
  destruct (mr_kind (msg_step bb pos st)) eqn:K.
  - (* MkEnd *)
    exfalso. exact (bcs_code_nz bb pos st HP K).
  - (* MkSysex: 1 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bcs_sysex bb pos st K) as (j & Er & Hj & Hf0).
    rewrite Er in MSG. unfold msg_cells in MSG.
    cbn [is_end mr_kind writes_status writes_running writes_sysex writes_len
         mr_status mr_running mr_d1 mr_d2 mr_sysex mr_sysex_len mr_start mr_len] in MSG.
    step. step. bc_brc.
    step. step.
    destruct (Nat.lt_ge_cases j 3) as [J3|J3].
    + bc_br true.
      destruct (bc_forget40 _ _ _ MSG eq_refl) as [mj' MSG']. exact (NX _ _ mj' MSG').
    + bc_br false.
      step.
      pose proof (bc_rd m body bb (S pos) (body + Z.of_nat (S pos)) BB ltac:(lia) eq_refl) as HR.
      step. clear HR.
      step.
      destruct (Z.eqb_spec (at8 bb (S pos)) 19) as [A1|A1].
      * bc_br false.
        pose proof (bc_rd m body bb (S pos + 2) (body + Z.of_nat (S pos) + 2) BB ltac:(lia) ltac:(lia)) as HR.
        step. clear HR.
        step.
        destruct (Z.eqb_spec (at8 bb (S pos + 2)) 112) as [A3|A3].
        -- bc_br true.
           destruct (bc_forget40 _ _ _ MSG eq_refl) as [mj' MSG'].
           destruct (bc_forget25 _ _ _ CUR eq_refl) as [jc CUR'].
           eapply bc_hit; [ | eassumption .. ].
           apply system_at_true. exists pos. split; [lia|].
           unfold sys_hit. rewrite Hf0, A1. replace (S (S (S pos))) with (S pos + 2)%nat by lia.
           rewrite A3. reflexivity.
        -- bc_br false.
           destruct (bc_forget40 _ _ _ MSG eq_refl) as [mj' MSG']. exact (NX _ _ mj' MSG').
      * bc_br true.
        destruct (bc_forget40 _ _ _ MSG eq_refl) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkSysexCut: -6 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bc_forget40 _ _ _ MSG (bc_msg_size _ _ _)) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkBadStatus: -8 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bc_forget40 _ _ _ MSG (bc_msg_size _ _ _)) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkNoStatus: -7 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bc_forget40 _ _ _ MSG (bc_msg_size _ _ _)) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkChanShort: -6 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bc_forget40 _ _ _ MSG (bc_msg_size _ _ _)) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkChanCut: -6 *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    destruct (bc_forget40 _ _ _ MSG (bc_msg_size _ _ _)) as [mj' MSG']. exact (NX _ _ mj' MSG').
  - (* MkChan: 1, with a status 80..EF *)
    rewrite (bcs_code_lit _ _ K). step. bc_brc.
    pose proof (bcs_chan_status bb pos st HS K) as CS.
    unfold msg_cells, is_end in MSG. rewrite K in MSG.
    cbn [writes_status writes_running writes_sysex writes_len] in MSG.
    step. step. bc_br true.
    destruct (bc_forget40 _ _ _ MSG eq_refl) as [mj' MSG']. exact (NX _ _ mj' MSG').
Qed.

Lemma bc_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m0 body bb -> stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m' /\
       wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DIGINET_BODY_CHECK) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 BB ST MI.
  change (evt rsegs bcQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cec) fc None m0 (seg_rom rsegs))).
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(SPZ - 144, SPZ)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  carve_frame 144%nat ST.
  (* the prologue: ra, s0..s6 at sp - 8 .. sp - 64; then diginet_cursor_init (sp - 96, body, len) *)
  do 15 step.
  lazymatch goal with FR : rw_cells rsegs ?mm (SPZ + -144) _ |- _ =>
    destruct (bc_frame_split _ _ _ _ (SPZ + -136) (SPZ + -96) (SPZ + -71) (SPZ + -64) FR
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (j0 & jm & jc & j7 & R0 & RM & RC & R7 & RS);
    clear FR
  end.
  destruct (Z.lt_ge_cases body (2^64)) as [BL|BL].
  2: {
    (* body = 2^64: the body is empty and a0 is NULL. *)
    assert (L0 : length bb = O) by lia.
    assert (Z0 : Z_to_bv 64 body = Z_to_bv 64 0).
    { apply bv_eq. rewrite !unsigned_lit_wrap. replace body with (2^64) by lia. reflexivity. }
    rewrite Z0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
        [ eapply CI with (c := SPZ + -96) (body := 0) (len := Z.of_nat (length bb)) (cj := jc) (a2 := Z_to_bv 64 0);
          first [ eassumption | lia ]
        | post_call rsegs mm ]
    end.
    match goal with H : rw_cells _ ?mm _ (cursor_cells _ (if _ then _ else _) _ _) |- _ =>
      assert (CUR0 : rw_cells rsegs mm (SPZ + -96) (cursor_cells 0 (Z.of_nat (length bb)) O 0))
        by (rewrite L0; exact H);
      clear H
    end.
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BB0 : bytes_at rsegs mm 0 bb)
        by (split; [lia|]; split; [rewrite L0; cbn; lia|]; intros i Hi; rewrite L0 in Hi; lia);
      eapply evt_cut;
        [ eapply MN with (c := SPZ + -96) (mp := SPZ + -136) (body := 0) (bb := bb) (mj := jm) (pos := O) (st := 0);
          first [ eassumption | lia | (left; reflexivity) ]
        | post_call rsegs mm ]
    end.
    rewrite (bcs_code_end bb 0 0 ltac:(lia)). step. bc_brc.
    rewrite <- Z0.
    bc_forget_mc. eapply bc_scan; eassumption. }
  assert (BR1 : 0 <= body < 2^64) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply CI with (c := SPZ + -96) (body := body) (len := Z.of_nat (length bb)) (cj := jc) (a2 := Z_to_bv 64 0);
        first [ eassumption | lia ]
      | post_call rsegs mm ]
  end.
  match goal with H : rw_cells _ _ _ (cursor_cells _ (if _ then _ else _) _ _) |- _ => apply bc_ci_fix in H end.
  (* diginet_msg_next (sp - 96, sp - 136) from the cursor (0, 0) *)
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply MN with (c := SPZ + -96) (mp := SPZ + -136) (body := body) (bb := bb) (mj := jm) (pos := O) (st := 0);
        first [ eassumption | lia | (left; reflexivity) ]
      | post_call rsegs mm ]
  end.
  destruct (Nat.le_gt_cases (length bb) 0) as [END|NE].
  - rewrite (bcs_code_end bb 0 0 END). step. bc_brc.
    bc_forget_mc. eapply bc_scan; eassumption.
  - pose proof (bc_loop (length bb)) as L. unfold bc_loop_at in L.
    destruct (bcs_code_cases _ (bcs_code_nz bb 0 0 NE)) as [C|[C|[C|C]]]; rewrite C; step; bc_brc; do 5 step;
      (eapply L with (pos := O) (st := 0);
       [ lia | exact NE | left; reflexivity | symmetry; exact C | eassumption .. ]).
Qed.

End Walk.

Theorem diginet_body_check_holds :
  diginet_cursor_init_contract -> diginet_msg_next_contract -> diginet_body_check_contract.
Proof.
  intros CI MN. unfold diginet_body_check_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB BB ST LO DJ MI.
  pose proof (bytes_at_bound _ _ _ _ BB) as [BB1 BB2].
  pose proof ST as (LO0 & _ & _).
  eapply bc_main; try eassumption; lia.
Qed.
