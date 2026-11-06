(* Case 6 of the op loop of LLVMFuzzerTestOneInput (ubsan, fuzz_transport.c:1200-1205): the model's side. The
   worlds op_begin_m leaves (op6_bg after its two memsets, op6_bb after its last two writes), m_close_m's test and
   the world it hands to m_set (op6_x), the facts the machine walk needs about them, and the model's op 6 split into
   its three calls (op6_split). No machine here: U/Prog/T/LLVMFuzzerTestOneInput_op6_{head,mid,tail}.v walk the code,
   U/Prog/T/LLVMFuzzerTestOneInput_op6.v binds the pieces to llvm_op_stmt 6. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the model's worlds of op 6 *)

(* op_begin_m's two memsets (TCb.v:341-342) and its result (:343-344) *)
Definition op6_bg (B : list byte) : list byte :=
  upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)).
Definition op6_bb (B : list byte) : list byte :=
  set_M_fail (set_OW_desk_off (op6_bg B) (-1)) (g_fail_next (set_OW_desk_off (op6_bg B) (-1))).

(* m_close_m's test (TCb.v:334) and the world it hands to m_set (:333-337), OW.e3 being 0 after op_begin *)
Definition op6_cond (Bb : list byte) : bool :=
  truth (M_desk_known Bb) && negb (truth (M_foreign Bb)) && negb (M_state Bb =? S_CLOSED).
Definition op6_x (B : list byte) : list byte :=
  if op6_cond (op6_bb B) then set_M_fail (set_OW_e3 (op6_bb B) 1) 0 else op6_bb B.

Lemma op6_begin_eq : forall B, op_begin_m B = Some (op6_bb B, tt).
Proof. intros B. reflexivity. Qed.

(* inversion of the model's results, by name (never injection on a world-carrying option) *)
Lemma op6_inv1 : forall (X Y : list byte), Some (X, tt) = Some (Y, tt) -> X = Y.
Proof. intros X Y H. injection H as E. exact E. Qed.

Lemma op6_inv3 : forall (X Y : list byte) (u v : fuzz_in) (p q : nat),
  Some (X, (u, p)) = Some (Y, (v, q)) -> X = Y /\ u = v /\ p = q.
Proof. intros X Y u v p q H. injection H as E1 E2 E3. auto. Qed.

Lemma op6_lu : forall (X v : list byte) k, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd X k v) = Z.to_nat W_LEN.
Proof.
  intros X v k L Hk Hv. rewrite length_upd; [exact L | lia | rewrite L; unfold W_LEN in *; lia].
Qed.

Lemma op6_len_put : forall (X : list byte) k n v, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> length (upd X k (put n v)) = Z.to_nat W_LEN.
Proof. intros X k n v L Hk Hn. apply op6_lu; [exact L | exact Hk | rewrite length_put; exact Hn]. Qed.

Lemma op6_uo : forall (X v : list byte) (k k' : Z) (nn : nat),
  length X = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' -> k + Z.of_nat (length v) <= W_LEN ->
  (k' + Z.of_nat nn <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd X k v) k' nn = u_at X k' nn.
Proof.
  intros X v k k' nn L Hk Hk' Hv Hd. apply u_at_upd_out; [lia | lia | lia |].
  rewrite L. unfold W_LEN in *. lia.
Qed.

(* a put-write that misses g_fail_next leaves it *)
Lemma op6_gf_put : forall (X : list byte) k n v, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd X k (put n v)) = g_fail_next X.
Proof.
  intros X k n v L Hk Hn Hd. unfold g_fail_next.
  apply op6_uo; rewrite ?length_put; [exact L | exact Hk | unfold OFF_g_fail_next; lia | exact Hn | lia].
Qed.

(* the length of a chain of put-writes on a world of length W_LEN *)
Ltac op6_lenp L :=
  first [ exact L | apply op6_len_put; [ op6_lenp L | lia | unfold W_LEN in *; lia ] ].

Lemma op6_bg_len : forall B, length B = Z.to_nat W_LEN -> length (op6_bg B) = Z.to_nat W_LEN.
Proof.
  intros B L. unfold op6_bg, OFF_OW, OFF_GOT, SZ_OW, SZ_GOT.
  apply op6_lu; [apply op6_lu; [exact L | lia | rewrite repeat_length; unfold W_LEN; lia] | lia |
                 rewrite repeat_length; unfold W_LEN; lia].
Qed.

Lemma op6_bg_gf : forall B, length B = Z.to_nat W_LEN -> g_fail_next (op6_bg B) = g_fail_next B.
Proof.
  intros B L.
  assert (L1 : length (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) = Z.to_nat W_LEN)
    by (apply op6_lu; [exact L | unfold OFF_OW; lia | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia]).
  unfold op6_bg, g_fail_next.
  rewrite op6_uo; [| exact L1 | unfold OFF_GOT; lia | unfold OFF_g_fail_next; lia
                   | rewrite repeat_length; unfold OFF_GOT, SZ_GOT, W_LEN; lia
                   | rewrite repeat_length; unfold OFF_GOT, SZ_GOT, OFF_g_fail_next; lia].
  rewrite op6_uo; [reflexivity | exact L | unfold OFF_OW; lia | unfold OFF_g_fail_next; lia
                   | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia
                   | rewrite repeat_length; unfold OFF_OW, SZ_OW, OFF_g_fail_next; lia].
Qed.

(* op_begin's last two writes (:392-393): the machine writes M.fail (88) before OW.desk_off (65544), the model
   after; the spans are disjoint and OW.desk_off's write does not move g_fail_next *)
Lemma op6_bb_eq : forall B, length B = Z.to_nat W_LEN ->
  upd (upd (op6_bg B) 88 (put 4 (g_fail_next (op6_bg B)))) 65544 (put 4 (-1)) = op6_bb B.
Proof.
  intros B L. pose proof (op6_bg_len B L) as Lg.
  unfold op6_bb, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  rewrite (op6_gf_put (op6_bg B) 65544 4 (-1) Lg) by (unfold W_LEN, OFF_g_fail_next; lia).
  apply upd_upd_comm; rewrite ?length_put, ?Lg; unfold W_LEN; lia.
Qed.

Lemma op6_bb_len : forall B, length B = Z.to_nat W_LEN -> length (op6_bb B) = Z.to_nat W_LEN.
Proof.
  intros B L. pose proof (op6_bg_len B L) as Lg. rewrite <- (op6_bb_eq B L). op6_lenp Lg.
Qed.

Lemma op6_bb_gf : forall B, length B = Z.to_nat W_LEN -> g_fail_next (op6_bb B) = g_fail_next B.
Proof.
  intros B L. pose proof (op6_bg_len B L) as Lg. rewrite <- (op6_bb_eq B L).
  assert (L1 : length (upd (op6_bg B) 88 (put 4 (g_fail_next (op6_bg B)))) = Z.to_nat W_LEN) by op6_lenp Lg.
  rewrite (op6_gf_put _ 65544 4 (-1) L1) by (unfold W_LEN, OFF_g_fail_next; lia).
  rewrite (op6_gf_put _ 88 4 _ Lg) by (unfold W_LEN, OFF_g_fail_next; lia).
  apply op6_bg_gf. exact L.
Qed.

(* m_close's first test reads M.desk_known before op_begin's last two writes *)
Lemma op6_dk : forall B, length B = Z.to_nat W_LEN -> M_desk_known (op6_bb B) = s32_at (op6_bg B) 0.
Proof.
  intros B L. pose proof (op6_bg_len B L) as Lg. rewrite <- (op6_bb_eq B L).
  assert (L1 : length (upd (op6_bg B) 88 (put 4 (g_fail_next (op6_bg B)))) = Z.to_nat W_LEN) by op6_lenp Lg.
  unfold M_desk_known, A_M_desk_known, OFF_M.
  rewrite s32_at_upd_out; rewrite ?length_put, ?L1; [| lia | lia | lia | unfold W_LEN; lia].
  rewrite s32_at_upd_out; rewrite ?length_put, ?Lg; [reflexivity | lia | lia | lia | unfold W_LEN; lia].
Qed.

(* op_begin zeroed OW, so OW.e3 is 0 and m_close's increment gives 1 *)
Lemma op6_e3 : forall B, length B = Z.to_nat W_LEN -> OW_e3 (op6_bb B) = 0.
Proof.
  intros B L. pose proof (op6_bg_len B L) as Lg. rewrite <- (op6_bb_eq B L).
  assert (L1 : length (upd (op6_bg B) 88 (put 4 (g_fail_next (op6_bg B)))) = Z.to_nat W_LEN) by op6_lenp Lg.
  assert (L0 : length (upd B 65312 (repeat (b8 0) (Z.to_nat 304))) = Z.to_nat W_LEN)
    by (apply op6_lu; [exact L | lia | rewrite repeat_length; unfold W_LEN; lia]).
  unfold OW_e3, A_OW_e3, OFF_OW.
  rewrite s32_at_upd_out; rewrite ?length_put, ?L1; [| lia | lia | lia | unfold W_LEN; lia].
  rewrite s32_at_upd_out; rewrite ?length_put, ?Lg; [| lia | lia | lia | unfold W_LEN; lia].
  unfold op6_bg, OFF_OW, OFF_GOT, SZ_OW, SZ_GOT.
  rewrite s32_at_upd_out; rewrite ?repeat_length, ?L0; [| lia | lia | lia | unfold W_LEN; lia].
  unfold s32_at, u_at.
  rewrite sub_upd_d; rewrite ?repeat_length, ?L; [| lia | lia | lia | unfold W_LEN; lia].
  vm_compute. reflexivity.
Qed.

Lemma op6_close_eq : forall B, length B = Z.to_nat W_LEN ->
  m_close_m (op6_bb B) = m_set_m (set_M_fly_on (op6_x B) 0) S_CLOSED R_CLOSED.
Proof.
  intros B L. unfold m_close_m, op6_x, op6_cond. rewrite (op6_e3 B L).
  destruct (truth (M_desk_known (op6_bb B)) && negb (truth (M_foreign (op6_bb B))) &&
            negb (M_state (op6_bb B) =? S_CLOSED)); reflexivity.
Qed.

(* m_set (TCb.v:169-179) writes only OW and M.state: g_fail_next stays *)
Lemma op6_mset_gf : forall X Y st why, length X = Z.to_nat W_LEN ->
  m_set_m X st why = Some (Y, tt) -> g_fail_next Y = g_fail_next X.
Proof.
  intros X Y st why L H. unfold m_set_m in H.
  destruct (M_state X =? st).
  { apply op6_inv1 in H. subst Y. reflexivity. }
  cbv zeta in H.
  destruct (OW_n X <? TRANS_MAX) eqn:E1.
  - destruct (OW_n X <? 0) eqn:E2; cbv beta iota in H; [discriminate H|].
    destruct (int_inc (OW_n X)) as [n1|]; cbv beta iota in H; [|discriminate H].
    apply op6_inv1 in H. subst Y.
    apply Z.ltb_lt in E1. apply Z.ltb_ge in E2.
    unfold set_M_state, set_OW_n, set_OW_t_reason, set_OW_t_old, set_OW_t_state,
      A_M_state, A_OW_n, A_OW_t_reason, A_OW_t_old, A_OW_t_state, OFF_M, OFF_OW, TRANS_MAX in *.
    repeat (rewrite op6_gf_put by (first [ op6_lenp L | unfold W_LEN, OFF_g_fail_next in *; lia ])).
    reflexivity.
  - cbv beta iota in H.
    destruct (int_inc (OW_n X)) as [n1|]; cbv beta iota in H; [|discriminate H].
    apply op6_inv1 in H. subst Y.
    unfold set_M_state, set_OW_n, A_M_state, A_OW_n, OFF_M, OFF_OW.
    repeat (rewrite op6_gf_put by (first [ op6_lenp L | unfold W_LEN, OFF_g_fail_next in *; lia ])).
    reflexivity.
Qed.

(* op 6 of the model (TOps.v:320-325) after op_begin, its three calls by name *)
Lemma op6_split : forall I B A D c k B1 c2 k1,
  snd (fuzz_u8_m D c) mod 9 = 6 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c2, k1)) ->
  exists Bm B3 r, m_close_m (op6_bb B) = Some (Bm, tt) /\
    diginet_session_close_m I None Bm (g_now Bm) = Some (B3, r) /\
    settle_m B3 0 = Some (B1, tt) /\ c2 = fst (fuzz_u8_m D c) /\ k1 = k.
Proof.
  intros I B A D c k B1 c2 k1 Hop H.
  unfold LLVMFuzzerTestOneInput_op_m in H.
  destruct (fuzz_u8_m D c) as [c0 opb]. cbn [fst snd] in Hop |- *.
  cbv beta iota zeta in H. rewrite Hop in H.
  change (6 =? 0) with false in H. change (6 =? 1) with false in H. change (6 =? 2) with false in H.
  change (6 =? 3) with false in H. change (6 =? 4) with false in H. change (6 =? 5) with false in H.
  change (6 =? 6) with true in H. cbv beta iota in H.
  rewrite op6_begin_eq in H. cbv beta iota in H.
  destruct (m_close_m (op6_bb B)) as [[Bm []]|] eqn:E1; cbv beta iota in H; [|discriminate H].
  destruct (diginet_session_close_m I None Bm (g_now Bm)) as [[B3 r]|] eqn:E2; cbv beta iota in H;
    [|discriminate H].
  destruct (settle_m B3 0) as [[B4 []]|] eqn:E3; cbv beta iota in H; [|discriminate H].
  apply op6_inv3 in H. destruct H as (<- & <- & <-).
  exists Bm, B3, r. split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. split; reflexivity.
Qed.

Lemma op6_cursor : forall D c, llvm_cursor D c -> fi_n c <> 0 -> llvm_cursor D (fst (fuzz_u8_m D c)).
Proof.
  intros D c (H1 & H2 & H3) Hn. unfold fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  unfold llvm_cursor. cbn [fst fi_off fi_n]. lia.
Qed.

(* a 32-bit field against a small literal, as the zified branch states it (the plain case 6) *)
Lemma op6_s32_eq : forall x c, -2^31 <= x < 2^31 -> 0 <= c < 2^31 ->
  (x mod 18446744073709551616 = c <-> x = c).
Proof.
  intros x c Hx Hc. split; intros E; [|subst; apply Z.mod_small; lia].
  destruct (Z_le_gt_dec 0 x) as [P|N]; [rewrite Z.mod_small in E by lia; lia|].
  rewrite <- (Z.mod_add x 1 18446744073709551616) in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.

(* m_close's then arm (:381-382): OW.e3 = 1, M.fail = 0 *)
Lemma op6_then_len : forall B, length B = Z.to_nat W_LEN ->
  length (set_M_fail (set_OW_e3 (op6_bb B) 1) 0) = Z.to_nat W_LEN.
Proof.
  intros B L. pose proof (op6_bb_len B L) as Lb.
  unfold set_M_fail, set_OW_e3, A_M_fail, A_OW_e3, OFF_M, OFF_OW. op6_lenp Lb.
Qed.

Lemma op6_then_gf : forall B, length B = Z.to_nat W_LEN ->
  g_fail_next (set_M_fail (set_OW_e3 (op6_bb B) 1) 0) = g_fail_next B.
Proof.
  intros B L. pose proof (op6_bb_len B L) as Lb.
  assert (L1 : length (set_OW_e3 (op6_bb B) 1) = Z.to_nat W_LEN)
    by (unfold set_OW_e3, A_OW_e3, OFF_OW; op6_lenp Lb).
  unfold set_M_fail, A_M_fail, OFF_M.
  rewrite (op6_gf_put _ (0 + 88) 4 0 L1) by (unfold W_LEN, OFF_g_fail_next; lia).
  unfold set_OW_e3, A_OW_e3, OFF_OW.
  rewrite (op6_gf_put _ (65312 + 200) 4 1 Lb) by (unfold W_LEN, OFF_g_fail_next; lia).
  apply op6_bb_gf. exact L.
Qed.

Lemma op6_x_len : forall B, length B = Z.to_nat W_LEN -> length (op6_x B) = Z.to_nat W_LEN.
Proof.
  intros B L. unfold op6_x.
  destruct (op6_cond (op6_bb B)); [apply op6_then_len | apply op6_bb_len]; exact L.
Qed.
