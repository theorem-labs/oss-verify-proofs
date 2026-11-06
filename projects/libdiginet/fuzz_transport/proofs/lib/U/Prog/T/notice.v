(* notice (fuzz/fuzz_transport.c:937-973; model TCb.v notice_m), entry 0x14bc8, 85 instructions (0x14bc8-0x14d18).
   Prologue `addi sp,sp,-16; sd ra,8(sp)`; the UBSan checks of the pointer n (NULL at 0x14bd0, misaligned at
   0x14bd8) are closed by ntc_at (0 < p, p mod 8 = 0). n->kind - 1 is bounded by `bltu` (0x14be8: out of 1..6 is the
   default arm, the `ret` at 0x14d0c) and indexes the jump table at 0x10438 in .rodata (read from the image under
   mem_inv): DESK 0x14c08, STATE 0x14c84, DATA 0x14c40, ACKED 0x14c60, ACK_LOST 0x14c2c, FOREIGN 0x14cf8.
   Every `unimp` (0x14d18) branch is closed from the model premise: the signed-overflow checks of GOT.n++ /
   GOT.acked++ / GOT.desk++ / GOT.ndata++ / GOT.foreign++ (`blt` after `addiw`) by int_inc's Some, the bound of
   GOT.t[GOT.n] (`bgeu` at 0x14c9c) by the model's `GOT.n < 0 -> None`, and its pointer-overflow check (`bltu` at
   0x14cb4) by computation. check_state_desk, check_inflight_acked and check_state_online are tail calls from the
   entry sp (frame popped first); check_inflight_lost and check_state_data are `jal` calls from sp - 16.
   Each callee gets the notice ntrunc n: n with the announce's version and name cut to their first 10 bytes.
   ntc_at bounds the announce only by [a, a + 20) (off the world and off the window), not the lists' lengths,
   so a longer list need not survive notice's own stores (GOT, the saved ra); the 10-byte prefixes lie inside
   [a, a + 20), and check_state_desk_m reads at most version[9] / name[9] (strz_len <= 9), so it answers the same
   (desk_trunc); the other checks do not read the announce. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import check_state_online_c
  check_inflight_acked_c check_inflight_lost_c check_state_desk_c check_state_data_c notice_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the notice a callee gets: the announce's version and name cut to 10 bytes ---- *)

Definition ntr (a : tann) : tann := TAnn (firstn 10 (ta_version a)) (firstn 10 (ta_name a)).
Definition ntrunc (n : ntc) : ntc :=
  Ntc (n_kind n) (n_state n) (n_old n) (n_reason n) (n_counter n) (n_retry n) (n_mac_offset n) (n_pers n)
      (option_map ntr (n_ann n)) (n_body n) (n_body_len n).

Lemma nt_nth_firstn : forall (l : list byte) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d H.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma nt_len_firstn : forall (l : list byte) v, (v <= 9)%nat ->
  (length (firstn 10 l) <=? v)%nat = (length l <=? v)%nat.
Proof.
  intros l v Hv. rewrite length_firstn.
  destruct (Nat.leb_spec (Nat.min 10 (length l)) v); destruct (Nat.leb_spec (length l) v); lia.
Qed.

Lemma nt_strz_le : forall F a v, frame_strz_len F a = Some v -> (v <= 9)%nat.
Proof.
  intros F a v H. unfold frame_strz_len, list_strz_len in H. destruct F as [f|]; [|discriminate H].
  destruct (a - tf_addr f <? 0); [discriminate H|].
  match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate H|].
  injection H as <-. apply strz_len_le.
Qed.

(* check_state_desk reads version[0 .. 9] and name[0 .. 9] at most *)
Lemma desk_trunc : forall I F B n, check_state_desk_m I F B (ntrunc n) = check_state_desk_m I F B n.
Proof.
  intros I F B n. unfold check_state_desk_m, ntrunc. cbn [n_pers n_mac_offset n_ann].
  destruct (n_ann n) as [a|]; cbn [option_map]; [|reflexivity].
  repeat lazymatch goal with
  | |- (if ?c then _ else _) = (if ?c then _ else _) => destruct c; cbn beta iota zeta; [try reflexivity | try reflexivity]
  | |- match ?x with Some _ => _ | None => _ end = match ?x with Some _ => _ | None => _ end =>
      let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta; [ | reflexivity]
  end.
  cbn [ntr ta_version ta_name].
  pose proof (nt_strz_le _ _ _ E0). pose proof (nt_strz_le _ _ _ E1).
  rewrite !firstn_firstn, !(Nat.min_l _ 10) by lia.
  rewrite !nt_len_firstn by lia. rewrite !nt_nth_firstn by lia.
  reflexivity.
Qed.

(* ---- moving the premises the callees ask for from notice's entry memory ---- *)

Lemma nt_bytes_firstn : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof. intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma nt_tr : forall (sp : word) m m' a bs,
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bytes_at rsegs m a bs ->
  (a + Z.of_nat (length bs) <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= a) ->
  (a + Z.of_nat (length bs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a) ->
  bytes_at rsegs m' a bs.
Proof.
  intros sp m m' a bs MU Hb Hw Hs. apply (bytes_at_transport rsegs _ m m' a bs Hb MU).
  cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ntc_move : forall m m' p n (sp sp' : word) K',
  ntc_at m p n sp 48 ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bv_unsigned sp - 48 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  ntc_at m' p (ntrunc n) sp' K'.
Proof.
  intros m m' p n sp sp' K' NT MU H1 H2.
  destruct NT as (Hp0 & Hp8 & OW & OS & NB & NBb & NBl & K0 & K4 & K8 & K12 & KP & KM & KBL & KC & KR & BB & BBw & BBs
                  & ANN).
  unfold off_world, off_window in *.
  unfold ntc_at, off_world, off_window, ntrunc. cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len
                                                    n_counter n_retry n_body n_ann].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  exists NB. split; [apply (nt_tr sp m m'); [exact MU | exact NBb | rewrite NBl; lia | rewrite NBl; lia]|].
  split; [exact NBl|]. do 9 (split; [assumption|]).
  split; [apply (nt_tr sp m m'); [exact MU | exact BB | lia | lia]|].
  split; [lia|]. split; [lia|].
  destruct (n_ann n) as [a|]; cbn [option_map].
  - destruct ANN as (A0 & A8 & AV & AN & AW & AS). cbn [ntr ta_version ta_name].
    assert (LV : (length (firstn 10 (ta_version a)) <= 10)%nat) by (rewrite length_firstn; lia).
    assert (LN : (length (firstn 10 (ta_name a)) <= 10)%nat) by (rewrite length_firstn; lia).
    split; [lia|]. split; [lia|].
    split; [apply (nt_tr sp m m'); [exact MU | apply nt_bytes_firstn; exact AV | lia | lia]|].
    split; [apply (nt_tr sp m m'); [exact MU | apply nt_bytes_firstn; exact AN | lia | lia]|].
    split; lia.
  - exact ANN.
Qed.

Lemma tf_move : forall m m' (sp sp' : word) K' Fr,
  tframe_at m sp 48 Fr ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bv_unsigned sp - 48 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' Fr.
Proof.
  intros m m' sp sp' K' [fr|] TF MU H1 H2; [|exact I].
  unfold tframe_at in *. destruct TF as (T0 & TB & TW & TS). unfold off_world, off_window in *.
  split; [exact T0|]. split; [apply (nt_tr sp m m'); [exact MU | exact TB | lia | lia]|]. split; lia.
Qed.

Lemma rr_move : forall m m' (sp : word),
  relro_img m ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 48 ->
  relro_img m'.
Proof.
  intros m m' sp RR MU WS i Hi. specialize (RR i Hi). unfold mrd in RR |- *.
  rewrite (MU (wa (RELRO_BASE + i))); [exact RR|].
  unfold wa. rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
  cbn [outside]. unfold RELRO_BASE, RELRO_LEN, W_BASE_UBSAN, W_LEN in *. split; [lia|]. split; [lia | exact I].
Qed.

(* ---- machine arithmetic ---- *)

Lemma nt_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small; [reflexivity | change (bv_half_modulus 64) with (2^63); lia
                            | change (bv_half_modulus 64) with (2^63); lia].
Qed.

Lemma nt_ltu : forall x y, bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 <? y mod 2^64).
Proof. intros. unfold bv_ltu. rewrite !unsigned_lit_wrap. reflexivity. Qed.

Lemma nt_eqb : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 =? y mod 2^64).
Proof. intros. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

Lemma nt_land7 : forall p, 0 <= p < 2^64 -> p mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 p)) 7 = 0.
Proof.
  intros p Hp H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8.
Qed.

(* addiw rd, rs, 1 of an int below INT_MAX *)
Lemma nt_inc : forall g, -2^31 <= g < 2^31 - 1 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 g) + 1) = g + 1.
Proof.
  intros g Hg. rewrite unsigned_lit_wrap.
  assert (E : bv_swrap 32 (g mod 2 ^ 64 + 1) = bv_swrap 32 (g + 1)).
  { unfold bv_swrap, bv_wrap. f_equal.
    change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
    rewrite (Z.mod_eq g (2^64)) by lia.
    replace (g - 2 ^ 64 * (g / 2 ^ 64) + 1 + 2 ^ 31) with ((g + 1 + 2^31) + (- (2^32 * (g / 2^64))) * 2^32) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite E. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(* n->kind - 1 out of 0 .. 5, unsigned *)
Lemma nt_kind_oob : forall k, -2^31 <= k < 2^31 -> k < 1 \/ 6 < k ->
  bv_ltu (Z_to_bv 64 5) (Z_to_bv 64 (k + -1)) = true.
Proof.
  intros k Hk Ho. rewrite nt_ltu. rewrite (Z.mod_small 5) by lia. apply Z.ltb_lt.
  destruct (Z.ltb_spec k 1).
  - rewrite <- (Z_mod_plus_full (k + -1) 1 (2^64)). rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* 12 * i from `slli a3,a2,2; slli a4,a2,4; sub a3,a4,a3` *)
Lemma nt_x12 : forall g, 0 <= g < 16 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 g)) 4)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 g)) 2))) = Z_to_bv 64 (12 * g).
Proof.
  intros g Hg. rewrite (unsigned_lit g) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Ltac bsolve :=
  lazymatch goal with
  | |- negb _ = true => apply Bool.negb_true_iff; bsolve
  | |- negb _ = false => apply Bool.negb_false_iff; bsolve
  | |- (_ =? _) = true => apply Z.eqb_eq; lia
  | |- (_ =? _) = false => apply Z.eqb_neq; lia
  | |- (_ <? _) = true => apply Z.ltb_lt; lia
  | |- (_ <? _) = false => apply Z.ltb_ge; lia
  | |- (_ <=? _) = true => apply Z.leb_le; lia
  | |- (_ <=? _) = false => apply Z.leb_gt; lia
  end.

Ltac zmod_small :=
  repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end.

(* a signed 64-bit compare against a small constant *)
Lemma nt_eqb_s : forall x c, -2^63 <= x < 2^63 -> 0 <= c < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 c) = (x =? c).
Proof.
  intros x c Hx Hc. rewrite nt_eqb. rewrite (Z.mod_small c) by lia.
  destruct (Z.ltb_spec x 0) as [N|P].
  - rewrite <- (Z_mod_plus_full x 1 (2^64)). rewrite Z.mod_small by lia.
    destruct (Z.eqb_spec (x + 1 * 2^64) c); destruct (Z.eqb_spec x c); first [reflexivity | exfalso; lia].
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the branch condition at the current pc is v *)
Ltac take v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let C := fresh "C" in
      assert (C : c = v) by (rewrite ?nt_eqb_s, ?nt_lts, ?nt_ltu, ?nt_eqb by lia; zmod_small; bsolve);
      rewrite C; cbv iota; clear C
  end.

(* the world premise / post: the one world cell in the context (eassumption would first try to unify it with
   other memory facts, which unfolds them and costs tens of seconds) *)
Ltac wexact := match goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => exact H end.

(* the model's int_inc x = Some _ : x is not INT_MAX *)
Ltac inc_some NM x :=
  revert NM; unfold int_inc; destruct (Z.eqb_spec x INT_MAX) as [? | ?]; intros NM; [discriminate NM|].

(* 0x14d0c ld ra,8(sp); addi sp,sp,16; ret, and the post *)
Ltac epi :=
  step; step;
  lazymatch goal with FR : rw_cells rsegs ?mm (bv_unsigned ?sp + -16) _, ST : stk rsegs ?mm _ (bv_unsigned ?sp + -16) |- _ =>
    release_frame FR ST (bv_unsigned sp) end;
  step;
  apply evt_done; hnf; do 16 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].

(* after a tail call: the callee's post is notice's (frame popped, world as the callee left it) *)
Ltac tail_fin :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & mz & Eq & MUc & WMc
                  & MIc & STc & EB & WMz);
  subst ms';
  apply evt_done; hnf; do 15 eexists; exists mz; split; [reflexivity|];
  split; [eapply munch_trans; [eassumption | eapply munch_weaken; [| exact MUc]];
          unfold sub_fp; intros ? ?; cbn [outside] in *; split; [lia | exact I]|];
  split; [eapply wmono_trans; eassumption|];
  split; [exact MIc|]; split; [exact STc|]; rewrite EB; exact WMz.

(* STATE from 0x14cd4 (both GOT.n cases): GOT.n++, then check_state_online (tail call) when n->state is ONLINE *)
Ltac state_tail B p NB NBl K4 n NM B' lo sp Hsp ST FR MI ONL :=
  step;                                     (* 0x14cd4 addiw a3,a2,1 *)
  rewrite nt_inc by (unfold INT_MAX in *; lia);
  step;                                     (* 0x14cd8 blt a3,a2: the overflow trap *)
  take false;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let HR := fresh "HR" in
    assert (HR : ov_read_bytes rsegs mm (Z_to_bv 64 (p + 4)) 4 = Some (sub NB 4 4))
      by (apply (bytes_at_read rsegs mm p NB 4 4); [assumption | lia | rewrite NBl; lia]);
    step;                                   (* 0x14cdc lw a1,4(a1): n->state *)
    clear HR
  end;
  rewrite wm_lw, K4;
  step;                                     (* 0x14ce0 li a2,2 *)
  pose proof (length_le4 (Z_to_bv 64 (GOT_n B + 1)));
  step;                                     (* 0x14ce4 sw a3,116(a0): GOT.n *)
  match goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ (upd ?X 65084 (put 4 ?v))] |- _ =>
    change (upd X 65084 (put 4 v)) with (set_GOT_n X v) in H end;
  step;                                     (* 0x14ce8 bne a1,a2 *)
  destruct (Z.eqb_spec (n_state n) 2) as [S2|S2];
  [ take false;
    replace (n_state n =? S_ONLINE) with true in NM by (symmetry; apply Z.eqb_eq; exact S2);
    step; step;                             (* 0x14cec ld ra,8(sp); 0x14cf0 addi sp,sp,16 *)
    release_frame FR ST (bv_unsigned sp);
    step;                                   (* 0x14cf4 j check_state_online *)
    eapply evt_cut;
    [ eapply ONL with (lo := lo) (B' := B');
      [ wexact | exact NM | exact Hsp | exact ST | lia | unfold w_off_stack; lia | exact MI ]
    | tail_fin ]
  | take true;
    replace (n_state n =? S_ONLINE) with false in NM by (symmetry; apply Z.eqb_neq; exact S2);
    injection NM as <-;
    epi; wexact ].

Theorem notice_holds : check_state_online_contract -> check_inflight_acked_contract -> check_inflight_lost_contract ->
  check_state_desk_contract -> check_state_data_contract -> notice_contract.
Proof.
  intros ONL ACK LOST DESK DATA.
  unfold check_state_online_contract, check_state_online_ENTRY, check_state_online_FRAME in ONL.
  unfold check_inflight_acked_contract, check_inflight_acked_ENTRY, check_inflight_acked_FRAME in ACK.
  unfold check_inflight_lost_contract, check_inflight_lost_ENTRY, check_inflight_lost_FRAME in LOST.
  unfold check_state_desk_contract, check_state_desk_ENTRY, check_state_desk_FRAME in DESK.
  unfold check_state_data_contract, check_state_data_ENTRY, check_state_data_FRAME in DATA.
  unfold notice_contract, notice_ENTRY, notice_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B' p n Fr
    -> NT TF RR WM NM Hsp ST LO WS MI.
  pose proof NT as NT0.
  destruct NT0 as (Hp0 & Hp8 & OWp & OSp & NB & NBb & NBl & K0 & K4 & K8 & K12 & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bytes_at_bound rsegs m p NB NBb) as PB. rewrite NBl in PB.
  pose proof (s32_range NB 0) as KR. rewrite K0 in KR.
  pose proof (s32_range NB 4) as SR. rewrite K4 in SR.
  unfold off_world in OWp. unfold off_window in OSp. unfold w_off_stack in WS.
  wk_facts.
  carve_frame 16%nat ST.
  step.                                     (* 0x14bc8 addi sp,sp,-16 *)
  step.                                     (* 0x14bcc sd ra,8(sp) *)
  step.                                     (* 0x14bd0 beqz a1: n = NULL, the ubsan trap *)
  take false.
  step.                                     (* 0x14bd4 andi a0,a1,7 *)
  step.                                     (* 0x14bd8 bnez a0: n misaligned, the ubsan trap *)
  rewrite (nt_land7 p) by lia.
  take false.
  assert (HR0 : ov_read_bytes rsegs m0 (Z_to_bv 64 p) 4 = Some (sub NB 0 4)).
  { pose proof (bytes_at_read rsegs m0 p NB 0 4 NBb ltac:(lia) ltac:(rewrite NBl; lia)) as R.
    rewrite Z.add_0_r in R. exact R. }
  step.                                     (* 0x14bdc lw a0,0(a1): n->kind *)
  clear HR0.
  rewrite wm_lw, K0.
  unfold notice_m in NM.
  assert (KC : n_kind n = 1 \/ n_kind n = 2 \/ n_kind n = 3 \/ n_kind n = 4 \/ n_kind n = 5 \/ n_kind n = 6 \/
               (n_kind n < 1 \/ 6 < n_kind n)) by lia.
  destruct KC as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]].
  7: {
    (* the default arm: kind outside 1 .. 6 *)
    unfold N_STATE, N_ACKED, N_ACK_LOST, N_DESK, N_DATA, N_FOREIGN in NM. cbv zeta in NM.
    repeat match type of NM with context [n_kind n =? ?c] =>
      replace (n_kind n =? c) with false in NM by (symmetry; apply Z.eqb_neq; lia) end.
    cbv iota in NM. injection NM as <-.
    step.                                   (* 0x14be0 addi a0,a0,-1 *)
    step.                                   (* 0x14be4 li a2,5 *)
    step.                                   (* 0x14be8 bltu a2,a0 *)
    rewrite nt_kind_oob by lia. cbv iota.
    epi. exact WM. }
  all: rewrite Hk; rewrite Hk in NM;
       cbn [Z.eqb Pos.eqb N_STATE N_ACKED N_ACK_LOST N_DESK N_DATA N_FOREIGN TRANS_MAX] in NM;
       step; step; step; take false; do 7 step.
  - (* N_DESK 0x14c08: GOT.desk++, tail call check_state_desk *)
    inc_some NM (GOT_desk B).
    pose proof (s32_range B A_GOT_desk) as GR. change (s32_at B A_GOT_desk) with (GOT_desk B) in GR.
    unfold INT_MAX in *.
    step.                                   (* 0x14c08 auipc a0 *)
    step.                                   (* 0x14c0c lw a3,1540(a0): GOT.desk *)
    change (s32_at B 65292) with (GOT_desk B).
    step.                                   (* 0x14c10 addiw a2,a3,1 *)
    rewrite nt_inc by lia.
    step.                                   (* 0x14c14 blt a2,a3: the overflow trap *)
    take false.
    pose proof (length_le4 (Z_to_bv 64 (GOT_desk B + 1))) as L4.
    step.                                   (* 0x14c18 sw a2,1540(a0) *)
    step.                                   (* 0x14c1c mv a0,a1 *)
    step.                                   (* 0x14c20 ld ra,8(sp) *)
    step.                                   (* 0x14c24 addi sp,sp,16 *)
    release_frame FR ST (bv_unsigned sp).
    step.                                   (* 0x14c28 j check_state_desk *)
    eapply evt_cut.
    { eapply DESK with (lo := lo) (B := set_GOT_desk B (GOT_desk B + 1)) (B' := B') (p := p) (n := ntrunc n)
                       (Fr := Fr).
      - reflexivity.
      - apply (ntc_move m m1 p n sp sp 48 NT MU); lia.
      - apply (tf_move m m1 sp sp 48 Fr TF MU); lia.
      - exact (rr_move m m1 sp RR MU WS).
      - wexact.
      - rewrite desk_trunc. exact NM.
      - exact Hsp.
      - exact ST.
      - exact LO.
      - unfold w_off_stack. exact WS.
      - exact MI. }
    tail_fin.
  - (* N_STATE 0x14c84: GOT.t[GOT.n] = (state, old, reason) when GOT.n < 16, GOT.n++, check_state_online
       (tail call) when the state is ONLINE *)
    unfold TRANS_MAX in NM.
    pose proof (s32_range B A_GOT_n) as GR. change (s32_at B A_GOT_n) with (GOT_n B) in GR.
    step.                                   (* 0x14c84 auipc a0 *)
    step.                                   (* 0x14c88 addi a0,a0,1092: &g_fail_next *)
    step.                                   (* 0x14c8c lw a2,116(a0): GOT.n *)
    change (s32_at B 65084) with (GOT_n B).
    step.                                   (* 0x14c90 li a3,15 *)
    step.                                   (* 0x14c94 blt a3,a2: GOT.n >= 16 skips the store *)
    destruct (Z.ltb_spec 15 (GOT_n B)) as [GH|GL].
    + (* 0x14c94 taken: GOT.n >= 16, no record *)
      take true.
      replace (GOT_n B <? 16) with false in NM by (symmetry; apply Z.ltb_ge; lia). cbv iota in NM.
      inc_some NM (GOT_n B).
      state_tail B p NB NBl K4 n NM B' lo sp Hsp ST FR MI ONL.
    + take false.
      assert (GP : 0 <= GOT_n B).
      { destruct (Z.ltb_spec (GOT_n B) 0) as [GN|GP]; [|exact GP]. exfalso. revert NM.
        replace (GOT_n B <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (GOT_n B <? 0) with true by (symmetry; apply Z.ltb_lt; exact GN). cbv iota. intros NM.
        discriminate NM. }
      replace (GOT_n B <? 16) with true in NM by (symmetry; apply Z.ltb_lt; lia).
      replace (GOT_n B <? 0) with false in NM by (symmetry; apply Z.ltb_ge; exact GP). cbv iota in NM.
      inc_some NM (GOT_n B).
      step.                                 (* 0x14c98 li a3,16 *)
      step.                                 (* 0x14c9c bgeu a2,a3: GOT.t index out of bounds, the ubsan trap *)
      take false.
      step.                                 (* 0x14ca0 slli a3,a2,2 *)
      step.                                 (* 0x14ca4 slli a4,a2,4 *)
      step.                                 (* 0x14ca8 sub a3,a4,a3: 12 * GOT.n *)
      rewrite nt_x12 by lia.
      step.                                 (* 0x14cac addi a4,a0,120: &GOT.t *)
      step.                                 (* 0x14cb0 not a4 *)
      step.                                 (* 0x14cb4 bltu a4,a3: &GOT.t[GOT.n] overflows, the ubsan trap *)
      take false.
      assert (HR4 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 4)) 4 = Some (sub NB 4 4))
        by exact (bytes_at_read rsegs m0 p NB 4 4 NBb ltac:(lia) ltac:(rewrite NBl; lia)).
      assert (HR8 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 8)) 4 = Some (sub NB 8 4))
        by exact (bytes_at_read rsegs m0 p NB 8 4 NBb ltac:(lia) ltac:(rewrite NBl; lia)).
      assert (HR12 : ov_read_bytes rsegs m0 (Z_to_bv 64 (p + 12)) 4 = Some (sub NB 12 4))
        by exact (bytes_at_read rsegs m0 p NB 12 4 NBb ltac:(lia) ltac:(rewrite NBl; lia)).
      step.                                 (* 0x14cb8 lw a4,4(a1): n->state *)
      step.                                 (* 0x14cbc lw a5,8(a1): n->old_state *)
      step.                                 (* 0x14cc0 lw a6,12(a1): n->reason *)
      clear HR4 HR8 HR12.
      rewrite !wm_lw, K4, K8, K12.
      step.                                 (* 0x14cc4 add a3,a0,a3 *)
      replace (Z_to_bv 64 (274632 + 12 * GOT_n B)) with (Z_to_bv 64 (12 * GOT_n B + 274632)) by (f_equal; lia).
      pose proof (length_le4 (Z_to_bv 64 (n_state n))) as L4s.
      pose proof (length_le4 (Z_to_bv 64 (n_old n))) as L4o.
      pose proof (length_le4 (Z_to_bv 64 (n_reason n))) as L4r.
      step.                                 (* 0x14cc8 sw a4,120(a3): GOT.t[GOT.n].state *)
      step.                                 (* 0x14ccc sw a5,124(a3): GOT.t[GOT.n].old *)
      step.                                 (* 0x14cd0 sw a6,128(a3): GOT.t[GOT.n].reason *)
      match goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WX end.
      replace (65088 + 12 * GOT_n B) with (A_GOT_t_state (GOT_n B)) in WX by (unfold A_GOT_t_state, OFF_GOT; lia).
      replace (65092 + 12 * GOT_n B) with (A_GOT_t_old (GOT_n B)) in WX by (unfold A_GOT_t_old, OFF_GOT; lia).
      replace (65096 + 12 * GOT_n B) with (A_GOT_t_reason (GOT_n B)) in WX by (unfold A_GOT_t_reason, OFF_GOT; lia).
      change (upd (upd (upd B (A_GOT_t_state (GOT_n B)) (put 4 (n_state n))) (A_GOT_t_old (GOT_n B)) (put 4 (n_old n)))
                  (A_GOT_t_reason (GOT_n B)) (put 4 (n_reason n)))
        with (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state B (GOT_n B) (n_state n)) (GOT_n B) (n_old n))
                (GOT_n B) (n_reason n)) in WX.
      state_tail B p NB NBl K4 n NM B' lo sp Hsp ST FR MI ONL.
  - (* N_DATA 0x14c40: check_state_data (jal), GOT.ndata++ *)
    destruct (check_state_data_m Fr B n) as [[B1 []]|] eqn:CD; [|discriminate NM].
    assert (Hs16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    step.                                   (* 0x14c40 mv a0,a1 *)
    step.                                   (* 0x14c44 jal check_state_data *)
    eapply evt_cut.
    { eapply DATA with (lo := lo) (B := B) (B' := B1) (p := p) (n := ntrunc n) (Fr := Fr).
      - reflexivity.
      - apply (ntc_move m m0 p n sp _ 32 NT MU); rewrite Hs16; lia.
      - apply (tf_move m m0 sp _ 32 Fr TF MU); rewrite Hs16; lia.
      - wexact.
      - exact CD.
      - rewrite Hs16. replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia.
        rewrite Z_mod_plus_full. exact Hsp.
      - rewrite Hs16. exact ST.
      - rewrite Hs16. lia.
      - unfold w_off_stack. rewrite Hs16. lia.
      - exact MI. }
    wk_post_call rsegs m0.
    match goal with E : B1 = B |- _ => subst B1 end.
    match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Hs16 in H; rename H into ST end.
    inc_some NM (GOT_ndata B).
    injection NM as <-.
    pose proof (s32_range B A_GOT_ndata) as GR. change (s32_at B A_GOT_ndata) with (GOT_ndata B) in GR.
    unfold INT_MAX in *.
    step.                                   (* 0x14c48 auipc a0 *)
    step.                                   (* 0x14c4c lw a2,1488(a0): GOT.ndata *)
    change (s32_at B 65304) with (GOT_ndata B).
    step.                                   (* 0x14c50 addiw a1,a2,1 *)
    rewrite nt_inc by lia.
    step.                                   (* 0x14c54 blt a1,a2: the overflow trap *)
    take false.
    pose proof (length_le4 (Z_to_bv 64 (GOT_ndata B + 1))) as L4.
    step.                                   (* 0x14c58 sw a1,1488(a0) *)
    step.                                   (* 0x14c5c j 0x14d0c *)
    epi. wexact.
  - (* N_ACKED 0x14c60: GOT.acked++, tail call check_inflight_acked *)
    inc_some NM (GOT_acked B).
    pose proof (s32_range B A_GOT_acked) as GR. change (s32_at B A_GOT_acked) with (GOT_acked B) in GR.
    unfold INT_MAX in *.
    step.                                   (* 0x14c60 auipc a0 *)
    step.                                   (* 0x14c64 lw a3,1460(a0): GOT.acked *)
    change (s32_at B 65300) with (GOT_acked B).
    step.                                   (* 0x14c68 addiw a2,a3,1 *)
    rewrite nt_inc by lia.
    step.                                   (* 0x14c6c blt a2,a3: the overflow trap *)
    take false.
    pose proof (length_le4 (Z_to_bv 64 (GOT_acked B + 1))) as L4.
    step.                                   (* 0x14c70 sw a2,1460(a0) *)
    step.                                   (* 0x14c74 mv a0,a1 *)
    step.                                   (* 0x14c78 ld ra,8(sp) *)
    step.                                   (* 0x14c7c addi sp,sp,16 *)
    release_frame FR ST (bv_unsigned sp).
    step.                                   (* 0x14c80 j check_inflight_acked *)
    eapply evt_cut.
    { eapply ACK with (lo := lo) (B := set_GOT_acked B (GOT_acked B + 1)) (B' := B') (p := p) (n := ntrunc n).
      - reflexivity.
      - apply (ntc_move m m1 p n sp sp 16 NT MU); lia.
      - wexact.
      - exact NM.
      - exact Hsp.
      - exact ST.
      - lia.
      - unfold w_off_stack. lia.
      - exact MI. }
    tail_fin.
  - (* N_ACK_LOST 0x14c2c: check_inflight_lost (jal), M.fly.on = 0 *)
    destruct (check_inflight_lost_m B n) as [[B1 []]|] eqn:CL; [|discriminate NM].
    injection NM as <-.
    assert (Hs16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    step.                                   (* 0x14c2c mv a0,a1 *)
    step.                                   (* 0x14c30 jal check_inflight_lost *)
    eapply evt_cut.
    { eapply LOST with (lo := lo) (B := B) (B' := B1) (p := p) (n := ntrunc n).
      - reflexivity.
      - apply (ntc_move m m0 p n sp _ 16 NT MU); rewrite Hs16; lia.
      - wexact.
      - exact CL.
      - rewrite Hs16. replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia.
        rewrite Z_mod_plus_full. exact Hsp.
      - rewrite Hs16. exact ST.
      - rewrite Hs16. lia.
      - unfold w_off_stack. rewrite Hs16. lia.
      - exact MI. }
    wk_post_call rsegs m0.
    match goal with E : B1 = B |- _ => subst B1 end.
    match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Hs16 in H; rename H into ST end.
    step.                                   (* 0x14c34 auipc a0 *)
    step.                                   (* 0x14c38 sw zero,1836(a0): M.fly.on = 0 *)
    step.                                   (* 0x14c3c j 0x14d0c *)
    epi. wexact.
  - (* N_FOREIGN 0x14cf8: GOT.foreign++ *)
    inc_some NM (GOT_foreign B).
    injection NM as <-.
    pose proof (s32_range B A_GOT_foreign) as GR. change (s32_at B A_GOT_foreign) with (GOT_foreign B) in GR.
    unfold INT_MAX in *.
    step.                                   (* 0x14cf8 auipc a0 *)
    step.                                   (* 0x14cfc lw a2,1304(a0): GOT.foreign *)
    change (s32_at B 65296) with (GOT_foreign B).
    step.                                   (* 0x14d00 addiw a1,a2,1 *)
    rewrite nt_inc by lia.
    step.                                   (* 0x14d04 blt a1,a2: the overflow trap *)
    take false.
    pose proof (length_le4 (Z_to_bv 64 (GOT_foreign B + 1))) as L4.
    step.                                   (* 0x14d08 sw a1,1304(a0) *)
    epi. wexact.
Qed.
