(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/U/Prog into libdiginet/fuzz_decode (module path and addresses only: entry 0x14028 -> 0x13e04, every other pc of the function -0x224, the callees 0x14170 -> 0x13bbc and 0x141a0 -> 0x13bec) *)
(* Modified by Theorem Labs, 2026-10: the UBSan walk of diginet_body_check against its contract. *)
(* Walk of diginet_body_check (src/diginet_codec.c:47-64 at 835f336c) in fuzz_decode.ubsan,
   0x13e04..0x13f4c. The prologue saves ra and s0..s7 in the 144-byte frame and leaves the
   message at sp - 144, the cursor at sp - 104 and those nine saved registers at sp - 72;
   diginet_cursor_init and diginet_msg_next are hypotheses.
   - ubc_loop walks the cursor loop (0x13e5c) by induction on the bytes left of the body. Each
     turn calls diginet_msg_next and reads the answer: 0 leaves the loop for the prefix scan,
     1 with the message status F0, sysex_len >= 3 and the bytes 13 and 70 of the payload gives
     -10, and every other answer takes the next turn. DgnLib.bc_loop_step joins the turns, so
     the loop keeps `bc_loop (length bb) bb 0 0 = bc_loop (length bb - pos) bb pos st`.
   - ubc_scan walks the prefix scan (0x13ed0) by induction on the bytes left, keeping that no
     index below i starts F0 13 xx 70 (DgnSpec.sys_hit); ubc_pre (0x13ea8) enters it, or
     answers 0 at once when the body is shorter than 4 bytes.
   - ubc_epi (0x13f1c) restores the registers, merges the three stack pieces back into
     [lo, sp) and answers body_check bb.
   The seven branches to the trap at 0x13f48 are never taken: at 0x13e88 and 0x13e94 the
   payload address is body + sysex_len's start, which DgnLib.msg_step_sysex keeps inside the
   body, so it is neither 0 nor within 2 of 2^64; at 0x13ed0, 0x13edc, 0x13ee0, 0x13ef0 and
   0x13efc the scan index is below length bb, and body is not 0 and body + length bb <= 2^64.
   diginet_cursor_init is called with the body address reduced mod 2^64, which its contract
   needs and which the contract of diginet_body_check allows to be 2^64 with an empty body.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  diginet_body_check_c.
Import ListNotations.
Open Scope Z_scope.

(** * Cells and the stack *)

Lemma ubc_rw_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Hl, Hw.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma ubc_rw_cons : forall m A c cs, rw_cells rsegs m A (c :: cs) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. apply (ubc_rw_app m A [c] cs) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

(* The 72 bytes below the saved registers: the message (40), the cursor (25), padding (7). *)
Lemma ubc_frame3 : forall m A j svd, rw_cells rsegs m A (CB 72 j :: svd) ->
  rw_cells rsegs m A [CB 40 (firstn 40 j)] /\ rw_cells rsegs m (A + 40) [CB 25 (firstn 25 (skipn 40 j))] /\
  rw_cells rsegs m (A + 65) (CB 7 (firstn 7 (skipn 25 (skipn 40 j))) :: svd).
Proof.
  intros m A j svd H.
  apply (rw_cells_split_CB rsegs m A [] 72 j svd [40; 25; 7]%nat) in H; [|reflexivity].
  cbn [app mk_CB_cells] in H.
  apply ubc_rw_cons in H. destruct H as [H1 H]. apply ubc_rw_cons in H. destruct H as [H2 H3].
  cbn [csize] in H2, H3. change (Z.of_nat 40) with 40 in H2, H3. change (Z.of_nat 25) with 25 in H3.
  split; [exact H1|]. split; [exact H2|]. replace (A + 65) with (A + 40 + 25) by lia. exact H3.
Qed.

Lemma ubc_msg_cells_size : forall body mj r, cells_size (msg_cells body mj r) = 40%nat.
Proof. intros body mj r. unfold msg_cells. destruct (is_end r); [reflexivity|]. destruct (writes_len _); reflexivity. Qed.

Lemma ubc_mod8 : forall x k, x mod 8 = 0 -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof. intros x k H1 H2. rewrite Zplus_mod, H1, H2. reflexivity. Qed.

Lemma ubc_firstn1 : forall (l : list byte) i, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l (b8 0)].
Proof.
  induction l as [|x l IH]; intros [|i] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

(* One byte of a readable block, named by nth so that zxb of it is at8. *)
Lemma ubc_rdb : forall m a l (i : nat), bytes_at rsegs m a l -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i l (b8 0)].
Proof.
  intros m a l i BL Hi. rewrite (bytes_at_ov_read rsegs m a l i 1 BL ltac:(lia)).
  rewrite (ubc_firstn1 l i Hi). reflexivity.
Qed.

(* the same read when the address is the register itself (offset 0) *)
Lemma ubc_rdw0 : forall m (w : word) a l (i : nat), bytes_at rsegs m a l -> (i < length l)%nat ->
  bv_unsigned w = a + Z.of_nat i -> ov_read_bytes rsegs m w 1 = Some [nth i l (b8 0)].
Proof.
  intros m w a l i BL Hi E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply ubc_rdb; assumption.
Qed.

Lemma ubc_zxb : forall x : byte, bv_unsigned (zxb x) = bz x.
Proof. intros x. unfold zxb. pose proof (bz_range x) as R. unfold bz in *. apply unsigned_lit. lia. Qed.

Lemma ubc_zxb_at8 : forall (l : list byte) i, bv_unsigned (zxb (nth i l (b8 0))) = at8 l i.
Proof. intros l i. apply ubc_zxb. Qed.

(** * The model *)

Lemma ubc_chan_status : forall b pos st, st_ok st -> mr_kind (msg_step b pos st) = MkChan ->
  0x80 <= mr_status (msg_step b pos st) < 0xf0.
Proof.
  intros b pos st Hs K. unfold msg_step in *.
  destruct (length b <=? pos)%nat; [cbn in K; discriminate|].
  destruct (at8 b pos =? 0xf0); [destruct (find_f7 _); cbn in K; discriminate|].
  destruct (Z.leb_spec 0xf0 (at8 b pos)) as [A|A]; [cbn in K; discriminate|].
  destruct (Z.leb_spec 0x80 (at8 b pos)) as [B|B].
  - rewrite (chan_step_status _ _ _ _ _ _ K). lia.
  - destruct (Z.eqb_spec st 0) as [E|E]; [cbn in K; discriminate|].
    rewrite (chan_step_status _ _ _ _ _ _ K). destruct Hs; lia.
Qed.

Lemma ubc_hit : forall b i, bc_loop (length b) b 0 0 = false -> (i + 3 < length b)%nat ->
  sys_hit b i = true -> body_check b = -10.
Proof.
  intros b i H L S. unfold body_check. rewrite H.
  replace (system_at b) with true; [reflexivity|]. symmetry. apply system_at_true. exists i. split; assumption.
Qed.

Lemma ubc_none : forall b, bc_loop (length b) b 0 0 = false -> system_at b = false -> body_check b = 0.
Proof. intros b H S. unfold body_check. rewrite H, S. reflexivity. Qed.

Lemma ubc_true : forall b, bc_loop (length b) b 0 0 = true -> body_check b = -10.
Proof. intros b H. unfold body_check. rewrite H. reflexivity. Qed.

(* A sysex step writes the status F0. *)
Lemma ubc_sysex_status : forall b pos st, st_ok st -> mr_kind (msg_step b pos st) = MkSysex ->
  mr_status (msg_step b pos st) = 240.
Proof.
  intros b pos st Hst K.
  assert (EC : mr_code (msg_step b pos st) = 1) by (unfold mr_code; rewrite K; reflexivity).
  exact (proj2 (msg_step_code1_f0 b pos st Hst EC) K).
Qed.

Lemma ubc_zxb_lit : forall z, 0 <= z < 256 -> bv_unsigned (zxb (b8 z)) = z.
Proof. intros z H. rewrite ubc_zxb. apply bz_b8. lia. Qed.

(* The cells of the message after a sysex step and after a channel step. *)
Lemma ubc_msg_sysex : forall bd mj r, mr_kind r = MkSysex ->
  msg_cells bd mj r =
  [ C1 (b8 (mr_status r)); C1 (b8 (mr_running r)); C1 (b8 (mr_d1 r)); C1 (b8 (mr_d2 r));
    CB 4 (firstn 4 (skipn 4 mj));
    C8 (Z_to_bv 64 (bd + Z.of_nat (mr_sysex r)));
    C8 (Z_to_bv 64 (Z.of_nat (mr_sysex_len r)));
    C8 (Z_to_bv 64 (Z.of_nat (mr_start r)));
    C8 (Z_to_bv 64 (Z.of_nat (mr_len r))) ].
Proof.
  intros bd mj r K. unfold msg_cells, is_end, writes_status, writes_running, writes_sysex, writes_len.
  rewrite K. reflexivity.
Qed.

Lemma ubc_msg_chan : forall bd mj r, mr_kind r = MkChan ->
  msg_cells bd mj r =
  [ C1 (b8 (mr_status r)); C1 (b8 (mr_running r)); C1 (b8 (mr_d1 r)); C1 (b8 (mr_d2 r));
    CB 4 (firstn 4 (skipn 4 mj));
    C8 (Z_to_bv 64 0);
    C8 (Z_to_bv 64 (Z.of_nat (mr_sysex_len r)));
    C8 (Z_to_bv 64 (Z.of_nat (mr_start r)));
    C8 (Z_to_bv 64 (Z.of_nat (mr_len r))) ].
Proof.
  intros bd mj r K. unfold msg_cells, is_end, writes_status, writes_running, writes_sysex, writes_len.
  rewrite K. reflexivity.
Qed.

(* diginet_cursor_init is called with the body address reduced mod 2^64 (the contract of
   diginet_body_check allows body = 2^64, and then bb is empty). *)
Lemma ubc_cur0 : forall b l, 0 < b -> 0 <= l -> b + l <= 2^64 ->
  cursor_cells (b mod 2^64) (if b mod 2^64 =? 0 then 0 else l) 0 0 = cursor_cells b l 0 0.
Proof.
  intros b l H1 H0 H2. unfold cursor_cells. rewrite Z_to_bv_mod64.
  destruct (Z.eqb_spec (b mod 2^64) 0) as [E|E]; [|reflexivity].
  change (2^64) with 18446744073709551616 in *.
  assert (Eb : b = 18446744073709551616) by (Z.div_mod_to_equations; lia).
  assert (El : l = 0) by lia. rewrite El. reflexivity.
Qed.

(** * The walk *)

Section Walk.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (body lo : Z) (bb : list byte) (Q : machine_state -> Prop).
Hypothesis CI : diginet_cursor_init_contract.
Hypothesis MN : diginet_msg_next_contract.
Hypothesis HB0 : 0 < body.
Hypothesis SP8 : bv_unsigned sp mod 8 = 0.
Hypothesis LO0 : 0 < lo.
Hypothesis LO : lo + 144 <= bv_unsigned sp.
Hypothesis DB : body + Z.of_nat (length bb) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= body.
Hypothesis HQ : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
  stk rsegs m' lo (bv_unsigned sp) ->
  Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc ra) fc None m' (seg_rom rsegs)).

Definition ubc_svd : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Local Abbreviation SPF := (Z_to_bv 64 (bv_unsigned sp + -144)).
Local Abbreviation LEN := (Z_to_bv 64 (Z.of_nat (length bb))).
Local Abbreviation BODY := (Z_to_bv 64 body).

Lemma ubc_stk4 : forall m a b c,
  stk rsegs m lo (bv_unsigned sp + -144) ->
  stk rsegs m (bv_unsigned sp + -144) a -> a = bv_unsigned sp + -104 ->
  stk rsegs m (bv_unsigned sp + -104) b -> b = bv_unsigned sp + -79 ->
  stk rsegs m (bv_unsigned sp + -79) c -> c = bv_unsigned sp ->
  stk rsegs m lo (bv_unsigned sp).
Proof.
  intros m a b c H1 H2 Ea H3 Eb H4 Ec. subst a b c.
  eapply stk_merge; [|exact H4|lia]. eapply stk_merge; [|exact H3|lia].
  eapply stk_merge; [exact H1|exact H2|lia].
Qed.

(** ** The epilogue, 0x13f1c *)

Lemma ubc_epi : forall (ra' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' t3 t4 t5 t6 : word)
    m mj cj pad,
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m (bv_unsigned sp + -144) [CB 40 mj] ->
  rw_cells rsegs m (bv_unsigned sp + -104) [CB 25 cj] ->
  rw_cells rsegs m (bv_unsigned sp + -79) (CB 7 pad :: ubc_svd) ->
  a0 = Z_to_bv 64 (body_check bb) ->
  evt rsegs Q
    (MS (mkR ra' SPF gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' t3 t4 t5 t6 m mj cj pad
    MU WM MI ST MSG CUR SV ->.
  pose proof (stk_of_rw_cells rsegs m _ _ MSG) as SM.
  pose proof (stk_of_rw_cells rsegs m _ _ CUR) as SC.
  pose proof (stk_of_rw_cells rsegs m _ _ SV) as SS.
  cbn [cells_size csize ubc_svd Nat.add] in SM, SC, SS.
  unfold ubc_svd in SV.
  do 11 step.
  apply evt_done. apply HQ; try assumption.
  eapply ubc_stk4; [exact ST | exact SM | lia | exact SC | lia | exact SS | lia].
Qed.

(** ** The prefix scan, 0x13ed0: the body has no F0 13 xx 70 before the index i *)

Ltac ubc_sub := repeat match goal with H : bv_unsigned ?w = _ |- _ => rewrite H end.
Ltac ubc_u := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
  rewrite (unsigned_lit e) by lia end.
Ltac ubc_n := ubc_sub; rewrite ?ubc_zxb_at8; rewrite ?ubc_zxb_lit by lia;
  fold_closed_in_goal; ubc_u; fold_closed_in_goal.
Ltac ubc_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?v_sltu_b2z, ?v_sltiu_b2z;
  do 3 (ubc_n; decide_tests; cbv beta iota; cbn [negb Z.b2z andb orb]);
  first [ reflexivity | solve_cond_rec ].
Ltac ubc_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; ubc_cond]
  end.
Ltac ubc_val := rewrite ?unsigned_lit_wrap; ubc_sub; Z.div_mod_to_equations; lia.

Lemma ubc_scan : forall (n i : nat) m mj cj pad
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2' s3' s4' s5' s6' s7' : word),
  (length bb - i <= n)%nat -> (i + 3 < length bb)%nat ->
  bc_loop (length bb) bb 0 0 = false ->
  (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  bytes_at rsegs m body bb ->
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m (bv_unsigned sp + -144) [CB 40 mj] ->
  rw_cells rsegs m (bv_unsigned sp + -104) [CB 25 cj] ->
  rw_cells rsegs m (bv_unsigned sp + -79) (CB 7 pad :: ubc_svd) ->
  bv_unsigned a0 = 2^64 - 1 - body -> bv_unsigned a1 = body + Z.of_nat i + 1 ->
  bv_unsigned a2 = Z.of_nat i + 3 -> bv_unsigned a3 = 1 -> bv_unsigned a4 = 240 ->
  bv_unsigned a5 = 19 -> bv_unsigned a6 = 112 -> bv_unsigned a7 = body + Z.of_nat i ->
  evt rsegs Q
    (MS (mkR ra' SPF gp tp t0 t1 t2 LEN BODY a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ed0) fc None m (seg_rom rsegs)).
Proof.
  intros n. induction n as [|n IH]; intros i m mj cj pad ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s2' s3' s4' s5' s6' s7' Hn Hi BCF NOHIT BB MU WM MI ST MSG CUR SV Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7;
    [lia|].
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  pose proof (ubc_rdb m body bb i BB ltac:(lia)) as R0.
  pose proof (ubc_rdw0 m a1 body bb (S i) BB ltac:(lia) ltac:(lia)) as R1.
  pose proof (ubc_rdb m body bb (S (S (S i))) BB ltac:(lia)) as R3.
  (* 0x13f08: the index i carries no F0 13 xx 70; take the next one or leave the loop *)
  assert (CONT : forall t0' : word, sys_hit bb i = false ->
    evt rsegs Q (MS (mkR ra' SPF gp tp t0' t1 t2 LEN BODY a0 a1 a2 a3 a4 a5 a6 a7
                         s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs))).
  { intros t0' SH. do 3 step. step.
    destruct (Nat.eq_dec (length bb) (i + 4)%nat) as [Hend|Hend]; [ubc_br false | ubc_br true].
    - assert (SA : system_at bb = false).
      { apply system_at_false. intros j Hj.
        destruct (Nat.eq_dec j i) as [->|Hne]; [exact SH | apply NOHIT; lia]. }
      step. eapply ubc_epi; try eassumption.
      rewrite (ubc_none bb BCF SA). reflexivity.
    - eapply (IH (S i) m mj cj pad); try eassumption; try lia; try ubc_val.
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact SH | apply NOHIT; lia]. }
  step. ubc_br false.
  do 2 step. step. ubc_br false.
  step. ubc_br false.
  do 2 step.
  destruct (Z.eqb_spec (at8 bb i) 240) as [H0|H0]; [ubc_br false | ubc_br true].
  2: { apply CONT. unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) H0). reflexivity. }
  step. step. ubc_br false.
  do 2 step.
  destruct (Z.eqb_spec (at8 bb (S i)) 19) as [H1|H1]; [ubc_br false | ubc_br true].
  2: { apply CONT. unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) H1).
       destruct (at8 bb i =? 240); reflexivity. }
  step. ubc_br false.
  do 2 step.
  destruct (Z.eqb_spec (at8 bb (S (S (S i)))) 112) as [H3|H3]; [ubc_br true | ubc_br false].
  - (* a whole F0 13 xx 70 at i *)
    assert (SH : sys_hit bb i = true) by (unfold sys_hit; rewrite H0, H1, H3; reflexivity).
    do 2 step.
    eapply ubc_epi; try eassumption.
    rewrite (ubc_hit bb i BCF ltac:(lia) SH). reflexivity.
  - apply CONT. unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) H3).
    destruct (at8 bb i =? 240), (at8 bb (S i) =? 19); reflexivity.
Qed.

(** ** The entry of the prefix scan, 0x13ea8 *)

Ltac ubc_rv :=
  rewrite ?w0_lit, ?v_sltu_b2z, ?v_sltiu_b2z;
  ubc_u; try (rewrite zb_lxor_ones by lia); ubc_u;
  decide_tests; cbn [Z.b2z]; fold_closed_in_goal; ubc_u; lia.

Lemma ubc_pre : forall m mj cj pad
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2' s3' s4' s5' s6' s7' : word),
  bc_loop (length bb) bb 0 0 = false ->
  bytes_at rsegs m body bb ->
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m (bv_unsigned sp + -144) [CB 40 mj] ->
  rw_cells rsegs m (bv_unsigned sp + -104) [CB 25 cj] ->
  rw_cells rsegs m (bv_unsigned sp + -79) (CB 7 pad :: ubc_svd) ->
  evt rsegs Q
    (MS (mkR ra' SPF gp tp t0 t1 t2 LEN BODY a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ea8) fc None m (seg_rom rsegs)).
Proof.
  intros m mj cj pad ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2' s3' s4' s5' s6' s7'
    BCF BB MU WM MI ST MSG CUR SV.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  do 2 step.
  destruct (lt_dec (length bb) 4%nat) as [Hs|Hs]; [ubc_br true | ubc_br false].
  - assert (SA : system_at bb = false)
      by (apply system_at_false; intros j Hj; exfalso; lia).
    step. eapply ubc_epi; try eassumption.
    rewrite (ubc_none bb BCF SA). reflexivity.
  - do 8 step.
    eapply (ubc_scan (length bb) 0 m mj cj pad); try eassumption.
    { lia. }
    { lia. }
    { intros j Hj. exfalso. lia. }
    all: ubc_rv.
Qed.

(** ** The cursor loop, 0x13e5c *)

(* the answer of the step, from its kind *)
Ltac ubc_kcode v :=
  lazymatch goal with
  | K : mr_kind ?r = _ |- _ =>
      let EC := fresh "EC" in
      assert (EC : mr_code r = v) by (unfold mr_code; rewrite K; reflexivity);
      rewrite EC; clear EC
  end.

(* a step that is not the end has moved the cursor, so pos was inside the body *)
Ltac ubc_plt K :=
  lazymatch type of K with
  | mr_kind (msg_step ?b ?p ?s) = _ =>
      let E := fresh "E" in
      assert (PLT : (p < length b)%nat) by
        (pose proof (is_end_msg_step b p s) as E; unfold is_end in E; rewrite K in E;
         apply (proj1 (Nat.leb_gt (length b) p)); symmetry; exact E)
  end.

(* forget the contents of the message / of the cursor *)
Ltac ubc_forget :=
  lazymatch goal with
  | H : rw_cells rsegs _ (bv_unsigned sp + -144) _ |- _ =>
      let j := fresh "mjF" in let H2 := fresh "MSGF" in
      destruct (rw_cells_forget rsegs _ _ _ H) as (j & H2);
      rewrite ?ubc_msg_cells_size in H2; cbn [cells_size csize Nat.add] in H2; clear H
  end.
Ltac ubc_forget_cur :=
  lazymatch goal with
  | H : rw_cells rsegs _ (bv_unsigned sp + -104) _ |- _ =>
      let j := fresh "cjF" in let H2 := fresh "CURF" in
      destruct (rw_cells_forget rsegs _ _ _ H) as (j & H2);
      cbn [cells_size csize cursor_cells Nat.add] in H2; clear H
  end.

(* a message that is not a refused sysex: take the next turn of the loop *)
Ltac ubc_again BK K :=
  step; ubc_br false; step; ubc_br true; ubc_forget;
  eapply BK; try eassumption; try lia;
  unfold refused; rewrite K; reflexivity.

Lemma ubc_loop : forall (n pos : nat) (st : Z) m mj pad
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2' s3' s4' s5' s6' s7' : word),
  (length bb - pos < n)%nat -> (pos <= length bb)%nat -> st_ok st ->
  bc_loop (length bb) bb 0 0 = bc_loop (length bb - pos) bb pos st ->
  bytes_at rsegs m body bb ->
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m (bv_unsigned sp + -144) [CB 40 mj] ->
  rw_cells rsegs m (bv_unsigned sp + -104) (cursor_cells body (Z.of_nat (length bb)) pos st) ->
  rw_cells rsegs m (bv_unsigned sp + -79) (CB 7 pad :: ubc_svd) ->
  bv_unsigned s2' = 1 -> bv_unsigned s3' = 240 -> bv_unsigned s4' = 3 ->
  bv_unsigned s5' = 19 -> bv_unsigned s6' = 2^64 - 2 -> bv_unsigned s7' = 112 ->
  evt rsegs Q
    (MS (mkR ra' SPF gp tp t0 t1 t2 LEN BODY a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e5c) fc None m (seg_rom rsegs)).
Proof.
  intros n. induction n as [|n IH]; intros pos st m mj pad ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s2' s3' s4' s5' s6' s7' Hn Hpos Hst BCI BB MU WM MI ST MSG CUR SV Hs2 Hs3 Hs4 Hs5 Hs6 Hs7; [lia|].
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply MN with (c := bv_unsigned sp + -104) (mp := bv_unsigned sp + -144) (body := body)
                       (bb := bb) (mj := mj) (pos := pos) (st := st)
      | post_call rsegs mm ] end.
  { lia. } { lia. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { lia. } { exact Hpos. } { exact Hst. } { exact CUR. } { exact BB. } { exact MSG. }
  { right; lia. } { lia. } { lia. } { assumption. }
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (msg_cells _ _ _) |- _ =>
    rename H into MSG1 end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -104) (cursor_cells _ _ _ _) |- _ =>
    rename H into CUR1 end.
  (* one more turn of the loop, after a message that is not refused *)
  assert (BACK : forall m' mj' (ra'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word),
    refused bb (msg_step bb pos st) = false -> (pos < length bb)%nat ->
    bytes_at rsegs m' body bb ->
    munch [(bv_unsigned sp + -144, bv_unsigned sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
    stk rsegs m' lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m' (bv_unsigned sp + -144) [CB 40 mj'] ->
    rw_cells rsegs m' (bv_unsigned sp + -104)
      (cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
         (mr_st (msg_step bb pos st))) ->
    rw_cells rsegs m' (bv_unsigned sp + -79) (CB 7 pad :: ubc_svd) ->
    evt rsegs Q (MS (mkR ra'' SPF gp tp t0' t1' t2' LEN BODY a0' a1' a2' a3' a4' a5' a6' a7'
                         s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4 t5 t6)
                    F (Z_to_bv 64 0x13e5c) fc None m' (seg_rom rsegs))).
  { intros m' mj' ra'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' Href Hlt
      BB' MU' WM' MI' ST' MSG' CUR' SV'.
    pose proof (msg_step_progress bb pos st Hlt) as PRG.
    eapply (IH (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)) m' mj' pad);
      try eassumption; try lia.
    - apply msg_step_st_ok; exact Hst.
    - rewrite BCI, (bc_loop_step (length bb - pos) bb pos st Hlt ltac:(lia)), Href. reflexivity. }
  destruct (mr_kind (msg_step bb pos st)) eqn:K.
  - (* MkEnd: the cursor is spent; the prefix scan decides *)
    ubc_kcode 0.
    assert (PE : (length bb <= pos)%nat).
    { pose proof (is_end_msg_step bb pos st) as E. unfold is_end in E. rewrite K in E.
      apply Nat.leb_le. symmetry. exact E. }
    replace (length bb - pos)%nat with 0%nat in BCI by lia. cbn [bc_loop] in BCI.
    step. ubc_br false.
    step. ubc_br false.
    step.
    ubc_forget. ubc_forget_cur.
    eapply ubc_pre; eassumption.
  - (* MkSysex *)
    ubc_kcode 1.
    ubc_plt K.
    destruct (msg_step_sysex bb pos st K) as (SX0 & SXi & SXl & SXp).
    pose proof (ubc_sysex_status bb pos st Hst K) as SST.
    assert (RF : refused bb (msg_step bb pos st) =
      ((3 <=? mr_sysex_len (msg_step bb pos st))%nat && (at8 bb (S pos) =? 19)
       && (at8 bb (S pos + 2) =? 112))%bool)
      by (unfold refused; rewrite K, SXi; reflexivity).
    rewrite (ubc_msg_sysex body mj (msg_step bb pos st) K), SST, SXi in MSG1.
    step. ubc_br true.
    step. step. ubc_br false.
    step.
    destruct (lt_dec (mr_sysex_len (msg_step bb pos st)) 3%nat) as [L3|L3].
    + step. ubc_br true. ubc_forget.
      eapply BACK; try eassumption; try lia.
      rewrite RF, (proj2 (Nat.leb_gt 3 (mr_sysex_len (msg_step bb pos st))) L3). reflexivity.
    + step. ubc_br false.
      step. step. ubc_br false.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ubc_rdb mm body bb (S pos) BB ltac:(lia)) as RS1;
        pose proof (ubc_rdb mm body bb (S pos + 2)%nat BB ltac:(lia)) as RS2
      end.
      step.
      destruct (Z.eqb_spec (at8 bb (S pos)) 19) as [H1|H1]; [step; ubc_br false | step; ubc_br true].
      2: { ubc_forget. eapply BACK; try eassumption; try lia.
           rewrite RF, andb_false_r. reflexivity. }
      step. ubc_br false.
      step.
      destruct (Z.eqb_spec (at8 bb (S pos + 2)) 112) as [H3|H3];
        [step; ubc_br false | step; ubc_br true].
      2: { ubc_forget. eapply BACK; try eassumption; try lia.
           rewrite RF, andb_false_r. reflexivity. }
      assert (BCT : bc_loop (length bb) bb 0 0 = true).
      { rewrite BCI, (bc_loop_step (length bb - pos) bb pos st PLT ltac:(lia)), RF.
        rewrite (proj2 (Nat.leb_le 3 (mr_sysex_len (msg_step bb pos st))) ltac:(lia)).
        reflexivity. }
      do 2 step. ubc_forget. ubc_forget_cur.
      eapply ubc_epi; try eassumption.
      rewrite (ubc_true bb BCT). reflexivity.
  - (* MkSysexCut *) ubc_kcode (-6). ubc_plt K. ubc_again BACK K.
  - (* MkBadStatus *) ubc_kcode (-8). ubc_plt K. ubc_again BACK K.
  - (* MkNoStatus *) ubc_kcode (-7). ubc_plt K. ubc_again BACK K.
  - (* MkChanShort *) ubc_kcode (-6). ubc_plt K. ubc_again BACK K.
  - (* MkChanCut *) ubc_kcode (-6). ubc_plt K. ubc_again BACK K.
  - (* MkChan: a channel message, its status is never F0 *)
    ubc_kcode 1. ubc_plt K.
    pose proof (ubc_chan_status bb pos st Hst K) as CST.
    rewrite (ubc_msg_chan body mj (msg_step bb pos st) K) in MSG1.
    step. ubc_br true.
    step. step. ubc_br true.
    ubc_forget.
    eapply BACK; try eassumption; try lia.
    unfold refused. rewrite K. reflexivity.
Qed.

(** ** The whole function, 0x13e04 *)

Lemma ubc_all : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m0 body bb -> stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 BODY LEN a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e04) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 BB ST MI.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  carve_frame 144%nat ST.
  do 15 step.
  lazymatch goal with H : rw_cells rsegs _ _ (CB 72 _ :: _) |- _ =>
    apply ubc_frame3 in H; destruct H as (MSG & CUR & SV) end.
  replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) in CUR by lia.
  replace (bv_unsigned sp + -144 + 65) with (bv_unsigned sp + -79) in SV by lia.
  step.
  (* The contract allows body = 2^64 (then bb is empty); the register holds body mod 2^64. *)
  rewrite <- (Z_to_bv_mod64 body).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
      [ eapply CI with (c := bv_unsigned sp + -104) (body := body mod 2^64) (len := Z.of_nat (length bb))
      | post_call rsegs mm ] end.
  { exact a2. }
  { lia. }
  { apply ubc_mod8; [exact SP8 | vm_compute; reflexivity]. }
  { apply Z.mod_pos_bound; lia. }
  { lia. }
  { exact CUR. }
  { assumption. }
  rewrite (Z_to_bv_mod64 body).
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -104) _ |- _ => rename H into CUR1 end.
  rewrite (ubc_cur0 body (Z.of_nat (length bb)) ltac:(lia) ltac:(lia) ltac:(lia)) in CUR1.
  do 6 step.
  destruct (rw_cells_forget rsegs _ _ _ MSG) as (mj1 & MSG1).
  cbn [cells_size csize Nat.add] in MSG1.
  eapply (ubc_loop (S (length bb)) 0%nat 0 _ mj1 _); try eassumption.
  { lia. }
  { lia. }
  { left; reflexivity. }
  { rewrite Nat.sub_0_r. reflexivity. }
  all: vm_compute; reflexivity.
Qed.

End Walk.

Theorem diginet_body_check_holds :
  diginet_cursor_init_contract -> diginet_msg_next_contract -> diginet_body_check_contract.
Proof.
  intros CI MN. unfold diginet_body_check_contract, DIGINET_BODY_CHECK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB0 BB SP8 ST LO0 LO DB MI.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  eapply ubc_all; try eassumption; try lia.
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST'.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exact ST'.
Qed.
