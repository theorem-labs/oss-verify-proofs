(* The walk of io_recv in the ubsan image, against U/Prog/T/io_recv_c.v. *)
(* io_recv (fuzz/fuzz_transport.c:906-929, the harness fix c47f6290 on 835f336c) at 0x14b20, 156 bytes: it saves
   ra, s0-s2 in a 32-byte frame, s2 = &g_fail_next, then
     g_rx_fail != 0: g_rx_fail = 0, return -EIO;
     g_rx == 0 or g_rx_times == 0: return 0;
     else g_rx_times--, n = min (g_rx_len, cap); n != 0: m_rx (g_rx, n); n == 0: m_tick ();
     g_rx read again; memcpy (buf, g_rx, n); return (int) n. The function has no UBSan check.
   The model's Some (io_recv_m, TModel/TCb.v) gives every branch; its g_fail_next is kept by
   TModel/TIoRecv.v io_recv_m_g_fail_next. The buffer [buf, buf + cap) is split at n for memcpy and joined
   again after it. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TWorldMem TSess0 TCb TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import m_rx_c m_tick_c io_recv_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- Z / bitvector bridges for the branches ---- *)

Lemma ir_s32_mod_inj : forall v w, -2^31 <= v < 2^31 -> -2^31 <= w < 2^31 -> v mod 2^64 = w mod 2^64 -> v = w.
Proof. intros v w Hv Hw H. Z.div_mod_to_equations. lia. Qed.

Lemma ir_eqb_s32 : forall v, -2^31 <= v < 2^31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intro E. apply N. apply (ir_s32_mod_inj v 0); [exact Hv | lia | exact E].
Qed.

Lemma ir_eqb_u64 : forall v, 0 <= v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ir_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ir_u8 : forall bs k, 0 <= u_at bs k 8 < 2^64.
Proof. intros bs k. pose proof (u_at_range bs k 8) as R. change (8 * Z.of_nat 8) with 64 in R. exact R. Qed.

(* ---- the world: g_rx and g_rx_len are not g_rx_times ---- *)

Lemma ir_rx_t : forall B t, Z.of_nat (length B) = W_LEN -> g_rx (set_g_rx_times B t) = g_rx B.
Proof.
  intros B t L. unfold g_rx, set_g_rx_times.
  apply u_at_upd_out; rewrite ?length_put; unfold OFF_g_rx, OFF_g_rx_times, W_LEN in *;
    cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

Lemma ir_len_t : forall B t, Z.of_nat (length B) = W_LEN -> g_rx_len (set_g_rx_times B t) = g_rx_len B.
Proof.
  intros B t L. unfold g_rx_len, set_g_rx_times.
  apply u_at_upd_out; rewrite ?length_put; unfold OFF_g_rx_len, OFF_g_rx_times, W_LEN in *;
    cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* ---- the heap frame ---- *)

Lemma ir_bat_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & Hb) Hk Hn.
  assert (LS : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

Lemma ir_bat_skipn : forall m X Y k, bytes_at rsegs m X Y -> (k <= length Y)%nat ->
  bytes_at rsegs m (X + Z.of_nat k) (skipn k Y).
Proof.
  intros m X Y k HB Hk. rewrite <- (firstn_skipn k Y) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite firstn_length_le in HB by exact Hk. exact HB.
Qed.

(* what frame_read read out of the frame block X / Y is in memory at the address it read from *)
Lemma ir_frame_read_at : forall m X Y p len db,
  bytes_at rsegs m X Y -> frame_read (Some (TFrame X Y)) p len = Some db -> 0 < len ->
  bytes_at rsegs m p db /\ length db = Z.to_nat len /\ X <= p /\ p + len <= X + Z.of_nat (length Y).
Proof.
  intros m X Y p len db HB HR Hl. unfold frame_read in HR. cbn [tf_addr tf_bytes] in HR.
  replace (len =? 0) with false in HR by (symmetry; apply Z.eqb_neq; lia).
  destruct ((p - X <? 0) || (len <? 0) || (Z.of_nat (length Y) <? p - X + len)) eqn:E; [discriminate HR|].
  injection HR as HR. subst db.
  apply orb_false_iff in E. destruct E as [E E3]. apply orb_false_iff in E. destruct E as [E1 E2].
  apply Z.ltb_ge in E1. apply Z.ltb_ge in E3.
  split; [|split; [apply length_sub; lia | lia]].
  replace p with (X + (p - X)) at 1 by lia. apply ir_bat_sub; [exact HB | lia | rewrite Z2Nat.id by lia; lia].
Qed.

Lemma ir_frame_from : forall X Y p fr, frame_from (Some (TFrame X Y)) p = Some fr ->
  fr = TFrame p (skipn (Z.to_nat (p - X)) Y) /\ X <= p <= X + Z.of_nat (length Y).
Proof.
  intros X Y p fr H. unfold frame_from in H. cbn [tf_addr tf_bytes] in H.
  destruct ((p - X <? 0) || (Z.of_nat (length Y) <? p - X)) eqn:E; [discriminate H|].
  injection H as H. subst fr. apply orb_false_iff in E. destruct E as [E1 E2].
  apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. split; [reflexivity | lia].
Qed.

(* m_rx's model is defined only when n stays inside its frame *)
Lemma ir_m_rx_len : forall I fr B n p, m_rx_m I (Some fr) B n = Some p -> 0 <= n <= Z.of_nat (length (tf_bytes fr)).
Proof.
  intros I fr B n p H. unfold m_rx_m in H. cbv beta iota zeta in H.
  destruct ((n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n)) eqn:E; [discriminate H|].
  apply orb_false_iff in E. destruct E as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. lia.
Qed.

(* m_rx's frame: the block from g_rx on *)
Lemma ir_tframe_rx : forall m sp X Y p, 0 < X -> bytes_at rsegs m X Y ->
  (X + Z.of_nat (length Y) <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= X) ->
  (X + Z.of_nat (length Y) <= bv_unsigned sp - m_rx_FRAME \/ bv_unsigned sp <= X) ->
  X <= p <= X + Z.of_nat (length Y) ->
  tframe_at m sp m_rx_FRAME (Some (TFrame p (skipn (Z.to_nat (p - X)) Y))).
Proof.
  intros m sp X Y p HX HB HW HS Hp. unfold tframe_at, off_world, off_window. cbn [tf_addr tf_bytes].
  rewrite length_skipn. split; [lia|]. split.
  - replace p with (X + Z.of_nat (Z.to_nat (p - X))) at 1 by lia. apply ir_bat_skipn; [exact HB | lia].
  - split; lia.
Qed.

(* ---- the buffer: one cell of cap bytes, split at n for memcpy and joined after it ---- *)

Lemma ir_cb_split : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k bs)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros m A n bs k [[Hwf HB] HW] Hk.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf, HB, HW.
  destruct Hwf as [Hl _]. rewrite app_nil_r in HB. rewrite Nat.add_0_r in HW.
  rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite firstn_length_le in HB2 by lia.
  destruct HW as (W1 & W2 & W3).
  split; split; [split | | split | ].
  - cbn [cells_wf cell_wf]. split; [apply firstn_length_le; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W3. lia.
Qed.

Lemma ir_cb_join : forall m A k j bs1 bs2, rw_cells rsegs m A [CB k bs1] ->
  rw_cells rsegs m (A + Z.of_nat k) [CB j bs2] -> rw_cells rsegs m A [CB (k + j) (bs1 ++ bs2)].
Proof.
  intros m A k j bs1 bs2 [[Hwf1 HB1] HW1] [[Hwf2 HB2] HW2].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf1, HB1, HW1, Hwf2, HB2, HW2.
  destruct Hwf1 as [L1 _]. destruct Hwf2 as [L2 _]. rewrite app_nil_r in HB1, HB2.
  rewrite Nat.add_0_r in HW1, HW2.
  destruct HW1 as (W1 & W2 & W3). destruct HW2 as (V1 & V2 & V3).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB1|]. rewrite L1. exact HB2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i (Z.of_nat k)) as [Lt|Ge]; [apply W3; lia|].
    replace (A + i) with (A + Z.of_nat k + (i - Z.of_nat k)) by lia. apply V3. lia.
Qed.

(* memcpy wrote the cell [p, p + n): the stack [lo, hi) keeps its bytes readable wherever p lies
   (as sc_stk_cell, Prog/T/send_control.v) *)
Lemma ir_stk_cell : forall m m' lo hi p n bs,
  stk rsegs m lo hi -> munch [(p, p + Z.of_nat n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' p [CB n bs] -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi p n bs (H1 & H2 & H) MU WMo [[Hwf (Hp & Hl & HB)] _].
  cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hl, HB. rewrite app_nil_r in Hl, HB.
  destruct Hwf as [Hlen _].
  split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv (b & Hb)]. split; [apply WMo; exact Hv|].
  destruct (Z_le_gt_dec p a) as [L1|L1]; [destruct (Z_lt_ge_dec a (p + Z.of_nat n)) as [L2|L2]|].
  - specialize (HB (Z.to_nat (a - p)) ltac:(lia)).
    replace (p + Z.of_nat (Z.to_nat (a - p))) with a in HB by lia.
    rewrite HB. destruct (nth_error bs (Z.to_nat (a - p))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma ir_firstn_app : forall (l1 l2 : list byte), firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity | f_equal; apply IH]. Qed.

(* ---- walk tactics ---- *)

(* 0x14ba4-0x14bb8: ld ra, s0-s2; the frame released; addi sp,sp,32; ret *)
Ltac ir_epi sp :=
  do 4 step;
  match goal with S : stk _ _ _ _, Fc : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame Fc S (bv_unsigned sp) end;
  do 2 step.

(* the callee's footprint and wmono about the memory of the goal: carry every fact across the call *)
Ltac ir_transport :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
    match goal with MUc : munch _ ?ma mb, WMc : wmono _ ?ma mb |- _ =>
      transport_after_call rsegs ma mb MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs ma |- _ => clear H end; try clear ma
    end
  end.

(* 0x14b94-0x14ba0, after m_rx or m_tick and the load of g_rx: memcpy (buf, sa, n) of the n bytes sb (SRCB, SRCL
   in the context), the buffer joined again, sext.w a0,s0 *)
Ltac ir_copy sp bp cap J n lo MC ST SRCB SRCL sb sa :=
  let BC1 := fresh "BC1" in let BC2 := fresh "BC2" in
  lazymatch goal with BCh : rw_cells rsegs _ bp [CB (Z.to_nat cap) J] |- _ =>
    destruct (ir_cb_split _ bp (Z.to_nat cap) J (Z.to_nat n) BCh ltac:(lia)) as [BC1 BC2]; clear BCh end;
  rewrite Z2Nat.id in BC2 by lia;
  do 2 step; step;
  eapply evt_cut;
  [ eapply MC with (src := sb) (junk := firstn (Z.to_nat n) J);
    [ rewrite (unsigned_lit sa) by lia; exact SRCB
    | rewrite (unsigned_lit n) by lia; exact SRCL
    | rewrite (unsigned_lit bp), (unsigned_lit n) by lia; exact BC1
    | rewrite (unsigned_lit bp), (unsigned_lit sa), (unsigned_lit n) by lia; lia
    | assumption ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; unfold memcpy_post in PO;
  let m3 := fresh "m" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let KC := fresh "KC" in
  let KB := fresh "KB" in let Eq := fresh "Eq" in let MI3 := fresh "MI" in let ST3 := fresh "ST" in
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & KC & KB);
  subst ms'; clear KB;
  rewrite (unsigned_lit bp), (unsigned_lit n) in MUc, KC by lia;
  replace (bp + n) with (bp + Z.of_nat (Z.to_nat n)) in MUc by lia;
  assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32))
    by (eapply ir_stk_cell; [exact ST | exact MUc | exact WMc | exact KC]);
  clear BC1 ST; ir_transport; rename ST3 into ST;
  let BCJ := fresh "BCJ" in
  pose proof (ir_cb_join _ bp (Z.to_nat n) (Z.to_nat cap - Z.to_nat n) sb (skipn (Z.to_nat n) J) KC
                ltac:(rewrite Z2Nat.id by lia; exact BC2)) as BCJ;
  replace (Z.to_nat n + (Z.to_nat cap - Z.to_nat n))%nat with (Z.to_nat cap) in BCJ by lia;
  clear KC BC2;
  rewrite (ret_pc_even 84896) by (first [lia | reflexivity]);
  step.

Theorem io_recv_holds : m_rx_contract -> m_tick_contract -> memcpy_contract -> io_recv_contract.
Proof.
  intros MRX MTK MC.
  unfold m_rx_contract, m_rx_ENTRY in MRX.
  unfold m_tick_contract, m_tick_ENTRY, m_tick_FRAME in MTK.
  unfold memcpy_contract in MC.
  unfold io_recv_contract, io_recv_ENTRY, io_recv_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bp cap r J got TF B B' HA1 HA2 Hcap BC BA BS TFA TOK WM GF HM SP16 ST LO WO MI.
  subst a1 a2.
  unfold w_off_stack in WO.
  wk_facts.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB0.
  assert (LB : Z.of_nat (length B) = W_LEN) by (rewrite LB0; apply Z2Nat.id; lia).
  pose proof (io_recv_m_g_fail_next _ _ _ _ _ _ _ LB0 HM) as GFK.
  unfold arg_blk, off_world, off_window in BA. destruct BA as (BA1 & BA2 & BA3 & BA4).
  (* the frame block X / Y of TF, or an empty block at buf when there is no frame *)
  assert (TFX : exists X Y, bytes_at rsegs m X Y /\
            (X + Z.of_nat (length Y) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= X) /\
            (X + Z.of_nat (length Y) <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= X) /\
            (bp + cap <= X \/ X + Z.of_nat (length Y) <= bp) /\ X + Z.of_nat (length Y) < 2^64 /\
            ((TF = Some (TFrame X Y) /\ 0 < X) \/ TF = None)).
  { destruct TF as [[X Y]|].
    - unfold tframe_at, off_world, off_window in TFA. cbn [tf_addr tf_bytes] in TFA.
      unfold io_recv_sep, blk_sep in BS. cbn [tf_addr tf_bytes] in BS.
      unfold tframe_ok in TOK. cbn [tf_addr tf_bytes] in TOK.
      destruct TFA as (T0 & T1 & T2 & T3). exists X, Y. split; [exact T1|]. split; [exact T3|].
      split; [exact T2|]. split; [exact BS|]. split; [exact TOK|]. left. split; [reflexivity | exact T0].
    - exists bp, []. split; [apply bytes_at_nil; lia|]. cbn [length Z.of_nat].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. reflexivity. }
  clear TFA TOK BS. destruct TFX as (X & Y & FB & FS & FW & FD & FOK & HTF).
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                          (bp, bp + cap)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.
  (* addi sp,sp,-32; sd ra,s0-s2; auipc a0; addi s2,a0,1428 (= &g_fail_next); lw a0,24(s2) = g_rx_fail *)
  do 7 step.
  step.
  change (s32_at B 64992) with (g_rx_fail B).
  (* beqz a0 *)
  step.
  rewrite ir_eqb_s32 by (apply s32_range).
  unfold io_recv_m, truth in HM.
  destruct (g_rx_fail B =? 0) eqn:EF; cbv iota; cbn [negb] in HM; cbv iota in HM.
  2: { (* g_rx_fail != 0: g_rx_fail = 0; li s0,-5; j; sext.w a0,s0 *)
       apply some_triple_inv in HM. destruct HM as (HB & Hr & Hg). subst B' r got.
       step. do 3 step.
       ir_epi sp.
       change (upd B 64992 (put 4 0)) with (set_g_rx_fail B 0) in *.
       apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [assumption|].
       split; [eassumption|]. split; [rewrite GFK; exact GF|]. split; [exact BC | reflexivity]. }
  (* g_rx_fail == 0: ld a0,40(s2) = g_rx; li s0,0; beqz a0 *)
  step. change (u_at B 65008 8) with (g_rx B).
  step. step.
  rewrite ir_eqb_u64 by (apply ir_u8).
  destruct (g_rx B =? 0) eqn:ER; cbv iota.
  1: { (* g_rx == 0: return 0 *)
       try rewrite ER in HM. cbn [orb] in HM. apply some_triple_inv in HM. destruct HM as (HB & Hr & Hg). subst B' r got.
       step. ir_epi sp.
       apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [assumption|].
       split; [eassumption|]. split; [exact GF|]. split; [exact BC | reflexivity]. }
  (* mv s1,a1; lw a1,28(s2) = g_rx_times; beqz a1 *)
  step. step. change (s32_at B 64996) with (g_rx_times B).
  step.
  rewrite ir_eqb_s32 by (apply s32_range).
  destruct (g_rx_times B =? 0) eqn:ET; cbv iota.
  1: { (* g_rx_times == 0: return 0 *)
       try rewrite ER, ET in HM. cbn [orb] in HM. apply some_triple_inv in HM. destruct HM as (HB & Hr & Hg). subst B' r got.
       step. ir_epi sp.
       apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [assumption|].
       split; [eassumption|]. split; [exact GF|]. split; [exact BC | reflexivity]. }
  try rewrite ER, ET in HM. cbn [orb] in HM.
  (* ld s0,48(s2) = g_rx_len; addi a1,a1,-1; sw a1,28(s2) *)
  step. change (u_at B 65016 8) with (g_rx_len B).
  step. step.
  (* the model: g_rx_times - 1 does not overflow; n = min (g_rx_len, cap) on the world after the store *)
  destruct (int_dec (g_rx_times B)) as [t|] eqn:EID; [|discriminate HM].
  assert (Ht : t = g_rx_times B - 1)
    by (unfold int_dec in EID; destruct (g_rx_times B =? INT_MIN); [discriminate EID | injection EID as EID; lia]).
  subst t. cbv beta iota zeta in HM.
  change (upd B 64996 (put 4 (g_rx_times B + -1))) with (set_g_rx_times B (g_rx_times B - 1)) in WMw.
  rewrite (ir_len_t B (g_rx_times B - 1) LB) in HM.
  pose proof (ir_rx_t B (g_rx_times B - 1) LB) as RX1.
  pose proof (ir_u8 B OFF_g_rx_len) as RL. change (u_at B OFF_g_rx_len 8) with (g_rx_len B) in RL.
  revert HM. remember (if g_rx_len B <? cap then g_rx_len B else cap) as n eqn:En. intros HM.
  assert (Hn : 0 <= n <= cap) by (subst n; destruct (g_rx_len B <? cap) eqn:E; [apply Z.ltb_lt in E | ]; lia).
  (* bltu s0,a2: n is g_rx_len (taken) or cap (mv s0,a2) *)
  step.
  rewrite ir_ltu by lia.
  destruct (g_rx_len B <? cap) eqn:EL; cbv iota.
  1: assert (En' : n = g_rx_len B) by (rewrite En; try rewrite EL; reflexivity).
  2: assert (En' : n = cap) by (rewrite En; try rewrite EL; reflexivity).
  2: step.
  all: rewrite <- En'.
  (* beqz s0 *)
  all: step.
  all: rewrite ir_eqb_u64 by lia.
  all: destruct (n =? 0) eqn:EN; cbv iota; try rewrite EN in HM; cbv iota in HM.
  all: lazymatch type of EN with
  | (_ =? 0) = true =>
     (* n == 0: jal m_tick; ld a1 = g_rx; memcpy (buf, g_rx, 0) *)
     apply Z.eqb_eq in EN;
     destruct (m_tick_m (set_g_rx_times B (g_rx_times B - 1))) as [[B2 []]|] eqn:ETK; [|discriminate HM];
     cbv beta iota in HM;
     replace (frame_read TF (g_rx B2) n) with (Some (@nil byte)) in HM by (rewrite EN; reflexivity);
     cbv beta iota in HM;
     apply some_triple_inv in HM; destruct HM as (HB & Hr & Hg); subst B' r got;
     step;
     eapply evt_cut;
     [ eapply MTK with (lo := lo) (B := set_g_rx_times B (g_rx_times B - 1)) (B' := B2);
       [ rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
       | unfold w_off_stack; rewrite Hsp; lia | assumption | exact WMw | exact ETK ]
     | ];
     intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m2 &
                 Eq & MUc & WMc & MI2 & ST2 & WM2);
     subst ms'; rewrite Hsp in MUc, ST2; clear WMw ST; ir_transport; rename ST2 into ST; rename WM2 into WMw;
     rewrite (ret_pc_even 84880) by (first [lia | reflexivity]);
     step; change (u_at B2 65008 8) with (g_rx B2);
     pose proof (ir_u8 B2 OFF_g_rx) as RSA; change (u_at B2 OFF_g_rx 8) with (g_rx B2) in RSA;
     lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (SRCB : bytes_at rsegs mm (g_rx B2) []) by (apply bytes_at_nil; lia) end;
     assert (SRCL : length (@nil byte) = Z.to_nat n) by (rewrite EN; reflexivity);
     ir_copy sp bp cap J n lo MC ST SRCB SRCL (@nil byte) (g_rx B2);
     rewrite (unsigned_lit n) by lia; rewrite Z.add_0_r;
     ir_epi sp;
     apply evt_done; unfold QQ; do 16 eexists; split; [reflexivity|];
     split; [exact MU|]; split; [exact WMO|]; split; [assumption|]; split; [assumption|];
     split; [exact WMw|]; split; [rewrite GFK; exact GF|]; split; [exact BCJ|];
     destruct (0 <? bv_swrap 32 n); reflexivity
  | (_ =? 0) = false =>
     (* n != 0: mv a1,s0; jal m_rx (g_rx, n); j; ld a1 = g_rx; memcpy (buf, g_rx, n) *)
     apply Z.eqb_neq in EN;
     destruct (m_rx_m timg_ubsan (frame_from TF (g_rx (set_g_rx_times B (g_rx_times B - 1))))
                 (set_g_rx_times B (g_rx_times B - 1)) n) as [[B2 x]|] eqn:ERX; [|discriminate HM];
     cbv beta iota in HM;
     destruct (frame_read TF (g_rx B2) n) as [bytes|] eqn:EFR; [|discriminate HM];
     apply some_triple_inv in HM; destruct HM as (HB & Hr & Hg); subst B' r got;
     rewrite RX1 in ERX;
     destruct HTF as [[HTF HX] | HTF]; subst TF;
     [ | exfalso; cbv beta iota delta [frame_from m_rx_m] in ERX; discriminate ERX ];
     destruct (frame_from (Some (TFrame X Y)) (g_rx B)) as [fr|] eqn:EFF;
       [ | exfalso; cbv beta iota delta [m_rx_m] in ERX; discriminate ERX ];
     apply ir_frame_from in EFF; destruct EFF as [EFF HP]; subst fr;
     pose proof (ir_m_rx_len _ _ _ _ _ ERX) as NL; cbn [tf_bytes] in NL; rewrite length_skipn in NL;
     do 2 step;
     eapply evt_cut;
     [ eapply MRX with (lo := lo) (B := set_g_rx_times B (g_rx_times B - 1)) (B' := B2)
           (fr := TFrame (g_rx B) (skipn (Z.to_nat (g_rx B - X)) Y)) (n := n) (r := x);
       lazymatch goal with
       | |- _ = Z_to_bv 64 _ => reflexivity
       | |- tframe_at _ _ _ _ =>
           apply ir_tframe_rx; [exact HX | exact FB | exact FW | unfold m_rx_FRAME; rewrite Hsp; lia | exact HP]
       | |- mem_inv _ _ => assumption
       | |- m_rx_m _ _ _ _ = _ => exact ERX
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- rw_cells _ _ _ _ => exact WMw
       | |- w_off_stack _ _ _ => unfold w_off_stack, m_rx_FRAME; rewrite Hsp; lia
       | |- _ mod 16 = 0 => rewrite Hsp; Z.div_mod_to_equations; lia
       | |- _ + m_rx_FRAME <= _ => unfold m_rx_FRAME; rewrite Hsp; lia
       | |- _ => cbn [tf_addr]; lia
       end
     | ];
     intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m2 &
                 Eq & MUc & WMc & MI2 & ST2 & WM2);
     subst ms'; rewrite Hsp in MUc, ST2; unfold m_rx_FRAME in MUc; clear WMw ST; ir_transport;
     rename ST2 into ST; rename WM2 into WMw;
     rewrite (ret_pc_even 84872) by (first [lia | reflexivity]);
     step;
     step; change (u_at B2 65008 8) with (g_rx B2);
     lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       destruct (ir_frame_read_at mm X Y (g_rx B2) n bytes FB EFR ltac:(lia)) as (SRCB & SRCL & SR1 & SR2) end;
     pose proof (ir_u8 B2 OFF_g_rx) as RSA; change (u_at B2 OFF_g_rx 8) with (g_rx B2) in RSA;
     ir_copy sp bp cap J n lo MC ST SRCB SRCL bytes (g_rx B2);
     rewrite (unsigned_lit n) by lia; rewrite Z.add_0_r;
     ir_epi sp;
     apply evt_done; unfold QQ; do 16 eexists; split; [reflexivity|];
     split; [exact MU|]; split; [exact WMO|]; split; [assumption|]; split; [assumption|];
     split; [exact WMw|]; split; [rewrite GFK; exact GF|]; split; [exact BCJ|];
     destruct (0 <? bv_swrap 32 n); [apply ir_firstn_app | reflexivity]
  end.
Qed.
