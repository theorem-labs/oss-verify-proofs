(* diginet_session_submit (transport/src/diginet_session.c:328-349) in the plain image, entry 0x16fb4: the walk of its
   machine contract (Prog/T/diginet_session_submit_c.v) from the contracts of diginet_body_check
   (Prog/diginet_body_check_c.v) and memcpy (Prog/memcpy_c.v). The binary inlines coalescable (:322-326). Each exit is
   stated once and proved once: the epilogue EPI (0x170b4), the append APP (0x17070) and its full-queue test AT60
   (0x17060), the coalescing COAL (0x17098); the search loop at 0x1704c (LOOP) by induction on the turns left. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memcpy_c diginet_body_check_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import diginet_session_submit_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the machine's tests as the model's ---- *)

Lemma sub_eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* lw sign-extends both keys; equal words are equal uint32_t *)
Lemma sub_eqb_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

(* :330 `!c->len || c->len > DIGINET_CMD_MAX_LEN` as the one unsigned test (len - 25) < -24 *)
Lemma sub_len_ltu : forall len, 0 <= len < 256 ->
  bv_ltu (Z_to_bv 64 (len + -25)) (Z_to_bv 64 (-24)) = (len =? 0) || (24 <? len).
Proof.
  intros len H. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec len 0); destruct (Z.ltb_spec 24 len); cbn [orb];
    first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* the inlined coalescable (:322-326): the binary tests key & 0xf70000 (kind 0 or 8) and key & 0xff0000 = 0x90000
   (kind 9) *)
Lemma sub_land_shl16 : forall key M, 0 <= M ->
  Z.land key (Z.shiftl M 16) = Z.shiftl (Z.land (Z.shiftr key 16) M) 16.
Proof.
  intros key M HM. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 16) as [L|L].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (n - 16 + 16) with n by lia. reflexivity.
Qed.

Lemma sub_u8_lt : forall x, 0 <= u8 x < 256.
Proof. intros. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma sub_z256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall k, 0 <= k < 256 -> P k = true.
Proof.
  intros P H k Hk. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat k).
  split; [lia | apply in_seq; lia].
Qed.

Lemma sub_k8 : forall k, 0 <= k < 256 ->
  0 <= Z.land k 247 < 256 /\
  (int_of_bool (negb (k =? 0) && negb (k =? DIGINET_KEY_INPUT) && negb (k =? DIGINET_KEY_KEEPALIVE)) =? 0)
    = (Z.land k 247 =? 0) || (k =? 9).
Proof.
  intros k Hk.
  pose proof (sub_z256 (fun j => (0 <=? Z.land j 247) && (Z.land j 247 <? 256) &&
     Bool.eqb (int_of_bool (negb (j =? 0) && negb (j =? DIGINET_KEY_INPUT) && negb (j =? DIGINET_KEY_KEEPALIVE)) =? 0)
              ((Z.land j 247 =? 0) || (j =? 9))) ltac:(vm_compute; reflexivity) k Hk) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply andb_prop in H1. destruct H1 as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Bool.eqb_prop in H2. split; [lia | exact H2].
Qed.

Lemma sub_coal_eq : forall key,
  (coalescable_m key =? 0) = (Z.land (u8 (Z.shiftr key 16)) 247 =? 0) || (u8 (Z.shiftr key 16) =? 9).
Proof. intros key. unfold coalescable_m. cbv zeta. exact (proj2 (sub_k8 _ (sub_u8_lt _))). Qed.

Lemma sub_coal1 : forall key, 0 <= key ->
  bv_eqb (Z_to_bv 64 (Z.land key 16187392)) (Z_to_bv 64 0) = (Z.land (u8 (Z.shiftr key 16)) 247 =? 0).
Proof.
  intros key Hk.
  change 16187392 with (Z.shiftl 247 16). rewrite sub_land_shl16 by lia.
  replace (Z.land (Z.shiftr key 16) 247) with (Z.land (u8 (Z.shiftr key 16)) 247).
  2:{ unfold u8. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. }
  pose proof (sub_u8_lt (Z.shiftr key 16)) as U. destruct (sub_k8 _ U) as [L _].
  rewrite Z.shiftl_mul_pow2 by lia. rewrite sub_eqb_u by lia.
  destruct (Z.eqb_spec (Z.land (u8 (Z.shiftr key 16)) 247 * 2 ^ 16) 0);
    destruct (Z.eqb_spec (Z.land (u8 (Z.shiftr key 16)) 247) 0); try reflexivity; exfalso; lia.
Qed.

Lemma sub_coal2 : forall key, 0 <= key ->
  bv_eqb (Z_to_bv 64 (Z.land key 16711680)) (Z_to_bv 64 589824) = (u8 (Z.shiftr key 16) =? 9).
Proof.
  intros key Hk.
  change 16711680 with (Z.shiftl 255 16). rewrite sub_land_shl16 by lia.
  replace (Z.land (Z.shiftr key 16) 255) with (u8 (Z.shiftr key 16)).
  2:{ unfold u8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  pose proof (sub_u8_lt (Z.shiftr key 16)) as U.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite sub_eqb_u by lia.
  destruct (Z.eqb_spec (u8 (Z.shiftr key 16) * 2 ^ 16) 589824);
    destruct (Z.eqb_spec (u8 (Z.shiftr key 16)) 9); try reflexivity; exfalso; lia.
Qed.

(* ---- the model ---- *)

(* diginet_session_submit_m with its tail (the queue part, :336-348) named: sub_k takes the result of the search *)
Definition sub_k (B C : list byte) (o : option (option Z)) : option (list byte * Z) :=
  match o with
  | None => None
  | Some (Some i) =>
      let B1 := upd B (A_S_queue_bytes i) C in
      Some (set_S_stats_coalesced B1 (u64 (S_stats_coalesced B1 + 1)), DIGINET_OK)
  | Some None =>
      let q := S_queued B in
      if q =? DIGINET_QUEUE_MAX then Some (B, DIGINET_E_SPACE)
      else if S_queue_N <=? q then None
      else Some (set_S_queued (upd B (A_S_queue_bytes q) C) (u32 (q + 1)), DIGINET_OK)
  end.

Lemma sub_m_eq : forall B C, diginet_session_submit_m B C =
  if (cmd_len_of C =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of C) then Some (B, DIGINET_E_ARG)
  else if negb (body_check (firstn (Z.to_nat (cmd_len_of C)) C) =? DIGINET_OK) then
    Some (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED)
  else sub_k B C (if coalescable_m (cmd_key_of C) =? 0 then Some None
                  else submit_find_m B (cmd_key_of C) 0 (Z.to_nat (S_queued B))).
Proof. reflexivity. Qed.

Lemma sub_find_S : forall B key i f, submit_find_m B key i (S f) =
  if 512 <=? i then None else if S_queue_key B i =? key then Some (Some i) else submit_find_m B key (i + 1) f.
Proof. reflexivity. Qed.

Lemma sub_k_none : forall B C B' r, sub_k B C (Some None) = Some (B', r) ->
  (S_queued B = 512 /\ B' = B /\ r = DIGINET_E_SPACE) \/
  (S_queued B < 512 /\ B' = set_S_queued (upd B (A_S_queue_bytes (S_queued B)) C) (u32 (S_queued B + 1)) /\
   r = DIGINET_OK).
Proof.
  intros B C B' r H. unfold sub_k in H. cbv zeta in H. unfold DIGINET_QUEUE_MAX, S_queue_N in H. revert H.
  destruct (Z.eqb_spec (S_queued B) 512) as [E|E]; intros H.
  - injection H as <- <-. left. auto.
  - revert H. destruct (Z.leb_spec 512 (S_queued B)) as [L|L]; intros H; [discriminate H|].
    injection H as <- <-. right. split; [lia|]. auto.
Qed.

Lemma sub_k_some : forall B C i B' r, sub_k B C (Some (Some i)) = Some (B', r) ->
  B' = set_S_stats_coalesced (upd B (A_S_queue_bytes i) C) (u64 (S_stats_coalesced (upd B (A_S_queue_bytes i) C) + 1))
  /\ r = DIGINET_OK.
Proof. intros B C i B' r H. unfold sub_k in H. cbv zeta in H. injection H as <- <-. auto. Qed.

(* the world after the stores of :333, :340, :347-348 is the model's *)
Lemma sub_refused_eq : forall B1,
  upd B1 19904 (put 8 (u_at B1 19904 8 + 1)) = set_S_stats_refused B1 (u64 (S_stats_refused B1 + 1)).
Proof.
  intros. unfold set_S_stats_refused, S_stats_refused, A_S_stats_refused, u64. rewrite put_mod64 by lia.
  reflexivity.
Qed.

Lemma sub_coal_w : forall B1,
  upd B1 19896 (put 8 (u_at B1 19896 8 + 1)) = set_S_stats_coalesced B1 (u64 (S_stats_coalesced B1 + 1)).
Proof.
  intros. unfold set_S_stats_coalesced, S_stats_coalesced, A_S_stats_coalesced, u64. rewrite put_mod64 by lia.
  reflexivity.
Qed.

Lemma sub_app_eq : forall B C q, length B = Z.to_nat W_LEN -> length C = 32%nat -> 0 <= q < 512 ->
  upd (upd B 19792 (put 4 (q + 1))) (A_S_queue_bytes q) C = set_S_queued (upd B (A_S_queue_bytes q) C) (u32 (q + 1)).
Proof.
  intros B C q LB LC Hq. unfold set_S_queued, u32.
  replace (put 4 ((q + 1) mod 2 ^ 32)) with (put 4 (q + 1)) by (unfold put; symmetry; apply Z_to_le_bytes_mod; lia).
  change A_S_queued with 19792.
  apply upd_upd_comm; rewrite ?length_put, ?LC, ?LB; unfold A_S_queue_bytes, OFF_g_s, W_LEN; lia.
Qed.

(* The stack of the frame is still a stack after a callee filled the cell [X, X + n) (memcpy's post), wherever that
   cell lies against the stack's range: inside the cell the post's cell gives the bytes, outside it the footprint. *)
Lemma sub_stk_fill : forall m m' lo hi X n cs,
  stk rsegs m lo hi -> munch [(X, X + n)] m m' -> wmono rsegs m m' -> rw_cells rsegs m' X cs ->
  n = Z.of_nat (cells_size cs) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi X n cs (H1 & H2 & H) MU WMo D En. subst n.
  pose proof (stk_of_rw_cells rsegs m' X cs D) as (_ & _ & SD).
  split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Wv [b Hb]].
  destruct (Z_lt_le_dec a X) as [L|L]; [|destruct (Z_lt_le_dec a (X + Z.of_nat (cells_size cs))) as [L2|L2]].
  - split; [apply WMo, Wv|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
  - apply SD. lia.
  - split; [apply WMo, Wv|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

(* ---- tactics ---- *)

Ltac sub_lia := unfold W_LEN in *; lia.
Ltac sub_solve_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  rewrite ?unsigned_lit by sub_lia;
  first [ reflexivity
        | apply Z.eqb_neq; sub_lia | apply Z.eqb_eq; sub_lia
        | apply Z.ltb_ge; sub_lia | apply Z.ltb_lt; sub_lia
        | apply negb_false_iff, Z.eqb_eq; sub_lia | apply negb_true_iff, Z.eqb_neq; sub_lia
        | apply negb_false_iff, Z.ltb_lt; sub_lia | apply negb_true_iff, Z.ltb_ge; sub_lia ].
Ltac bfalse :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false by (symmetry; first [solve_cond | sub_solve_cond]); cbv iota end.
Ltac btrue :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true by (symmetry; first [solve_cond | sub_solve_cond]); cbv iota end.

(* memcpy (s->queue[i], c, 32) from the frame of submit. HU0 / HU1 / HU2 read a0 / a1 / a2 back; the destination is
   the world piece at W_BASE_PLAIN + A_S_queue_bytes i (wm_piece). After the call: the kit's wk_post_call, with the
   frame's stack STh carried across the copy by sub_stk_fill first (the stack's range is not known to miss the world),
   then the copied bytes folded into the world (wk_world_after_call) and the rest transported. *)
Ltac sub_memcpy MC WMh CBh LCh MIh HU0 HU1 HU2 STh :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply MC;
    [ rewrite HU1; exact CBh
    | rewrite HU2, LCh; reflexivity
    | rewrite HU0, HU2; eapply (wm_piece rsegs _ _ _ _ 32 _ WMh); [reflexivity | lia | lia | sub_lia]
    | rewrite HU0, HU1, HU2; sub_lia
    | exact MIh ]
  | unfold memcpy_post;
    let ms' := fresh "ms'" in let PO := fresh "PO" in let m4 := fresh "m" in
    let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in let Dc := fresh "D" in
    let Ec := fresh "Eq" in let CBc := fresh "CBp" in let STc := fresh "ST" in
    intros ms' PO; rewrite HU0, HU1, HU2 in PO;
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Ec & MUc & WMc & MIc & Dc & CBc);
    subst ms';
    pose proof (sub_stk_fill _ _ _ _ _ _ _ STh MUc WMc Dc eq_refl) as STc; clear STh;
    wk_facts; wk_world_after_call rsegs mm m4; transport_after_call rsegs mm m4 MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm;
    try (lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end) ]
  end.

Theorem diginet_session_submit_holds : diginet_body_check_contract -> memcpy_contract ->
  diginet_session_submit_contract.
Proof.
  intros BC MC.
  unfold diginet_body_check_contract, DIGINET_BODY_CHECK in BC.
  unfold memcpy_contract in MC.
  unfold diginet_session_submit_contract, diginet_session_submit_ENTRY, diginet_session_submit_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo cp r C B B' A0 A1 CBy LC AB CM WM HM SP16 ST LO WO MI.
  subst a0 a1.
  destruct AB as (CP0 & CPE & OW & OWIN). unfold off_world in OW. unfold off_window in OWIN.
  unfold w_off_stack in WO.
  wk_facts.
  assert (EOFF : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as LB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HU1 : bv_unsigned (Z_to_bv 64 cp) = cp) by (apply unsigned_lit; lia).
  assert (HU2 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  assert (LR : 0 <= cmd_len_of C < 256).
  { pose proof (u_at_range C 24 1) as R. unfold cmd_len_of. change (2 ^ (8 * Z.of_nat 1)) with 256 in R. lia. }
  rewrite sub_m_eq in HM. change DIGINET_CMD_MAX_LEN with 24 in HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.
  (* prologue: addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); sd s2,0(sp) *)
  do 5 step.
  rename m into mI. rename MU into MU0. rename WMO into WM0.
  lazymatch goal with HF : rw_cells _ ?mm (bv_unsigned sp + -32) ?cs |- _ =>
    rename mm into m1; rename HF into FR; set (FRC := cs) in FR end.
  (* the common epilogue at 0x170b4: ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); ld s2,0(sp); addi sp,sp,32; ret *)
  assert (EPI : forall (mm : word -> option byte)
                       (xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word),
    rw_cells rsegs mm (bv_unsigned sp + -32) FRC ->
    stk rsegs mm lo (bv_unsigned sp + -32) ->
    munch [(bv_unsigned sp - 176, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI mm ->
    wmono rsegs mI mm -> mem_inv rsegs mm -> wmem rsegs mm B' ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 r)
                          xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x170b4) fc None mm (seg_rom rsegs))).
  { intros mm xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 FR2 ST2 MU2 WM2 MI2 WW2.
    unfold FRC in FR2.
    do 4 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2 | exact WW2]. }
  (* mv s1,a0; li a0,-1; beqz s1: s is not NULL *)
  do 3 step. bfalse.
  (* mv s0,a1; beqz a1: c is not NULL *)
  do 2 step. bfalse.
  (* lbu a1,24(s0): c->len *)
  assert (R24 : ov_read_bytes rsegs m1 (Z_to_bv 64 (cp + 24)) 1 = Some (sub C 24 1))
    by exact (bytes_at_read rsegs m1 cp C 24 1 CBy ltac:(lia) ltac:(rewrite LC; lia)).
  step. rewrite ?wm_lbu. change (u_at C 24 1) with (cmd_len_of C). clear R24.
  (* addi a2,a1,-25; li a3,-24; bltu a2,a3: c->len is 0 or above 24 (:330-331) *)
  do 3 step.
  rewrite sub_len_ltu by exact LR.
  destruct ((cmd_len_of C =? 0) || (24 <? cmd_len_of C)) eqn:LV; try rewrite LV in HM; cbv iota in HM |- *.
  { injection HM as <- <-. eapply EPI; eassumption. }
  apply orb_false_iff in LV. destruct LV as [LV1 LV2]. apply Z.eqb_neq in LV1. apply Z.ltb_ge in LV2.
  (* lui a0,4; addiw s2,a0,1760; add s2,s1,s2; mv a0,s0; jal diginet_body_check (c->bytes, c->len) *)
  do 5 step.
  set (bb := firstn (Z.to_nat (cmd_len_of C)) C) in HM |- *.
  assert (LBB : length bb = Z.to_nat (cmd_len_of C)) by (unfold bb; rewrite length_firstn; lia).
  assert (BBy : bytes_at rsegs m1 cp bb).
  { unfold bb. pose proof CBy as H. rewrite <- (firstn_skipn (Z.to_nat (cmd_len_of C)) C) in H.
    apply bytes_at_app in H. exact (proj1 H). }
  replace (Z_to_bv 64 (cmd_len_of C)) with (Z_to_bv 64 (Z.of_nat (length bb))) by (rewrite LBB; f_equal; lia).
  eapply evt_cut.
  { eapply BC; [ lia | exact BBy | rewrite Hsp; exact ST | rewrite Hsp; lia | rewrite Hsp, LBB; lia | exact MI ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2).
  subst ms'. rewrite Hsp in MUc, ST2.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. try clear m1. clear BBy.
  rewrite (ret_pc_even 0x17000) by (first [lia | reflexivity]).
  (* beqz a0: diginet_body_check answered 0 *)
  destruct (system_at bb) eqn:SA.
  { (* refused (:333-334): ld a0,112(s2); addi a0,a0,1; sd a0,112(s2); li a0,-10; j 0x170b4 *)
    assert (BCV : body_check bb = -10) by (rewrite body_check_spec, SA; reflexivity).
    rewrite BCV in HM |- *. change (negb (-10 =? DIGINET_OK)) with true in HM. cbv iota in HM.
    injection HM as <- <-.
    step. bfalse.
    do 5 step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN [CB _ _] |- _ => rewrite sub_refused_eq in H end.
    eapply EPI; eassumption. }
  assert (BCV : body_check bb = 0) by (rewrite body_check_spec, SA; reflexivity).
  rewrite BCV in HM |- *. change (negb (0 =? DIGINET_OK)) with false in HM. cbv iota in HM.
  step. btrue.
  (* lwu a2,28(s0): c->key; lwu a1,0(s2): s->queued *)
  assert (R28 : ov_read_bytes rsegs m2 (Z_to_bv 64 (cp + 28)) 4 = Some (sub C 28 4))
    by exact (bytes_at_read rsegs m2 cp C 28 4 CBy ltac:(lia) ltac:(rewrite LC; lia)).
  step. rewrite ?wm_lwu. change (u_at C 28 4) with (cmd_key_of C). clear R28.
  step. change (u_at B 19792 4) with (S_queued B).
  set (key := cmd_key_of C) in *. set (q := S_queued B) in *.
  assert (KR : 0 <= key < 2^32).
  { pose proof (u_at_range C 28 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R. exact R. }
  assert (QR : 0 <= q < 2^32).
  { pose proof (u_at_range B A_S_queued 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R. exact R. }
  (* 0x17070, the append (:347-348): slli a0,a1,5; addi a1,a1,1; add a0,s1,a0; sw a1,0(s2); addi a0,a0,1760;
     li a2,32; mv a1,s0; jal memcpy; li a0,0; j 0x170b4 *)
  assert (APP : forall (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    q < 512 -> B' = set_S_queued (upd B (A_S_queue_bytes q) C) (u32 (q + 1)) -> r = DIGINET_OK ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 cp)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xa0 (Z_to_bv 64 q) xa2 xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x17070) fc None m2 (seg_rom rsegs))).
  { intros xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hq -> ->.
    assert (EK : A_S_queue_bytes q = 3408 + 32 * q) by (unfold A_S_queue_bytes; lia).
    do 8 step.
    (* a0 = &s->queue[s->queued] *)
    lazymatch goal with |- context [Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + ?e + 1760)] =>
      assert (HU0 : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + e + 1760)) = W_BASE_PLAIN + A_S_queue_bytes q)
        by (rewrite ?(unsigned_lit q) by lia; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by sub_lia; lia)
    end.
    lazymatch goal with WH : rw_cells _ ?mm W_BASE_PLAIN [CB _ _], CB3 : bytes_at _ ?mm cp C, M3 : mem_inv _ ?mm
                        |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      sub_memcpy MC WH CB3 LC M3 HU0 HU1 HU2 ST2 end.
    do 2 step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN [CB _ _] |- _ => rewrite sub_app_eq in H by (auto; lia) end.
    eapply EPI; eassumption. }
  (* 0x17060, after the search found no entry (:345-347): li a0,512; bne a1,a0; li a0,-5; j 0x170b4 *)
  assert (AT60 : forall (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    sub_k B C (Some None) = Some (B', r) ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 cp)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xa0 (Z_to_bv 64 q) xa2 xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x17060) fc None m2 (seg_rom rsegs))).
  { intros xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    apply sub_k_none in HK. change (S_queued B) with q in HK.
    do 2 step.
    rewrite sub_eqb_u by lia.
    destruct HK as [(Q5 & -> & ->) | (Hq & HB & Hr)].
    - rewrite Q5. bfalse. do 2 step. eapply EPI; eassumption.
    - btrue. eapply APP; [exact Hq | exact HB | exact Hr]. }
  (* 0x17098, the entry s->queue[i] with the same key (:339-341): li a2,32; mv a1,s0; jal memcpy; li a0,0;
     ld a1,104(s2); addi a1,a1,1; sd a1,104(s2) *)
  assert (COAL : forall (i : Z) (xa0 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    0 <= i < 512 -> bv_unsigned xa0 = W_BASE_PLAIN + A_S_queue_bytes i ->
    B' = set_S_stats_coalesced (upd B (A_S_queue_bytes i) C)
           (u64 (S_stats_coalesced (upd B (A_S_queue_bytes i) C) + 1)) -> r = DIGINET_OK ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 cp)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x17098) fc None m2 (seg_rom rsegs))).
  { intros i xa0 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hi H0 -> ->.
    assert (EK : A_S_queue_bytes i = 3408 + 32 * i) by (unfold A_S_queue_bytes; lia).
    do 3 step.
    sub_memcpy MC WM CBy LC MI2 H0 HU1 HU2 ST2.
    do 4 step.
    lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN [CB _ _] |- _ => rewrite sub_coal_w in H end.
    eapply EPI; eassumption. }
  (* 0x1704c, the search (:337-343): lw a4,28(a0); beq a4,a2; addi a3,a3,-1; addi a0,a0,32; bnez a3 *)
  assert (LOOP : forall (f : nat) (i : Z) (xa0 xa3 xa4 xra xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    0 <= i -> Z.of_nat (S f) = q - i ->
    bv_unsigned xa0 = W_BASE_PLAIN + A_S_queue_bytes i -> bv_unsigned xa3 = q - i ->
    sub_k B C (submit_find_m B key i (S f)) = Some (B', r) ->
    evt rsegs QQ (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 cp)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) xa0 (Z_to_bv 64 q) (Z_to_bv 64 (bv_swrap 32 key))
                          xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x1704c) fc None m2 (seg_rom rsegs))).
  { intros f. induction f as [|f IH];
      intros i xa0 xa3 xa4 xra xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hi Hf H0 H3 HK;
      rewrite sub_find_S in HK;
      (revert HK; destruct (Z.leb_spec 512 i) as [I5|I5]; intros HK; cbv iota in HK;
       [ cbv [sub_k] in HK; discriminate HK | ]);
      (assert (HRk : ov_read_bytes rsegs m2 (Z_to_bv 64 (bv_unsigned xa0 + 28)) 4 = Some (sub B (A_S_queue_key i) 4)) by
        (apply (wm_read rsegs W_BASE_PLAIN m2 B);
         [ exact WM | unfold A_S_queue_key; lia | unfold A_S_queue_key; sub_lia
         | f_equal; rewrite H0; unfold A_S_queue_bytes, A_S_queue_key; lia ]));
      step; rewrite ?wm_lw; unfold s32_at; change (u_at B (A_S_queue_key i) 4) with (S_queue_key B i); clear HRk;
      step;
      (assert (SKR : 0 <= S_queue_key B i < 2^32) by
        (pose proof (u_at_range B (A_S_queue_key i) 4) as R; change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R; exact R));
      rewrite sub_eqb_s32 by lia;
      (revert HK; destruct (Z.eqb_spec (S_queue_key B i) key) as [KE|KE]; intros HK; cbv iota in HK |- *;
       [ apply sub_k_some in HK; destruct HK as [HB Hr]; eapply (COAL i); [lia | exact H0 | exact HB | exact Hr] | ]);
      do 3 step; rewrite H3.
    - (* the last turn: on to 0x17060 *)
      bfalse. eapply AT60. exact HK.
    - (* the next turn *)
      btrue.
      eapply (IH (i + 1));
        [ lia | lia
        | rewrite unsigned_lit by (rewrite H0; unfold A_S_queue_bytes; sub_lia); rewrite H0; unfold A_S_queue_bytes; lia
        | rewrite unsigned_lit by lia; lia
        | exact HK ]. }
  (* lui a0,0xf70; and a0,a2,a0; beqz a0: a key of kind 0 or 8 is not coalescable (:324-325, :336) *)
  do 3 step.
  rewrite ?(unsigned_lit key) by lia. rewrite sub_coal1 by lia.
  rewrite sub_coal_eq in HM.
  revert HM. destruct (Z.land (u8 (Z.shiftr key 16)) 247 =? 0) eqn:T1; intros HM; cbv iota.
  { cbn [orb] in HM. cbv iota in HM. eapply AT60. exact HM. }
  (* lui a0,0xff0; and a0,a2,a0; lui a3,0x90; beq a0,a3: nor of kind 9 *)
  do 4 step.
  rewrite ?(unsigned_lit key) by lia. rewrite sub_coal2 by lia.
  revert HM. destruct (u8 (Z.shiftr key 16) =? 9) eqn:T2; intros HM; cbv iota.
  { cbn [orb] in HM. cbv iota in HM. eapply AT60. exact HM. }
  cbn [orb] in HM. cbv iota in HM.
  (* beqz a1: no command queued, the search does not run *)
  step.
  rewrite sub_eqb_u by lia.
  revert HM. destruct (Z.eqb_spec q 0) as [Q0|Q0]; intros HM; cbv iota.
  { rewrite Q0 in HM. change (submit_find_m B key 0 (Z.to_nat 0)) with (Some (@None Z)) in HM.
    apply sub_k_none in HM. change (S_queued B) with q in HM.
    destruct HM as [(E & _) | (Hq & HB & Hr)]; [lia|].
    eapply APP; [exact Hq | exact HB | exact Hr]. }
  (* addi a0,s1,1760; sext.w a2,a2; mv a3,a1: the search from s->queue[0] *)
  do 3 step.
  replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 key) + 0))) with (Z_to_bv 64 (bv_swrap 32 key))
    by (rewrite unsigned_lit by lia; rewrite Z.add_0_r; reflexivity).
  eapply (LOOP (Z.to_nat q - 1)%nat 0);
    [ lia | lia
    | rewrite unsigned_lit by sub_lia; unfold A_S_queue_bytes; lia
    | rewrite unsigned_lit by lia; lia
    | replace (S (Z.to_nat q - 1)) with (Z.to_nat q) by lia; exact HM ].
Qed.
