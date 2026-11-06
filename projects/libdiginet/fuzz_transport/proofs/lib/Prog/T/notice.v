(* notice (fuzz/fuzz_transport.c:937-973; model TCb.v notice_m), entry 0x149e4, 70 instructions, against
   Prog/T/notice_c.v. Prologue `addi sp,sp,-16; sd ra,8(sp)`, then `lw a0,0(a1)` (n->kind), `addi a0,a0,-1` and
   `bltu 5,a0` to the shared epilogue 0x14af0 for a kind outside 1..6; else the .rodata jump table at 0x10428:
     kind 1 DESK     0x14a18  GOT.desk++ (world store), frame popped, tail call check_state_desk (entry sp);
     kind 2 STATE    0x14a88  GOT.t[GOT.n] := (state, old, reason) when GOT.n <= 15, GOT.n++, and when the
                              state is 2 frame popped and tail call check_state_online, else 0x14af0;
     kind 3 DATA     0x14a4c  jal check_state_data (sp - 16), GOT.ndata++, 0x14af0;
     kind 4 ACKED    0x14a68  GOT.acked++, frame popped, tail call check_inflight_acked (entry sp);
     kind 5 ACK_LOST 0x14a38  jal check_inflight_lost (sp - 16), M.fly.on := 0, 0x14af0;
     kind 6 FOREIGN  0x14ae0  GOT.foreign++, falls into 0x14af0.
   The callees get the notice as ntc_cut n: the same notice with the announce version / name cut to their first 10
   bytes (the struct's char[10] fields). ntc_at bounds the announce's span only by 20 bytes, so a longer list
   could reach into the bytes notice writes (the saved ra, the world) and would not survive the stores; the cut
   one does, and no callee model reads past byte 9 (strz_len <= 9, DgnSpec.v strz_len_le). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import
  check_state_online_c check_inflight_acked_c check_inflight_lost_c check_state_desk_c check_state_data_c notice_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the notice the callees get ---- *)

Definition ann_cut (a : tann) : tann := TAnn (firstn 10 (ta_version a)) (firstn 10 (ta_name a)).
Definition ntc_cut (n : ntc) : ntc :=
  Ntc (n_kind n) (n_state n) (n_old n) (n_reason n) (n_counter n) (n_retry n) (n_mac_offset n)
      (n_pers n) (option_map ann_cut (n_ann n)) (n_body n) (n_body_len n).

Lemma nt_bytes_firstn : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k (Ha & Hl & H). unfold bytes_at. rewrite length_firstn.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite ne_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  apply H. lia.
Qed.

(* bytes off notice's window and off the world keep their values across notice's footprint *)
Lemma nt_mv : forall m m' (sp : word) a (bs : list byte), bytes_at rsegs m a bs ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  (a + Z.of_nat (length bs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a) ->
  (a + Z.of_nat (length bs) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= a) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' sp a bs B MU H1 H2. eapply bytes_at_transport; [exact B | exact MU |].
  cbn [disjoint_from]. split; [exact H1 | split; [exact H2 | exact I]].
Qed.

Lemma ntc_move : forall m m' p n (sp sp' : word) K',
  ntc_at m p n sp 48 ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  bv_unsigned sp - 48 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  ntc_at m' p (ntc_cut n) sp' K'.
Proof.
  intros m m' p n sp sp' K' NT MU H1 H2.
  destruct NT as (P0 & P8 & OW & OWi & NB & BN & LN & K0 & K4 & K8 & K12 & KP & KM & KBL & KC & KR & BB & OWB & OWiB
                  & ANN).
  unfold ntc_cut, ntc_at. cbn [n_kind n_state n_old n_reason n_counter n_retry n_mac_offset n_pers n_ann n_body n_body_len].
  unfold off_world, off_window in *.
  split; [exact P0|]. split; [exact P8|]. split; [exact OW|]. split; [lia|].
  exists NB. split; [eapply nt_mv; [exact BN | exact MU | rewrite LN; lia | rewrite LN; lia]|].
  split; [exact LN|]. do 9 (split; [assumption|]).
  split; [eapply nt_mv; [exact BB | exact MU | lia | lia]|].
  split; [exact OWB|]. split; [lia|].
  destruct (n_ann n) as [a|]; cbn [option_map]; [|exact ANN].
  destruct ANN as (A0 & A8 & BV & BNm & AW & AWi).
  unfold ann_cut. cbn [ta_version ta_name].
  split; [exact A0|]. split; [exact A8|].
  split; [eapply nt_mv; [apply nt_bytes_firstn; exact BV | exact MU | rewrite length_firstn; lia
                         | rewrite length_firstn; lia]|].
  split; [eapply nt_mv; [apply nt_bytes_firstn; exact BNm | exact MU | rewrite length_firstn; lia
                         | rewrite length_firstn; lia]|].
  split; [exact AW | lia].
Qed.

Lemma tframe_move : forall m m' (sp sp' : word) K' Fr,
  tframe_at m sp 48 Fr ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  bv_unsigned sp - 48 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' Fr.
Proof.
  intros m m' sp sp' K' [fr|] TF MU H1 H2; [|exact I].
  destruct TF as (T0 & TB & TW & TWi). unfold tframe_at, off_world, off_window in *.
  split; [exact T0|]. split; [eapply nt_mv; [exact TB | exact MU | lia | lia]|]. split; [exact TW | lia].
Qed.

Lemma relro_move : forall m m' (sp : word), relro_img m ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 48 -> relro_img m'.
Proof.
  intros m m' sp RR MU WS i Hi. unfold mrd. rewrite MU.
  - exact (RR i Hi).
  - cbn [outside]. unfold RELRO_BASE, RELRO_LEN, W_BASE_PLAIN, W_LEN in *.
    rewrite wa_unsigned by lia. split; [lia | split; [lia | exact I]].
Qed.

(* ---- the callee models do not see the cut ---- *)

Lemma acked_cut : forall B n, check_inflight_acked_m B (ntc_cut n) = check_inflight_acked_m B n.
Proof. reflexivity. Qed.
Lemma lost_cut : forall B n, check_inflight_lost_m B (ntc_cut n) = check_inflight_lost_m B n.
Proof. reflexivity. Qed.
Lemma data_cut : forall F B n, check_state_data_m F B (ntc_cut n) = check_state_data_m F B n.
Proof. reflexivity. Qed.

Lemma fsl_le : forall F q k, frame_strz_len F q = Some k -> (k <= 9)%nat.
Proof.
  intros [f|] q k E; [|discriminate E]. unfold frame_strz_len, list_strz_len in E.
  destruct (q - tf_addr f <? 0); [discriminate E|].
  destruct (_ <? _)%nat; [discriminate E|]. injection E as <-. apply strz_len_le.
Qed.

Lemma firstn10_firstn : forall (l : list byte) k, (k <= 10)%nat -> firstn k (firstn 10 l) = firstn k l.
Proof. intros l k Hk. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma firstn10_len : forall (l : list byte) k, (k < 10)%nat ->
  (length (firstn 10 l) <=? k)%nat = (length l <=? k)%nat.
Proof. intros l k Hk. rewrite length_firstn. apply Bool.eq_iff_eq_true. rewrite !Nat.leb_le. lia. Qed.

Lemma firstn10_nth : forall (l : list byte) k d, (k < 10)%nat -> nth k (firstn 10 l) d = nth k l d.
Proof.
  intros l k d Hk. destruct (Nat.lt_ge_cases k (length l)) as [L|L].
  - rewrite <- (firstn_skipn 10 l) at 2. rewrite app_nth1; [reflexivity|]. rewrite length_firstn. lia.
  - rewrite (nth_overflow (firstn 10 l)) by (rewrite length_firstn; lia). rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma desk_cut : forall I F B n, check_state_desk_m I F B (ntc_cut n) = check_state_desk_m I F B n.
Proof.
  intros I F B n. unfold check_state_desk_m, ntc_cut.
  cbn [n_kind n_state n_old n_reason n_counter n_retry n_mac_offset n_pers n_ann n_body n_body_len].
  destruct (n_ann n) as [a|]; cbn [option_map]; [|reflexivity].
  unfold ann_cut. cbn [ta_version ta_name]. cbv beta iota zeta.
  destruct (frame_strz_len F (OW_desk_body B + SPEC_ANN_VERSION)) as [vn|] eqn:EV; [|reflexivity].
  destruct (frame_strz_len F (OW_desk_body B + SPEC_ANN_NAME)) as [nn|] eqn:EN; [|reflexivity].
  apply fsl_le in EV. apply fsl_le in EN.
  rewrite (firstn10_firstn (ta_version a) vn), (firstn10_len (ta_version a) vn), (firstn10_nth (ta_version a) vn),
    (firstn10_firstn (ta_name a) nn), (firstn10_len (ta_name a) nn), (firstn10_nth (ta_name a) nn) by lia.
  reflexivity.
Qed.

(* ---- machine facts ---- *)

Lemma nb_rd : forall m p (NB : list byte) k n, bytes_at rsegs m p NB -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length NB) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (p + k)) n = Some (sub NB k n).
Proof. intros m p NB k n B Hk Hn. exact (bytes_at_read rsegs m p NB k n B Hk ltac:(lia)). Qed.

Lemma nt_signed : forall v, -2^63 <= v < 2^63 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2^64). change (bv_half_modulus 64) with (2^63).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma nt_lts : forall c v, -2^63 <= c < 2^63 -> -2^63 <= v < 2^63 ->
  bv_lts (Z_to_bv 64 c) (Z_to_bv 64 v) = (c <? v).
Proof. intros c v Hc Hv. unfold bv_lts. rewrite !nt_signed by lia. reflexivity. Qed.

Lemma nt_eqb : forall v k, -2^63 <= v < 2^63 -> 0 <= k < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small k) by lia.
  destruct (Z.eqb_spec v k) as [->|N]; [rewrite Z.mod_small by lia; apply Z.eqb_refl|]. apply Z.eqb_neq. intros E.
  destruct (Z_lt_le_dec v 0) as [L|L].
  - rewrite <- (Z.mod_add v 1 (2^64)) in E by lia. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

(* bltu 5, kind - 1: taken exactly for a kind outside 1..6 *)
Lemma nt_ltu_out : forall k, -2^31 <= k < 2^31 -> k < 1 \/ 6 < k ->
  bv_ltu (Z_to_bv 64 5) (Z_to_bv 64 (k + -1)) = true.
Proof.
  intros k Hk Hout. rewrite bv_ltu_Z, !unsigned_lit_wrap. apply Z.ltb_lt.
  change (5 mod 2^64) with 5.
  destruct (Z_lt_le_dec (k + -1) 0) as [L|L].
  - rewrite <- (Z.mod_add (k + -1) 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma nt_sp16 : forall z, z mod 16 = 0 -> (z + -16) mod 16 = 0.
Proof. intros z H. replace (z + -16) with (z + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.

(* GOT.t[g]'s address after slli 2 / slli 4 / sub / add *)
Lemma nt_idx : forall g, 0 <= g <= 15 ->
  Z_to_bv 64 (271704 + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 g)) 4))
                        - bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 g)) 2))))
  = Z_to_bv 64 (12 * g + 271704).
Proof.
  intros g Hg. f_equal. rewrite (unsigned_lit g) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !unsigned_lit by lia. lia.
Qed.

(* the three GOT.t[g] stores, at the offsets the world hook computes, are the model's setters *)
Lemma got_t_upd : forall B g st old rs,
  upd (upd (upd B (65088 + 12 * g) (put 4 st)) (65092 + 12 * g) (put 4 old)) (65096 + 12 * g) (put 4 rs)
  = set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state B g st) g old) g rs.
Proof.
  intros. unfold set_GOT_t_reason, set_GOT_t_old, set_GOT_t_state, A_GOT_t_reason, A_GOT_t_old, A_GOT_t_state, OFF_GOT.
  replace (65084 + 4 + 12 * g + 0) with (65088 + 12 * g) by lia.
  replace (65084 + 4 + 12 * g + 4) with (65092 + 12 * g) by lia.
  replace (65084 + 4 + 12 * g + 8) with (65096 + 12 * g) by lia.
  reflexivity.
Qed.

(* x + 1 in int is defined: the model premise is not None *)
Ltac inc_ok HM x :=
  let E := fresh "Einc" in
  assert (E : (x =? INT_MAX) = false)
    by (destruct (x =? INT_MAX) eqn:E0; [unfold int_inc in HM; rewrite E0 in HM; cbv beta iota in HM; discriminate HM
                                        | reflexivity]);
  unfold int_inc in HM; rewrite E in HM; cbv beta iota in HM.

Theorem notice_holds : check_state_online_contract -> check_inflight_acked_contract -> check_inflight_lost_contract ->
  check_state_desk_contract -> check_state_data_contract -> notice_contract.
Proof.
  intros CON CACK CLOST CDESK CDATA.
  unfold notice_contract, notice_ENTRY, notice_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    p n Fr Ha1 NT TF RR WM HM S16 ST LO WS MI.
  subst a1.
  wk_facts.
  pose proof NT as (Hp0 & Hp8 & OWp & OWinp & NB & BNB & LNB & K0 & K4 & K8 & K12 & _).
  unfold off_world in OWp. unfold off_window in OWinp. unfold w_off_stack in WS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (s32_range NB 0) as RK0. pose proof (s32_range NB 4) as RK4.
  pose proof (s32_range NB 8) as RK8. pose proof (s32_range NB 12) as RK12.
  rewrite K0 in RK0. rewrite K4 in RK4. rewrite K8 in RK8. rewrite K12 in RK12.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  rename m into m0.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  step.                                   (* 0x149e4 addi sp,sp,-16 *)
  step.                                   (* 0x149e8 sd ra,8(sp) *)
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -16) ?cs |- _ => set (FRC := cs) in H end.
  assert (LFR : cells_size FRC = 16%nat) by reflexivity.
  (* the shared epilogue 0x14af0: ld ra,8(sp); addi sp,sp,16; ret *)
  assert (EPI : forall (m2 : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -16) FRC -> stk rsegs m2 lo (bv_unsigned sp + -16) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m2 ->
    wmono rsegs m0 m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B' ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14af0) fc None m2 (seg_rom rsegs))).
  { intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR2 ST2 MU2 WO2 MI2 WM2.
    unfold FRC in FR2.
    step.                                 (* 0x14af0 ld ra,8(sp) *)
    step.                                 (* 0x14af4 addi sp,sp,16 *)
    step.                                 (* 0x14af8 ret *)
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold QQ. do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WO2|]. split; [exact MI2|]. split; [exact ST2 | exact WM2]. }
  pose proof (nb_rd m p NB 0 4 BNB ltac:(lia) ltac:(rewrite LNB; lia)) as RD.
  step.                                   (* 0x149ec lw a0,0(a1): n->kind *)
  rewrite wm_lw, K0. clear RD.
  step.                                   (* 0x149f0 addi a0,a0,-1 *)
  step.                                   (* 0x149f4 li a2,5 *)
  unfold notice_m in HM.
  assert (KR : (n_kind n < 1 \/ 6 < n_kind n) \/ (1 <= n_kind n <= 6)) by lia.
  destruct KR as [KO|KI].
  { (* a kind outside 1..6: bltu to the epilogue; the model returns its world *)
    step.                                 (* 0x149f8 bltu a2,a0 *)
    if_true_by (nt_ltu_out (n_kind n) RK0 KO).
    assert (EB : B' = B).
    { revert HM. cbv zeta.
      destruct (Z.eqb_spec (n_kind n) N_STATE) as [E|_]; [unfold N_STATE in E; lia|].
      destruct (Z.eqb_spec (n_kind n) N_ACKED) as [E|_]; [unfold N_ACKED in E; lia|].
      destruct (Z.eqb_spec (n_kind n) N_ACK_LOST) as [E|_]; [unfold N_ACK_LOST in E; lia|].
      destruct (Z.eqb_spec (n_kind n) N_DESK) as [E|_]; [unfold N_DESK in E; lia|].
      destruct (Z.eqb_spec (n_kind n) N_DATA) as [E|_]; [unfold N_DATA in E; lia|].
      destruct (Z.eqb_spec (n_kind n) N_FOREIGN) as [E|_]; [unfold N_FOREIGN in E; lia|].
      intros E. inversion E. reflexivity. }
    subst B'. eapply EPI; eassumption. }
  assert (KC : n_kind n = 1 \/ n_kind n = 2 \/ n_kind n = 3 \/ n_kind n = 4 \/ n_kind n = 5 \/ n_kind n = 6) by lia.
  destruct KC as [Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]; rewrite Ek in HM |- *;
    unfold N_STATE, N_ACKED, N_ACK_LOST, N_DESK, N_DATA, N_FOREIGN in HM; cbn [Z.eqb Pos.eqb] in HM;
    step; if_false; do 7 step.            (* bltu not taken; slli; auipc; addi; add; lw (table); add; jr *)
  - (* kind 1, DESK, 0x14a18: GOT.desk++, frame popped, tail call check_state_desk *)
    step.                                 (* auipc a0,0x2e *)
    step.                                 (* lw a2,-892(a0): GOT.desk *)
    change (s32_at B 65292) with (GOT_desk B).
    inc_ok HM (GOT_desk B).
    step.                                 (* addi a2,a2,1 *)
    step.                                 (* sw a2,-892(a0) *)
    step.                                 (* mv a0,a1 *)
    unfold FRC in FR.
    step.                                 (* ld ra,8(sp) *)
    step.                                 (* addi sp,sp,16 *)
    step.                                 (* j check_state_desk *)
    release_frame FR ST (bv_unsigned sp).
    eapply evt_cut.
    { eapply CDESK with (p := p) (n := ntc_cut n) (Fr := Fr) (B' := B') (lo := lo).
      - reflexivity.
      - eapply ntc_move; [exact NT | exact MU | unfold check_state_desk_FRAME; lia | lia].
      - eapply tframe_move; [exact TF | exact MU | unfold check_state_desk_FRAME; lia | lia].
      - eapply relro_move; [exact RR | exact MU | exact WS].
      - eassumption.
      - rewrite desk_cut. exact HM.
      - exact S16.
      - exact ST.
      - unfold check_state_desk_FRAME. exact LO.
      - unfold w_off_stack, check_state_desk_FRAME. exact WS.
      - exact MI. }
    intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                Eq & MU3 & WO3 & MI3 & ST3 & EB & WM3).
    subst ms'. apply evt_done. unfold QQ.
    exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m3. split; [reflexivity|].
    split; [|split; [exact (wmono_trans rsegs _ _ _ WO WO3)|split; [exact MI3|split; [exact ST3|rewrite EB; exact WM3]]]].
    eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU3].
    unfold check_state_desk_FRAME. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
  - (* kind 2, STATE, 0x14a88: record the transition, GOT.n++, check ONLINE *)
    step.                                 (* auipc a0,0x2e *)
    step.                                 (* addi a0,a0,-1328: a0 = 0x42558 *)
    step.                                 (* lw a3,116(a0): GOT.n *)
    change (s32_at B 65084) with (GOT_n B).
    pose proof (s32_range B 65084) as RG. change (s32_at B 65084) with (GOT_n B) in RG.
    pose proof (nb_rd m p NB 4 4 BNB ltac:(lia) ltac:(rewrite LNB; lia)) as RD.
    step.                                 (* lw a2,4(a1): n->state *)
    rewrite wm_lw, K4. clear RD.
    step.                                 (* li a4,15 *)
    step.                                 (* blt a4,a3 *)
    rewrite nt_lts by lia.
    unfold TRANS_MAX in HM.
    (* 0x14ac4: GOT.n++, then ONLINE -> tail call check_state_online, else the epilogue *)
    assert (TAIL : forall (m2 : word -> option byte) (B1 : list byte) (x11 x14 x15 : word),
      rw_cells rsegs m2 (bv_unsigned sp + -16) FRC -> stk rsegs m2 lo (bv_unsigned sp + -16) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m2 ->
      wmono rsegs m0 m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B1 ->
      (if n_state n =? S_ONLINE then check_state_online_m (set_GOT_n B1 (GOT_n B + 1))
       else Some (set_GOT_n B1 (GOT_n B + 1), tt)) = Some (B', tt) ->
      evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x42558) x11
                            (Z_to_bv 64 (n_state n)) (Z_to_bv 64 (GOT_n B)) x14 x15 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x14ac4) fc None m2 (seg_rom rsegs))).
    { intros m2 B1 x11 x14 x15 FR2 ST2 MU2 WO2 MI2 WM2 HT.
      unfold FRC in FR2. unfold S_ONLINE in HT.
      step.                               (* 0x14ac4 addi a3,a3,1 *)
      step.                               (* li a1,2 *)
      step.                               (* sw a3,116(a0): GOT.n := GOT.n + 1 *)
      step.                               (* bne a2,a1 *)
      rewrite nt_eqb by lia.
      destruct (Z.eqb_spec (n_state n) 2) as [S2|S2]; cbn [negb].
      + replace (n_state n =? 2) with true in HT by (symmetry; apply Z.eqb_eq; exact S2). cbv beta iota in HT.
        step.                             (* ld ra,8(sp) *)
        step.                             (* addi sp,sp,16 *)
        step.                             (* j check_state_online *)
        release_frame FR2 ST2 (bv_unsigned sp).
        eapply evt_cut.
        { eapply CON with (B' := B') (lo := lo).
          - eassumption.
          - exact HT.
          - exact S16.
          - exact ST2.
          - unfold check_state_online_FRAME. lia.
          - unfold w_off_stack, check_state_online_FRAME. lia.
          - exact MI2. }
        intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 &
                    Eq & MU4 & WO4 & MI4 & ST4 & EB & WM4).
        subst ms'. apply evt_done. unfold QQ.
        exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m4. split; [reflexivity|].
        split; [|split; [exact (wmono_trans rsegs _ _ _ WO2 WO4)|split; [exact MI4|split; [exact ST4|rewrite EB; exact WM4]]]].
        eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MU4].
        unfold check_state_online_FRAME. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
      + replace (n_state n =? 2) with false in HT by (symmetry; apply Z.eqb_neq; exact S2). cbv beta iota in HT.
        injection HT as EB. subst B'.
        eapply EPI; eassumption. }
    destruct (Z.ltb_spec 15 (GOT_n B)) as [GH|GL]; cbv beta iota.
    + (* GOT.n >= 16: no record *)
      replace (GOT_n B <? 16) with false in HM by (symmetry; apply Z.ltb_ge; lia). cbv beta iota in HM.
      inc_ok HM (GOT_n B).
      eapply TAIL; eassumption.
    + (* 0 <= GOT.n <= 15: GOT.t[GOT.n] := (state, old, reason) *)
      replace (GOT_n B <? 16) with true in HM by (symmetry; apply Z.ltb_lt; lia). cbv beta iota in HM.
      assert (G0 : 0 <= GOT_n B).
      { destruct (Z_lt_le_dec (GOT_n B) 0) as [L|L]; [|exact L].
        replace (GOT_n B <? 0) with true in HM by (symmetry; apply Z.ltb_lt; exact L). cbv beta iota in HM.
        discriminate HM. }
      replace (GOT_n B <? 0) with false in HM by (symmetry; apply Z.ltb_ge; exact G0). cbv beta iota in HM.
      inc_ok HM (GOT_n B).
      step.                               (* slli a4,a3,2 *)
      step.                               (* slli a5,a3,4 *)
      step.                               (* sub a5,a5,a4 *)
      pose proof (nb_rd m p NB 8 4 BNB ltac:(lia) ltac:(rewrite LNB; lia)) as RD.
      step.                               (* lw a4,8(a1): n->old_state *)
      rewrite wm_lw, K8. clear RD.
      pose proof (nb_rd m p NB 12 4 BNB ltac:(lia) ltac:(rewrite LNB; lia)) as RD.
      step.                               (* lw a1,12(a1): n->reason *)
      rewrite wm_lw, K12. clear RD.
      step.                               (* add a5,a0,a5 *)
      rewrite (nt_idx (GOT_n B)) by lia.
      (* the store hook proves `k + length bs <= W_LEN` by lia when these are in the context; without them it
         falls back to vm_compute on the open offset 65088 + 12 * GOT_n B, which runs away (25 GB, killed) *)
      pose proof (length_le4 (Z_to_bv 64 (n_state n))) as L1.
      pose proof (length_le4 (Z_to_bv 64 (n_old n))) as L2.
      pose proof (length_le4 (Z_to_bv 64 (n_reason n))) as L3.
      step.                               (* sw a2,120(a5) *)
      step.                               (* sw a4,124(a5) *)
      step.                               (* sw a1,128(a5) *)
      lazymatch goal with W : rw_cells _ _ W_BASE_PLAIN _ |- _ => rewrite got_t_upd in W end.
      eapply TAIL; eassumption.
  - (* kind 3, DATA, 0x14a4c: jal check_state_data, GOT.ndata++ *)
    destruct (check_state_data_m Fr B n) as [[B1 []]|] eqn:ED; cbv beta iota in HM;
      [|discriminate HM].
    step.                                 (* mv a0,a1 *)
    step.                                 (* jal check_state_data *)
    eapply evt_cut.
    { eapply CDATA with (p := p) (n := ntc_cut n) (Fr := Fr) (B' := B1) (lo := lo).
      - reflexivity.
      - eapply ntc_move; [exact NT | exact MU | rewrite Hsp; unfold check_state_data_FRAME; lia | rewrite Hsp; lia].
      - eapply tframe_move; [exact TF | exact MU | rewrite Hsp; unfold check_state_data_FRAME; lia | rewrite Hsp; lia].
      - exact WM.
      - rewrite data_cut. exact ED.
      - rewrite Hsp. apply nt_sp16. exact S16.
      - rewrite Hsp. exact ST.
      - rewrite Hsp. unfold check_state_data_FRAME. lia.
      - unfold w_off_stack, check_state_data_FRAME. rewrite Hsp. lia.
      - exact MI. }
    intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                Eq & MU3 & WO3 & MI3 & ST3 & EB1 & WM3).
    subst ms'. subst B1. rewrite Hsp in MU3, ST3. unfold check_state_data_FRAME in MU3.
    clear WM. transport_after_call rsegs m m3 MU3 WO3. clear MU3 WO3 MI.
    rewrite (ret_pc_even 0x14a54) by (first [lia | reflexivity]).
    inc_ok HM (GOT_ndata B).
    injection HM as EB. subst B'.
    step.                                 (* auipc a0,0x2e *)
    step.                                 (* lw a1,-940(a0): GOT.ndata *)
    change (s32_at B 65304) with (GOT_ndata B).
    step.                                 (* addi a1,a1,1 *)
    step.                                 (* sw a1,-940(a0) *)
    step.                                 (* j 0x14af0 *)
    eapply EPI; eassumption.
  - (* kind 4, ACKED, 0x14a68: GOT.acked++, frame popped, tail call check_inflight_acked *)
    step.                                 (* auipc a0,0x2e *)
    step.                                 (* lw a2,-964(a0): GOT.acked *)
    change (s32_at B 65300) with (GOT_acked B).
    inc_ok HM (GOT_acked B).
    step.                                 (* addi a2,a2,1 *)
    step.                                 (* sw a2,-964(a0) *)
    step.                                 (* mv a0,a1 *)
    unfold FRC in FR.
    step.                                 (* ld ra,8(sp) *)
    step.                                 (* addi sp,sp,16 *)
    step.                                 (* j check_inflight_acked *)
    release_frame FR ST (bv_unsigned sp).
    eapply evt_cut.
    { eapply CACK with (p := p) (n := ntc_cut n) (B' := B') (lo := lo).
      - reflexivity.
      - eapply ntc_move; [exact NT | exact MU | unfold check_inflight_acked_FRAME; lia | lia].
      - eassumption.
      - rewrite acked_cut. exact HM.
      - exact S16.
      - exact ST.
      - unfold check_inflight_acked_FRAME. lia.
      - unfold w_off_stack, check_inflight_acked_FRAME. lia.
      - exact MI. }
    intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                Eq & MU3 & WO3 & MI3 & ST3 & EB & WM3).
    subst ms'. apply evt_done. unfold QQ.
    exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m3. split; [reflexivity|].
    split; [|split; [exact (wmono_trans rsegs _ _ _ WO WO3)|split; [exact MI3|split; [exact ST3|rewrite EB; exact WM3]]]].
    eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU3].
    unfold check_inflight_acked_FRAME. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
  - (* kind 5, ACK_LOST, 0x14a38: jal check_inflight_lost, M.fly.on := 0 *)
    destruct (check_inflight_lost_m B n) as [[B1 []]|] eqn:EL; cbv beta iota in HM;
      [|discriminate HM].
    injection HM as EB. subst B'.
    step.                                 (* mv a0,a1 *)
    step.                                 (* jal check_inflight_lost *)
    eapply evt_cut.
    { eapply CLOST with (p := p) (n := ntc_cut n) (B' := B1) (lo := lo).
      - reflexivity.
      - eapply ntc_move; [exact NT | exact MU | rewrite Hsp; unfold check_inflight_lost_FRAME; lia | rewrite Hsp; lia].
      - exact WM.
      - rewrite lost_cut. exact EL.
      - rewrite Hsp. apply nt_sp16. exact S16.
      - rewrite Hsp. exact ST.
      - rewrite Hsp. unfold check_inflight_lost_FRAME. lia.
      - unfold w_off_stack, check_inflight_lost_FRAME. rewrite Hsp. lia.
      - exact MI. }
    intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                Eq & MU3 & WO3 & MI3 & ST3 & EB1 & WM3).
    subst ms'. subst B1. rewrite Hsp in MU3, ST3. unfold check_inflight_lost_FRAME in MU3.
    clear WM. transport_after_call rsegs m m3 MU3 WO3. clear MU3 WO3 MI.
    rewrite (ret_pc_even 0x14a40) by (first [lia | reflexivity]).
    step.                                 (* auipc a0,0x1e *)
    step.                                 (* sw zero,-592(a0): M.fly.on := 0 *)
    step.                                 (* j 0x14af0 *)
    eapply EPI; eassumption.
  - (* kind 6, FOREIGN, 0x14ae0: GOT.foreign++, into the epilogue *)
    step.                                 (* auipc a0,0x2e *)
    step.                                 (* lw a1,-1088(a0): GOT.foreign *)
    change (s32_at B 65296) with (GOT_foreign B).
    inc_ok HM (GOT_foreign B).
    step.                                 (* addi a1,a1,1 *)
    step.                                 (* sw a1,-1088(a0) *)
    injection HM as EB. subst B'.
    eapply EPI; eassumption.
Qed.
