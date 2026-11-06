(* Walk of send_data (transport/src/diginet_session.c:388-401) in the ubsan image, entry 0x178c0, frame 64, against
   U/Prog/T/send_data_c.v and the model send_data_m (TModel/TSess.v). The binary inlines inflight_start and send_raw.
   - 0x178c0-0x178f4: prologue, the header h of :390 on the stack (sp + 8 .. sp + 23), and the UBSan alignment test
     of s (andi a0,a0,7; bnez -> unimp at 0x179b8): s = &g_s = 0x33970 is 8-aligned, so the trap is not taken.
   - 0x178f8-0x17918: s->host_counter += ncmds (:391) and h.send_counter; unsigned arithmetic, no UBSan check. The
     binary adds the sign-extended words (lw, add, sw) and the model the uint32_t values: equal modulo 2^32.
   - 0x17930: diginet_frame_build (out = s->inflight_frame, cap 1514) by its wide contract. Its footprint is its
     stack window and the 1514-byte out cell inside the world; the kit's wk_post_call (TModel/TWorldMem.v) folds
     the cell back into the world (wm_fill_out). On an error answer (bltz at 0x17938) the cell is unchanged and the
     function returns it; otherwise the cell holds the model's lib_frame followed by its old bytes (sd_built).
   - 0x1793c-0x17978: inflight_len, inflight_start's four stores and stats.tx_data++ (:397-399), in another order
     than the model's; the world after them is the model's (EW8).
   - 0x1797c: jalr through g_s.io.send, which the model's call_send says holds io_send's address (0x1482c); the
     io_send contract with the frame s->inflight_frame inside g_s. Then send_raw's tx_frames++ on 0 (:91-93).
   No abort is reachable; the one UBSan trap branch (0x178f4) is closed by the value of s. Every other branch of
   the model's Some is followed by the binary: the build's answer (n <? 0), inflight_bytes (n <= 1514), the io.send
   test (S_io_send = ti_io_send), and io_send's answer (0 or -EIO, TModel/TIoSendFail.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TWorldMem TNeed
  TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_build_c diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import io_send_c send_data_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TIoSendFail.
Import ListNotations.
Open Scope Z_scope.

(* ==== build-independent facts the walk uses ==== *)

(* (int) and (uint32_t) agree modulo 2^32: the binary adds the sign-extended words, the model the unsigned ones *)
Lemma sd_swrap32_add_mod : forall a b, (bv_swrap 32 a + bv_swrap 32 b) mod 2^32 = (a + b) mod 2^32.
Proof.
  intros a b. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma sd_swrap32_mod : forall a, bv_swrap 32 a mod 2^32 = a mod 2^32.
Proof.
  intros a. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

(* the n little-endian bytes of a value depend on it modulo 2^(8n) only *)
Lemma sd_put_cong : forall n a b w, 8 * Z.of_nat n <= w -> a mod 2^w = b mod 2^w -> put n a = put n b.
Proof.
  intros n a b w Hw H. unfold put.
  rewrite <- (Z_to_le_bytes_mod n a w Hw), <- (Z_to_le_bytes_mod n b w Hw), H. reflexivity.
Qed.

Lemma sd_b8_cong : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
Qed.

(* the low byte of the sign-extended uint32_t ncmds is (uint8_t)ncmds *)
Lemma sd_byte_ncmds : forall x, (bv_swrap 32 x mod 2^64) mod 256 = (x mod 256) mod 256.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

(* the 12 header bytes h + 4 .. h + 15 among the cells of the frame *)
Lemma sd_hdr_bytes : forall m A (w0 w1 w2 : word) (c0 c1 : byte) R,
  bytes_at rsegs m A (le4 w0 ++ le4 w1 ++ le2 w2 ++ [c0] ++ [c1] ++ R) ->
  bytes_at rsegs m A (le4 w0 ++ le4 w1 ++ le2 w2 ++ [c0; c1]).
Proof.
  intros m A w0 w1 w2 c0 c1 R H.
  replace (le4 w0 ++ le4 w1 ++ le2 w2 ++ [c0] ++ [c1] ++ R) with ((le4 w0 ++ le4 w1 ++ le2 w2 ++ [c0; c1]) ++ R) in H
    by (rewrite <- !app_assoc; reflexivity).
  apply bytes_at_app in H. exact (proj1 H).
Qed.

(* a write of the first bytes x of a span, then the rest of the span as it was, is the write of x *)
Lemma sd_upd_app_tail : forall (B x : list byte) k c, 0 <= k -> (length x <= c)%nat ->
  k + Z.of_nat c <= Z.of_nat (length B) ->
  upd B k (x ++ skipn (length x) (sub B k c)) = upd B k x.
Proof.
  intros B x k c Hk Hx Hc. unfold upd, sub.
  rewrite length_app, length_skipn, length_firstn, length_skipn.
  replace (Nat.min c (length B - Z.to_nat k)) with c by lia.
  rewrite <- app_assoc. f_equal. f_equal.
  rewrite skipn_firstn_comm, skipn_skipn.
  rewrite <- (firstn_skipn (c - length x) (skipn (Z.to_nat k + length x) B)).
  rewrite skipn_skipn.
  replace (length x + Z.to_nat k)%nat with (Z.to_nat k + length x)%nat by lia.
  replace (Z.to_nat k + (length x + (c - length x)))%nat with (c - length x + (Z.to_nat k + length x))%nat by lia.
  reflexivity.
Qed.

(* every answer of diginet_frame_build into the 1514-byte inflight_frame *)
Lemma sd_code_range : forall body mode, -10 <= build_code_w body 1514 mode <= 1514.
Proof.
  intros body mode. unfold build_code_w, build_code, frame_len.
  destruct (orb (mode =? 0) (mode =? 1)); [|lia].
  destruct (Z.ltb_spec 1484 (Z.of_nat (length body))); [lia|].
  destruct (system_at body); [lia|].
  destruct (Z.ltb_spec 1514 (Z.max 60 (30 + Z.of_nat (length body)))); lia.
Qed.

(* diginet_frame_build's bytes in g_s.inflight_frame (offset 1864 of the world) when it answers a length: the model's
   frame, the rest of the array untouched; the length is frame_len and the sum mode is 0 or 1 *)
Lemma sd_built : forall (B1 dm sm body : list byte) send nc mode,
  length B1 = Z.to_nat W_LEN -> length dm = 6%nat -> length sm = 6%nat ->
  0 <= build_code_w body (Z.of_nat (length (sub B1 1864 1514))) mode ->
  upd B1 1864 (build_out_w dm sm send 0 0 0 nc body mode (sub B1 1864 1514)) =
  upd B1 1864 (lib_frame dm sm send 0 0 0 nc body mode) /\
  build_code_w body (Z.of_nat (length (sub B1 1864 1514))) mode = frame_len (length body) /\
  (mode = 0 \/ mode = 1).
Proof.
  intros B1 dm sm body send nc mode LB Ld Ls Hn.
  assert (LO : length (sub B1 1864 1514) = 1514%nat)
    by (apply length_sub; [lia | rewrite LB; unfold W_LEN; lia]).
  unfold build_out_w. rewrite LO in Hn |- *. change (Z.of_nat 1514) with 1514 in Hn |- *.
  assert (M01 : mode = 0 \/ mode = 1).
  { unfold build_code_w in Hn. destruct (Z.eqb_spec mode 0); [lia|]. destruct (Z.eqb_spec mode 1); [lia|].
    cbn [orb] in Hn. lia. }
  assert (EW : build_code_w body 1514 mode = build_code body 1514)
    by (unfold build_code_w; destruct M01 as [-> | ->]; reflexivity).
  rewrite EW in Hn |- *.
  assert (EC : build_code body 1514 = frame_len (length body) /\ (30 + length body <= 1514)%nat).
  { unfold build_code in Hn |- *.
    destruct (Z.ltb_spec 1484 (Z.of_nat (length body))); [lia|].
    destruct (system_at body); [lia|].
    destruct (Z.ltb_spec 1514 (frame_len (length body))); [lia|]. split; [reflexivity|]. unfold frame_len in *. lia. }
  destruct EC as [EC Lb]. rewrite EC.
  split; [|split; [reflexivity | exact M01]].
  assert (FL : 0 <= frame_len (length body)) by (unfold frame_len; lia).
  rewrite (proj2 (Z.leb_le 0 (frame_len (length body))) FL). cbv iota.
  rewrite frame_build_bytes by exact M01.
  pose proof (length_build_frame dm sm send 0 0 0 nc body (mode =? 1) Ld Ls) as LF.
  replace (Z.to_nat (frame_len (length body))) with (length (build_frame dm sm send 0 0 0 nc body (mode =? 1)))
    by lia.
  apply sd_upd_app_tail; [lia | | rewrite LB; unfold W_LEN; lia].
  unfold frame_len in LF. lia.
Qed.

(* ---- branch conditions over literal words (as lib/U/Prog/T/diginet_session_deadline.v) ---- *)
Lemma sd_signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 (z + 1)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - replace (z mod 2^64) with (z + 2^64).
    + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
    + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma sd_lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !sd_signed_lit by assumption. reflexivity. Qed.

Lemma sd_eqb_sl : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|N]; [apply bv_eqb_refl|].
  unfold bv_eqb. apply Z.eqb_neq. intros E. apply N.
  rewrite <- (sd_signed_lit a Ha), <- (sd_signed_lit b Hb). f_equal. apply bv_eq. exact E.
Qed.

(* ---- side goals of the world algebra: the offsets of g_s's members (OFF_g_s = 1648) and the lengths of the
   worlds the stores make ---- *)
Ltac sd_offs :=
  unfold A_S_host_counter, A_S_cfg_sum_mode, A_S_desk_mac, A_S_cfg_host_mac, A_S_io_send, A_S_inflight,
    A_S_inflight_frame, A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries, A_S_inflight_sent_us,
    A_S_stats_tx_frames, A_S_stats_tx_data, OFF_g_fail_next, OFF_g_s;
  rewrite ?length_put; cbn [Z.of_nat]; lia.
Ltac sd_len :=
  repeat match goal with
  | |- context [length (upd ?bs ?k (put ?n ?v))] => rewrite (length_upd_put bs k n v); [ | sd_offs | sd_len; sd_offs ]
  | |- context [length (upd ?bs ?k ?v)] => rewrite (length_upd bs v k); [ | sd_offs | sd_len; sd_offs ]
  end.
Ltac sd_side := sd_len; sd_offs.

Theorem send_data_holds : diginet_frame_build_contract_w -> io_send_contract -> send_data_contract.
Proof.
  intros FB IOS.
  unfold send_data_contract, send_data_ENTRY, send_data_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bodyp ncmds now r body B B' TF HA0 HA1 HA2 HA3 HA4 Hnc Hnow BODY ARG WM GF HM SP16 ST LO WOS MI.
  subst a0 a1 a2 a3 a4.
  unfold arg_blk, off_world, off_window in ARG. destruct ARG as (Hb0 & Hb64 & Hbw & Hbs).
  unfold w_off_stack in WOS.
  wk_facts.
  assert (EO : OFF_g_s = 1648) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB.
  (* diginet_frame_build's contract asks for a stack bound lo > 0. The walk runs on [lo1, sp) with lo1 = max 1 lo;
     the strip [lo, lo1) (the byte 0 when lo = 0) lies below every window the walk writes, and its fact about the
     entry memory is kept aside (in a conjunction the store and call tactics do not carry) for the end (FIN). *)
  set (lo1 := Z.max 1 lo).
  destruct (stk_split rsegs m lo lo1 (bv_unsigned sp) ST ltac:(unfold lo1; lia)) as [STa ST1].
  clear ST. rename ST1 into ST.
  assert (STLOW : stk rsegs m lo lo1 /\ True) by (split; [exact STa | exact I]). clear STa.
  (* ---- the model: the host counter, the sum mode and the build's answer ---- *)
  unfold send_data_m in HM. cbv zeta in HM.
  set (send := u32 (S_host_counter B + ncmds)) in HM.
  set (B1 := set_S_host_counter B send) in HM.
  assert (Hsend : 0 <= send < 2^32) by (unfold send, u32; apply Z.mod_pos_bound; lia).
  assert (LB1 : length B1 = Z.to_nat W_LEN)
    by (unfold B1, set_S_host_counter, A_S_host_counter; rewrite length_upd_put; [exact LB | lia | rewrite LB; lia]).
  assert (ESB1 : S_host_counter B1 = send).
  { unfold S_host_counter, B1, set_S_host_counter. rewrite u_at_upd_put by (unfold A_S_host_counter; rewrite ?LB; lia).
    apply Z.mod_small. change (2 ^ (8 * Z.of_nat 4)) with (2^32). lia. }
  assert (EMODE : S_cfg_sum_mode B1 = s32_at B 1668).
  { unfold S_cfg_sum_mode, B1, set_S_host_counter.
    rewrite s32_at_upd_out by (unfold A_S_host_counter, A_S_cfg_sum_mode; rewrite ?length_put, ?LB; cbn [Z.of_nat]; lia).
    reflexivity. }
  rewrite ESB1, EMODE in HM.
  assert (EN : diginet_frame_build_code body DIGINET_MAX_FRAME_LEN (s32_at B 1668) =
               build_code_w body 1514 (s32_at B 1668)).
  { unfold diginet_frame_build_code, build_code_w, DIGINET_MAX_FRAME_LEN. rewrite lib_build_code_eq.
    destruct ((s32_at B 1668 =? 0) || (s32_at B 1668 =? 1)); reflexivity. }
  rewrite EN in HM.
  set (n := build_code_w body 1514 (s32_at B 1668)) in HM.
  pose proof (sd_code_range body (s32_at B 1668)) as Rn. fold n in Rn.
  (* the bytes of the host counter the binary stores (lw, add, sw: modulo 2^32) are the model's *)
  assert (EB1 : upd B 1808 (put 4 (s32_at B 1808 + bv_swrap 32 ncmds)) = B1).
  { unfold B1, set_S_host_counter. change (A_S_host_counter) with 1808. f_equal.
    apply (sd_put_cong 4 _ _ 32); [cbn; lia|]. unfold s32_at, send, u32, S_host_counter.
    change (A_S_host_counter) with 1808.
    rewrite sd_swrap32_add_mod, Z.mod_mod by lia. reflexivity. }
  (* the footprint the walk tracks: its own 64 bytes and the deepest callee window (io_send, 288) below them, and the
     world; weakened to the contract's FRAME 576 at the end *)
  pose proof (munch_refl [(bv_unsigned sp - 352, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 64%nat ST.
  (* prologue: addi sp,sp,-64; sd ra,56(sp); sd s0,48(sp); sd s1,40(sp); sd s2,32(sp); sd s3,24(sp) *)
  do 6 step.
  (* mv s1,a0; sd zero,8(sp); sw zero,16(sp); sh zero,20(sp) *)
  do 4 step.
  (* sb zero,22(sp): the kit's cell_of_bytes reads a one-byte store as [b] *)
  step. unfold le1; cbn [Z_to_le_bytes]; mem_after_store_opt.
  (* andi a0,a0,7 *)
  step. replace (Z.land (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))) 7) with 0 by reflexivity.
  (* sb a3,23(sp) *)
  step. unfold le1; cbn [Z_to_le_bytes]; mem_after_store_opt.
  (* bnez a0: the alignment trap (0x178f4 -> unimp at 0x179b8) is not taken, s = &g_s = 0x33970 is 8-aligned *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* mv s0,a4; mv a6,a2; mv a5,a1; lw a0,160(s1); addi s2,s1,216; add a0,a0,a3; lw a7,20(s1) *)
  do 7 step.
  (* sw a0,160(s1): s->host_counter += ncmds (:391); the world is then the model's B1 *)
  step. rewrite EB1 in WMw.
  (* sw a0,12(sp) writes the middle of the C8 cell sd zero,8(sp) made: give that cell back as bytes first *)
  eapply (rw_cells_merge rsegs _ _ [_] [_] _) in FR.
  cbn [app cells_size cells_bytes csize cbytes Nat.add] in FR. rewrite app_nil_r in FR.
  step.
  (* addi a2,s1,120; li a1,1514; addi a4,sp,8; mv a0,s2; mv a3,s1 *)
  do 5 step.
  (* jal diginet_frame_build (:393): out = s->inflight_frame, cap 1514, dst = s->desk_mac, src = s->cfg.host_mac,
     h at sp + 8 (the header h of :390: send_counter at h + 4, then ack 0, retry 0, cmd DATA = 0, num_commands) *)
  step.
  set (oj := sub B1 1864 1514).
  assert (LOJ : length oj = 1514%nat) by (apply length_sub; [lia | rewrite LB1; lia]).
  pose proof (wm_cell rsegs W_BASE_UBSAN _ B1 1864 1514 (W_BASE_UBSAN + OFF_g_s + 216) WMw
                ltac:(lia) ltac:(lia) ltac:(lia)) as DST.
  fold oj in DST.
  pose proof (wm_src rsegs W_BASE_UBSAN _ B1 A_S_desk_mac 6 (W_BASE_UBSAN + OFF_g_s + 120) WMw
                ltac:(unfold A_S_desk_mac; lia) ltac:(unfold A_S_desk_mac; lia) ltac:(unfold A_S_desk_mac; lia)) as BDM.
  pose proof (wm_src rsegs W_BASE_UBSAN _ B1 A_S_cfg_host_mac 6 (W_BASE_UBSAN + OFF_g_s) WMw
                ltac:(unfold A_S_cfg_host_mac; lia) ltac:(unfold A_S_cfg_host_mac; lia)
                ltac:(unfold A_S_cfg_host_mac; lia)) as BSM.
  change (sub B1 A_S_desk_mac 6) with (S_desk_mac B1) in BDM.
  change (sub B1 A_S_cfg_host_mac 6) with (S_cfg_host_mac B1) in BSM.
  assert (LDM : length (S_desk_mac B1) = 6%nat)
    by (apply length_sub; [unfold A_S_desk_mac; lia | rewrite LB1; unfold A_S_desk_mac; lia]).
  assert (LSM : length (S_cfg_host_mac B1) = 6%nat)
    by (apply length_sub; [unfold A_S_cfg_host_mac; lia | rewrite LB1; unfold A_S_cfg_host_mac; lia]).
  (* the header bytes at h + 4 = sp - 60 *)
  assert (HDR : forall mm, rw_cells rsegs mm (bv_unsigned sp + -64)
      [CB 8 (firstn 8 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))));
       CB 4 (firstn 4 (le8 (Z_to_bv 64 0)));
       C4 (Z_to_bv 64 (s32_at B 1808 + bv_swrap 32 ncmds));
       C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0);
       C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)));
       C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 ncmds))));
       C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at rsegs mm (bv_unsigned sp + -56 + 4)
      (Z_to_le_bytes 4 send ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 2 0 ++ [b8 0; b8 (u8 ncmds)])).
  { intros mm [[Hwf Hb] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (L0 & L1 & _).
    cbn [cells_bytes cbytes] in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite L0 in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite L1 in Hb.
    replace (bv_unsigned sp + -64 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -56 + 4) in Hb by lia.
    apply sd_hdr_bytes in Hb.
    assert (E0 : le4 (Z_to_bv 64 (s32_at B 1808 + bv_swrap 32 ncmds)) = Z_to_le_bytes 4 send).
    { rewrite le4_put. apply (sd_put_cong 4 _ _ 32); [cbn; lia|].
      unfold s32_at, send, u32, S_host_counter. change (A_S_host_counter) with 1808.
      rewrite sd_swrap32_add_mod, Z.mod_mod by lia. reflexivity. }
    assert (E1 : le4 (Z_to_bv 64 0) = Z_to_le_bytes 4 0) by (vm_compute; reflexivity).
    assert (E2 : le2 (Z_to_bv 64 0) = Z_to_le_bytes 2 0) by (vm_compute; reflexivity).
    assert (E3 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)) = b8 0) by (vm_compute; reflexivity).
    assert (E4 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 ncmds))) = b8 (u8 ncmds)).
    { unfold b8, u8. apply sd_b8_cong. rewrite unsigned_lit_wrap. apply sd_byte_ncmds. }
    rewrite E0, E1, E2, E3, E4 in Hb. exact Hb. }
  replace (Z_to_bv 64 1514) with (Z_to_bv 64 (Z.of_nat (length oj))) by (rewrite LOJ; reflexivity).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
  pose proof (HDR mC FR) as HDRm. clear HDR.
  eapply evt_cut.
  { eapply FB with (send := send) (ack := 0) (retry := 0) (cmd := 0) (ncmds := u8 ncmds)
      (dmac := S_desk_mac B1) (smac := S_cfg_host_mac B1) (bb := body) (oj := oj) (lo := lo1).
    all: try exact DST.
    all: try rewrite Hsp; try rewrite LOJ.
    all: first [ assumption | apply s32_range | (unfold lo1, u8; Z.div_mod_to_equations; lia) ]. }
  wk_post_call rsegs mC.
  lazymatch goal with
  | P : stk rsegs ?mm lo1 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) |- _ =>
      rename mm into m2; rewrite Hsp in P; rename P into ST
  end.
  lazymatch goal with W : wmem rsegs m2 (upd B1 1864 _) |- _ => rename W into WM2 end.
  clear BDM BSM HDRm.
  rewrite LOJ. change (Z.of_nat 1514) with 1514. fold n.
  (* the final frame clause, shared by the three returns: the footprint weakened to FRAME 576, and the stack bound
     lo back from lo1 (the strip [lo, lo1) is outside the footprint, so the entry memory's fact carries over) *)
  assert (FIN : forall mF, munch [(bv_unsigned sp - 352, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mF ->
      wmono rsegs m mF -> stk rsegs mF lo1 (bv_unsigned sp) ->
      munch [(bv_unsigned sp - 576, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mF /\
      stk rsegs mF lo (bv_unsigned sp)).
  { intros mF MUF WMF STF. destruct STLOW as [STa _]. pose proof STa as (Hlo0 & _).
    split.
    - eapply munch_weaken; [| exact MUF]. unfold sub_fp. cbn [outside]. intros y Hy. lia.
    - apply (stk_merge rsegs mF lo lo1 (bv_unsigned sp)); [| exact STF | unfold lo1; lia].
      apply (stk_transport rsegs _ m mF lo lo1 STa MUF WMF).
      intros y Hy. left. unfold lo1 in Hy. cbn [outside]. repeat split; lia. }
  (* mv a2,a0; bltz a0 (:395) *)
  step. step.
  rewrite sd_lts_lit by lia.
  destruct (Z.ltb_spec n 0) as [Hneg|Hpos]; cbv iota.
  - (* the build failed (:395-396): return its answer; the world is B1 *)
    cbv beta iota in HM. injection HM as EB' Er. subst B' r.
    assert (EW : upd B1 1864 (build_out_w (S_desk_mac B1) (S_cfg_host_mac B1) send 0 0 0 (u8 ncmds) body
                                (s32_at B 1668) oj) = B1).
    { unfold build_out_w. rewrite LOJ. change (Z.of_nat 1514) with 1514. fold n.
      rewrite (proj2 (Z.leb_gt 0 n) Hneg). unfold oj. apply upd_sub_id; [lia | rewrite LB1; lia]. }
    rewrite EW in WM2.
    (* mv a0,a2; ld ra,56(sp); ld s0,48(sp); ld s1,40(sp); ld s2,32(sp); ld s3,24(sp) *)
    do 6 step.
    release_frame FR ST (bv_unsigned sp).
    (* addi sp,sp,64; ret *)
    do 2 step.
    destruct (FIN _ ltac:(eassumption) ltac:(eassumption) ST) as [MUF STF].
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MUF|]. split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
    split; [exact WM2|].
    unfold g_fail_next, B1, set_S_host_counter.
    rewrite u_at_upd_out by (unfold A_S_host_counter, OFF_g_fail_next; rewrite ?length_put, ?LB; cbn [Z.of_nat]; lia).
    exact GF.
  - (* the frame is built (:397-400) *)
    cbv beta iota in HM.
    unfold inflight_start_m in HM. cbv beta iota zeta in HM.
    destruct (sd_built B1 (S_desk_mac B1) (S_cfg_host_mac B1) body send (u8 ncmds) (s32_at B 1668) LB1 LDM LSM
               ltac:(change (sub B1 1864 1514) with oj; rewrite LOJ; exact Hpos)) as (EW & EC & M01).
    unfold oj in WM2. rewrite EW in WM2.
    assert (ENF : n = frame_len (length body))
      by (rewrite <- EC; change (sub B1 1864 1514) with oj; rewrite LOJ; reflexivity).
    set (B2 := set_S_inflight_frame B1 (lib_frame (S_desk_mac B1) (S_cfg_host_mac B1) send 0 0 DIGINET_CMD_DATA
                                         (u8 ncmds) body (s32_at B 1668))) in HM.
    change (wmem rsegs m2 B2) in WM2.
    pose proof (wm_len _ _ _ _ WM2) as LB2.
    assert (LLF : Z.of_nat (length (lib_frame (S_desk_mac B1) (S_cfg_host_mac B1) send 0 0 DIGINET_CMD_DATA
                                      (u8 ncmds) body (s32_at B 1668))) = n).
    { rewrite frame_build_bytes by exact M01. rewrite length_build_frame by assumption. symmetry. exact ENF. }
    set (B3 := set_S_inflight_len B2 n) in HM.
    set (B7 := set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight B3 1)
                 (S_host_counter B3)) 0) now) in HM.
    set (B8 := set_S_stats_tx_data B7 (u64 (S_stats_tx_data B7 + 1))) in HM.
    (* lui a0,0x4; lw a1,160(s1); li a3,1; addiw s3,a0,1808; sw a3,212(s1); add s3,s1,s3; ld a3,8(s3);
       ld a0,64(s1); ld a4,72(s1); sd a2,1736(s1); sw a1,1744(s1); sw zero,1748(s1); sd s0,1752(s1);
       addi a3,a3,1; sd a3,8(s3); mv a1,s2: inflight_len (:397), inflight_start (:398, inlined), stats.tx_data
       (:399), and the loads of io.ctx and io.send for send_raw (:400, inlined) *)
    do 16 step.
    (* the world the binary leaves is the model's B8: the stores in another order and the values modulo their width *)
    assert (EW8 : upd (upd (upd (upd (upd (upd B2 1860 (put 4 1)) 3384 (put 8 n)) 3392 (put 4 (s32_at B2 1808)))
                  3396 (put 4 0)) 3400 (put 8 now)) 19848 (put 8 (u_at (upd B2 1860 (put 4 1)) 19848 8 + 1)) = B8).
    { rewrite (upd_upd_comm B2 (put 4 1) (put 8 n) 1860 3384) by sd_side.
      assert (V1 : put 4 (s32_at B2 1808) = put 4 (S_host_counter B3)).
      { apply (sd_put_cong 4 _ _ 32); [cbn; lia|]. unfold s32_at, S_host_counter, B3, set_S_inflight_len.
        rewrite u_at_upd_out by sd_side. change A_S_host_counter with 1808. apply sd_swrap32_mod. }
      assert (ETX : u_at (upd B2 1860 (put 4 1)) 19848 8 = S_stats_tx_data B7).
      { unfold S_stats_tx_data, B7, B3, set_S_inflight_sent_us, set_S_inflight_retries, set_S_inflight_counter,
          set_S_inflight, set_S_inflight_len.
        repeat rewrite u_at_upd_out by sd_side. reflexivity. }
      rewrite V1, ETX.
      unfold B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries, set_S_inflight_counter,
        set_S_inflight, set_S_inflight_len.
      unfold u64. rewrite put_mod64 by lia. reflexivity. }
    lazymatch goal with W : wmem rsegs ?mm (upd _ 19848 _) |- _ => rewrite EW8 in W; rename W into WM8 end.
    pose proof (wm_len _ _ _ _ WM8) as LB8.
    (* the model: inflight_bytes (the inflight_len bytes of the frame), and the test of io.send against io_send *)
    assert (ELEN : S_inflight_len B8 = n).
    { unfold S_inflight_len, B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      repeat rewrite u_at_upd_out by sd_side. rewrite u_at_upd_put by sd_side.
      apply Z.mod_small. change (2 ^ (8 * Z.of_nat 8)) with (2^64). lia. }
    unfold inflight_bytes in HM. rewrite ELEN in HM.
    replace (1514 <? n) with false in HM by (symmetry; apply Z.ltb_ge; lia). cbv beta iota in HM.
    set (fr := sub B8 A_S_inflight_frame (Z.to_nat n)) in HM.
    assert (LFR : Z.of_nat (length fr) = n) by (unfold fr; rewrite length_sub by sd_side; lia).
    unfold send_raw_m, call_send in HM.
    destruct (Z.eqb_spec (S_io_send B8) (ti_io_send timg_ubsan)) as [HSND|NSND]; cbv beta iota in HM;
      [|discriminate HM].
    destruct (io_send_m timg_ubsan B8 fr) as [[B9 r0]|] eqn:HIO; cbv beta iota in HM; [|discriminate HM].
    assert (EA4 : u_at (upd B2 1860 (put 4 1)) 1720 8 = 84012).
    { transitivity (S_io_send B8); [| exact HSND].
      unfold S_io_send, B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      repeat rewrite u_at_upd_out by sd_side. reflexivity. }
    assert (GF8 : g_fail_next B8 = g_fail_next B).
    { unfold g_fail_next, B8, B7, B3, B2, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len, set_S_inflight_frame.
      repeat rewrite u_at_upd_out by sd_side.
      unfold B1, set_S_host_counter. rewrite u_at_upd_out by sd_side. reflexivity. }
    rewrite EA4.
    (* jalr a4: s->io.send (s->io.ctx, s->inflight_frame, s->inflight_len), the harness's io_send *)
    step.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length fr))) by (rewrite LFR; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
    assert (EIF : io_send_FRAME = 288) by reflexivity.
    eapply evt_cut.
    { eapply IOS with (B := B8) (frame := fr) (lo := lo1) (r := r0) (B' := B9) (p := W_BASE_UBSAN + OFF_g_s + 216);
        [ reflexivity | reflexivity | lia
        | apply (wm_src rsegs W_BASE_UBSAN _ B8 A_S_inflight_frame (Z.to_nat n)); [exact WM8 | sd_offs | sd_offs | sd_offs]
        | unfold io_send_frame_at, SZ_g_s; right; rewrite LFR; lia
        | rewrite LFR; lia
        | unfold off_window, io_send_FRAME; rewrite Hsp, LFR; lia
        | rewrite GF8; exact GF
        | rewrite Hsp; Z.div_mod_to_equations; lia
        | rewrite Hsp; exact ST
        | unfold io_send_FRAME; rewrite Hsp; unfold lo1; lia
        | unfold w_off_stack, io_send_FRAME; rewrite Hsp; lia
        | assumption
        | exact WM8
        | exact HIO ]. }
    wk_post_call rsegs mS.
    lazymatch goal with
    | P : stk rsegs ?mm lo1 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) |- _ =>
        rename mm into m3; rewrite Hsp in P; rename P into ST
    end.
    lazymatch goal with W : wmem rsegs m3 B9 |- _ => rename W into WM9 end.
    pose proof (wm_len _ _ _ _ WM9) as LB9.
    pose proof (io_send_m_fail_next _ _ _ _ _ HIO LB8) as GF9.
    pose proof (io_send_m_ret _ _ _ _ _ HIO) as R0. unfold EIO in R0.
    (* mv a2,a0; bnez a0 (send_raw :91) *)
    step. step.
    (* the binary tests a0 against 0; io_send's answer is 0 or -EIO *)
    rewrite sd_eqb_sl by lia.
    destruct (Z.eqb_spec r0 0) as [Z0|NZ]; cbn [negb]; cbv iota.
    + (* io_send answered 0: stats.tx_frames++ (:91-92), return 0 *)
      cbv beta iota in HM. injection HM as EB' Er. subst B' r. subst r0.
      (* li a2,0; ld a0,0(s3); addi a0,a0,1; sd a0,0(s3) *)
      do 4 step.
      assert (EWF : upd B9 19840 (put 8 (u_at B9 19840 8 + 1)) =
                    set_S_stats_tx_frames B9 (u64 (S_stats_tx_frames B9 + 1)))
        by (unfold set_S_stats_tx_frames, S_stats_tx_frames, u64; rewrite put_mod64 by lia; reflexivity).
      lazymatch goal with W : wmem rsegs _ (upd B9 19840 _) |- _ => rewrite EWF in W end.
      (* mv a0,a2; ld ra,56(sp); ld s0,48(sp); ld s1,40(sp); ld s2,32(sp); ld s3,24(sp) *)
      do 6 step.
      release_frame FR ST (bv_unsigned sp).
      (* addi sp,sp,64; ret *)
      do 2 step.
      destruct (FIN _ ltac:(eassumption) ltac:(eassumption) ST) as [MUF STF].
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MUF|]. split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
      split; [eassumption|].
      unfold g_fail_next, set_S_stats_tx_frames. rewrite u_at_upd_out by sd_side.
      unfold g_fail_next in GF9. lia.
    + (* io_send answered -EIO: return it (:93) *)
      cbv beta iota in HM. injection HM as EB' Er. subst B' r.
      (* mv a0,a2; ld ra,56(sp); ld s0,48(sp); ld s1,40(sp); ld s2,32(sp); ld s3,24(sp) *)
      do 6 step.
      release_frame FR ST (bv_unsigned sp).
      (* addi sp,sp,64; ret *)
      do 2 step.
      destruct (FIN _ ltac:(eassumption) ltac:(eassumption) ST) as [MUF STF].
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MUF|]. split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
      split; [exact WM9|]. lia.
Qed.
