(* Case 3 of the op loop of LLVMFuzzerTestOneInput in the plain image, 0x139cc-0x139e0 and 0x13b7c-0x13c50
   (fuzz_transport.c:1181-1188; TOps.v tags the same lines :1178-1186):
     case 3: { uint64_t scale = SCALE[fuzz_u8(&in) % 4]; op_begin(); g_now += scale * fuzz_u16(&in);
               m_tick(); diginet_session_tick(&g_s, g_now); settle(1); break; }
   The model is the op =? 3 branch of TOps.v LLVMFuzzerTestOneInput_op_m; llvm_op3 takes its steps, in its
   order, as hypotheses. The machine, from tr6/llvmf-plain.dis:
     0x139cc       beqz s6 (n = 0 after the op byte) -> 0x13b7c a0 = 0; else 0x139d0 lbu a0, 1(s4),
                   s6 = n - 2, s3 = cursor + 2, andi a0, a0, 3
     0x13b80-0x13b90  s0 = SCALE[a0]: the table at 0x10440 (auipc at 0x13b84 + 0xffffd000 - 0x744), the ELF
                   symbol LLVMFuzzerTestOneInput.SCALE, 4 x u64 {1, 1000, 100000, 1000000} (fuzz_transport.c:1126)
     0x13b94-0x13bc0  op_begin: memset(s9 + 0x158 = &OW, 0, 0x130), memset(s9 + 0x74 = &GOT, 0, 0xe0),
                   lbu g_fail_next, sw -1 at s9 + 0x240 (OW.desk_off), sw at s10 + 0x58 (M.fail)
     0x13bc4-0x13c1c  fuzz_u16 as two lbu (fuzz_u16_m is two fuzz_u8_m): n = 0 -> 0x13be0 (t = 0); n = 1 -> the
                   low byte only; else both bytes, s6 -= 2, s3 += 2, a1 = hi << 8
     0x13c20-0x13c30  ld g_now (s9 + 0x20), a0 = a1 | a0, a0 * s0, + g_now, sd g_now
     0x13c34       jal m_tick; 0x13c38-0x13c44 a0 = 0x32e00 (&g_s), a1 = s4 (the new g_now),
                   jal diginet_session_tick; 0x13c48-0x13c4c a0 = 1, jal settle; 0x13c50 j 0x1428c (the latch)
   World offsets (TWorld.v; s9 = W_BASE_PLAIN + OFF_g_fail_next = 0x32790 + 0xfdc8): OFF_g_fail_next 0xfdc8 = 64968,
   OFF_g_now 0xfde8 = 65000, OFF_GOT 0xfe3c = 65084 (SZ_GOT 224), OFF_OW 0xff20 = 65312 (SZ_OW 304),
   A_OW_desk_off = OFF_OW + 232 = 65544, A_M_fail = OFF_M + 88 = 88, OFF_g_s 0x670. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess TOps TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  m_tick_c diginet_session_tick_c settle_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_disp.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model facts case 3 needs ---- *)

(* B' has the length of B and B's g_now. The binary keeps the new g_now in s4 across m_tick (0x13c2c-0x13c40)
   and hands it to diginet_session_tick; the model reads g_now after m_tick. m_tick writes only M and OW
   (TIoRecv.v's list of setters), and g_now (OFF_g_now = 0xfde8, 8 bytes) lies outside both. *)
Definition op3_nkeep (B B' : list byte) : Prop := length B' = length B /\ g_now B' = g_now B.

Lemma op3_nkeep_refl : forall B, op3_nkeep B B.
Proof. intros B. split; reflexivity. Qed.

Lemma op3_nkeep_upd : forall B0 X k v, op3_nkeep B0 X -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length B0) ->
  (k + Z.of_nat (length v) <= OFF_g_now \/ OFF_g_now + 8 <= k) ->
  op3_nkeep B0 (upd X k v).
Proof.
  intros B0 X k v [L G] Hk Hl Hd. split.
  - rewrite length_upd; [exact L | exact Hk | rewrite L; exact Hl].
  - unfold g_now. assert (EN : OFF_g_now = 65000) by reflexivity.
    rewrite u_at_upd_out.
    + exact G.
    + exact Hk.
    + lia.
    + change (Z.of_nat 8) with 8. lia.
    + rewrite L. exact Hl.
Qed.

Ltac op3_nk_side := unfold OFF_g_now in *; gk_side.

Ltac op3_nk_go :=
  lazymatch goal with
  | |- op3_nkeep ?B0 (upd ?X ?k ?v) =>
      apply (op3_nkeep_upd B0 X k v); [op3_nk_go | op3_nk_side | op3_nk_side | op3_nk_side]
  | |- op3_nkeep ?B0 ?X =>
      first [ match goal with H : op3_nkeep B0 X |- _ => exact H end
            | lazymatch X with B0 => apply op3_nkeep_refl end ]
  end.

Ltac op3_nk := gk_setters; op3_nk_go.

Lemma op3_m_set_nk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' st why u, op3_nkeep B0 B -> m_set_m B st why = Some (B', u) -> op3_nkeep B0 B'.
Proof.
  intros B0 HL0 B B' st why u HK H. pose proof (len_w B0 HL0) as HL.
  unfold m_set_m in H. gk_split H; apply some_pair_inv in H as [<- _]; op3_nk.
Qed.

Lemma op3_m_lost_nk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' why u, op3_nkeep B0 B -> m_lost_m B why = Some (B', u) -> op3_nkeep B0 B'.
Proof.
  intros B0 HL0 B B' why u HK H. pose proof (len_w B0 HL0) as HL. unfold m_lost_m in H.
  refine (op3_m_set_nk B0 HL0 _ B' S_IDLE why u _ H). op3_nk.
Qed.

Lemma op3_m_tick_nk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' u, op3_nkeep B0 B -> m_tick_m B = Some (B', u) -> op3_nkeep B0 B'.
Proof.
  intros B0 HL0 B B' u HK H. unfold m_tick_m in H. gk_split H.
  all: first [ exact (op3_m_lost_nk B0 HL0 B B' _ u HK H)
             | (apply some_pair_inv in H as [<- _]; exact HK) ].
Qed.

(* the write of g_now: its length, its g_fail_next, its value *)
Lemma op3_len_now : forall Bx v, Z.of_nat (length Bx) = W_LEN -> Z.of_nat (length (set_g_now Bx v)) = W_LEN.
Proof.
  intros Bx v HL. unfold set_g_now. assert (EN : OFF_g_now = 65000) by reflexivity.
  rewrite length_upd_put; [exact HL | lia | rewrite HL; change (Z.of_nat 8) with 8; unfold W_LEN; lia].
Qed.

Lemma op3_fn_now : forall Bx v, Z.of_nat (length Bx) = W_LEN -> g_fail_next (set_g_now Bx v) = g_fail_next Bx.
Proof.
  intros Bx v HL. unfold set_g_now, g_fail_next.
  assert (EN : OFF_g_now = 65000) by reflexivity. assert (EF : OFF_g_fail_next = 64968) by reflexivity.
  rewrite u_at_upd_out; [reflexivity | lia | lia | | ];
    rewrite length_put; change (Z.of_nat 8) with 8; change (Z.of_nat 1) with 1; [lia|].
  rewrite HL. unfold W_LEN. lia.
Qed.

Lemma op3_now_now : forall Bx v, Z.of_nat (length Bx) = W_LEN -> g_now (set_g_now Bx v) = v mod 2 ^ 64.
Proof.
  intros Bx v HL. unfold set_g_now, g_now. assert (EN : OFF_g_now = 65000) by reflexivity.
  rewrite u_at_upd_put; [reflexivity | lia | rewrite HL; change (Z.of_nat 8) with 8; unfold W_LEN; lia].
Qed.

(* the register the binary stores to g_now (0x13c2c add s4, a0, s4) against the model's (g_now + scale * t) mod 2^64 *)
Lemma op3_now_eq : forall L S G, Z_to_bv 64 (L * S + G) = Z_to_bv 64 ((G + S * L) mod 2 ^ 64).
Proof. intros L S G. rewrite Z_to_bv_mod64. f_equal. ring. Qed.

(* a write that misses g_fail_next leaves it *)
Lemma op3_fn_upd : forall (Bx v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length Bx) ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd Bx k v) = g_fail_next Bx.
Proof.
  intros Bx v k Hk Hl Hd. unfold g_fail_next.
  rewrite u_at_upd_out; [reflexivity | lia | unfold OFF_g_fail_next; lia | cbn [Z.of_nat]; lia | lia].
Qed.

(* a put-write inside the world keeps its length and, when it misses g_fail_next, g_fail_next *)
Lemma op3_len_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> Z.of_nat (length (upd u k (put n v))) = W_LEN.
Proof. intros u k n v Hu Hk Hn. rewrite length_upd_put; [exact Hu | lia | rewrite Hu; lia]. Qed.

Lemma op3_fn_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd u k (put n v)) = g_fail_next u.
Proof. intros u k n v Hu Hk Hn Hd. apply op3_fn_upd; rewrite ?length_put; [lia | rewrite Hu; lia | lia]. Qed.

(* op_begin (fuzz_transport.c:388-394) as the binary runs it at 0x13b94-0x13bc0: the two memsets, then
   OW.desk_off = -1 (sw at 0x13bbc), then M.fail = the g_fail_next byte loaded at 0x13bb4, before either store.
   That is the model's order; the model reads g_fail_next after OW.desk_off's write, which misses it. *)
Lemma op3_begin_world : forall (Bx Bz : list byte), Z.of_nat (length Bx) = W_LEN ->
  Bz = upd (upd Bx 65312 (repeat (Z_to_bv 8 0) 304)) 65084 (repeat (Z_to_bv 8 0) 224) ->
  op_begin_m Bx = Some (upd (upd Bz 65544 (put 4 (-1))) 88 (put 4 (u_at Bz OFF_g_fail_next 1)), tt).
Proof.
  intros Bx Bz HL EZ.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (R304 : Z.of_nat (length (repeat (Z_to_bv 8 0) 304)) = 304) by (rewrite repeat_length; lia).
  assert (R224 : Z.of_nat (length (repeat (Z_to_bv 8 0) 224)) = 224) by (rewrite repeat_length; lia).
  assert (P4 : forall v : Z, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65312 (repeat (Z_to_bv 8 0) 304))) = W_LEN)
    by (rewrite length_upd; [exact HL | lia | rewrite R304; lia]).
  assert (LZ : Z.of_nat (length Bz) = W_LEN)
    by (rewrite EZ, length_upd; [exact L1 | lia | rewrite R224, L1; lia]).
  unfold op_begin_m, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT.
  change (Z.to_nat SZ_OW) with 304%nat. change (Z.to_nat SZ_GOT) with 224%nat.
  change (b8 0) with (Z_to_bv 8 0).
  rewrite <- EZ.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  assert (EFN : g_fail_next (upd Bz 65544 (put 4 (-1))) = u_at Bz OFF_g_fail_next 1).
  { change (u_at Bz OFF_g_fail_next 1) with (g_fail_next Bz).
    apply op3_fn_upd; [lia | rewrite P4, LZ; lia | rewrite P4; unfold OFF_g_fail_next; lia]. }
  rewrite EFN. reflexivity.
Qed.

Section OP3.
Context (data : Z) (D : list byte).

(* 0x13c20-0x13c50: g_now += scale * t, m_tick(), diginet_session_tick(&g_s, g_now), settle(1), the latch
   (fuzz_transport.c:1181-1185). a0 / a1 hold the two bytes of t (lo, hi << 8), s0 the scale, s3 / s6 the
   cursor after fuzz_u16. *)
Lemma llvm_op3_tail : forall Sp lo ops c3 t scale B1 B3 B4 B5 r
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    rz gp tp e0 e1 e2 wsc wlo whi q2 q3 q4 q5 q6 q7 w19 x20 w22 x23 e3 e4 e5 e6,
  m_tick_contract -> diginet_session_tick_contract -> settle_contract ->
  llvm_mem data D Sp lo B1 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c3 -> 0 <= ops < OPS_MAX ->
  w19 = Z_to_bv 64 (data + fi_off c3) -> w22 = Z_to_bv 64 (fi_n c3) ->
  bv_unsigned wsc = scale ->
  Z.lor (bv_unsigned whi) (bv_unsigned wlo) = t ->
  m_tick_m (set_g_now B1 ((g_now B1 + scale * t) mod 2^64)) = Some (B3, tt) ->
  diginet_session_tick_m timg_plain None B3 (g_now B3) = Some (B4, r) ->
  settle_m B4 1 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c3 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 wsc (Z_to_bv 64 7) wlo whi q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) w19 x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22 x23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13c20) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c3 t scale B1 B3 B4 B5 r ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    rz gp tp e0 e1 e2 wsc wlo whi q2 q3 q4 q5 q6 q7 w19 x20 w22 x23 e3 e4 e5 e6
    MTC DTC STC HM HC3 HOPS H19 H22 HSC HT HB3 HB4 HB5 HK.
  subst w19 w22.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B1) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_now. wk_eq_fact OFF_g_s.
  unfold off_world in HOW. unfold off_window in HOWIN.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU5.
  pose proof (wmono_refl rsegs m) as WMO5.
  (* 0x13c20 ld s4, g_now; 0x13c24 or a0, a1, a0 (t = hi << 8 | lo); 0x13c28 mul a0, a0, s0 (t * scale);
     0x13c2c add s4, a0, s4; 0x13c30 sd s4, g_now (fuzz_transport.c:1181 g_now += scale * t) *)
  do 5 zstep.
  set (B2 := set_g_now B1 ((g_now B1 + scale * t) mod 2 ^ 64)) in *.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    replace W with B2 in H end.
  2: { unfold B2, set_g_now, g_now. rewrite put_mod64 by lia. rewrite <- HT, <- HSC.
       replace OFF_g_now with 65000 by reflexivity. f_equal. f_equal. ring. }
  assert (LB2 : Z.of_nat (length B2) = W_LEN) by (unfold B2; apply op3_len_now; exact LBz).
  assert (FN2 : g_fail_next B2 = g_fail_next B1) by (unfold B2; apply op3_fn_now; exact LBz).
  lazymatch goal with H : rw_cells rsegs ?m5 W_BASE_PLAIN [CB _ B2] |- _ =>
    assert (HM5 : llvm_mem data D Sp lo B2 m0 m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
  { eapply (llvm_mem_after_call data D Sp lo 0 B1 B2 m0 m);
      [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MU5 | exact WMO5 | assumption | assumption
      | assumption | rewrite FN2; exact HFN ]. }
  clear HM0 MU5 WMO5.
  try clear HD; try clear HSTK; try clear HMI; try clear HRO; try clear HWM; try clear HRW; try clear HFN.
  pose proof HM5 as HM5c. unfold llvm_mem in HM5c.
  destruct HM5c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB2n.
  pose proof (m_tick_gk B2 LB2n B2 B3 tt (gkeep_refl B2) HB3) as [_ FN3].
  pose proof (op3_m_tick_nk B2 LB2n B2 B3 tt (op3_nkeep_refl B2) HB3) as [_ NW3].
  (* ---- 0x13c34 jal m_tick (fuzz_transport.c:1182) ---- *)
  zstep.
  eapply evt_cut.
  { eapply MTC with (B := B2) (lo := lo).
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold m_tick_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold m_tick_FRAME. lia.
    - exact HMI.
    - exact HWM.
    - exact HB3. }
  intros ms' Hpost.
  destruct Hpost as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & WM3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  assert (HM3 : llvm_mem data D Sp lo B3 m0 m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo m_tick_FRAME B2 B3 m0 _ m3);
      [ exact HM5 | unfold m_tick_FRAME, LLVM_LOOP_K; lia | exact MU3 | exact WMO3
      | exact MI3 | exact ST3 | exact WM3 | rewrite FN3; exact HFN ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU3 WMO3 MI3 ST3 WM3 HM5.
  pose proof HM3 as HM3c. unfold llvm_mem in HM3c.
  destruct HM3c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  assert (HNOW : 0 <= g_now B3 < 2 ^ 64).
  { unfold g_now. pose proof (u_at_range B3 OFF_g_now 8) as R. cbn in R. lia. }
  (* ---- 0x13c38-0x13c3c a0 = &g_s; 0x13c40 a1 = s4, the new g_now; 0x13c44 jal diginet_session_tick
     (fuzz_transport.c:1183) ---- *)
  rewrite (ret_pc_even 0x13c38) by (first [lia | reflexivity]).
  do 4 zstep.
  eapply evt_cut.
  { eapply DTC with (B := B3) (TF := None) (lo := lo) (now := g_now B3).
    - reflexivity.
    - rewrite NW3. unfold B2. rewrite op3_now_now by exact LBz.
      rewrite <- HT, <- HSC. unfold g_now. replace OFF_g_now with 65000 by reflexivity.
      rewrite Z_to_bv_mod64. apply op3_now_eq.
    - exact HNOW.
    - exact HWM.
    - exact HFN.
    - exact HB4.
    - exact I.
    - exact HRO.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_tick_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_tick_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (c0 & cc1 & c2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & f3 & f4 & f5 & f6 & m4 &
                     -> & MU4 & WMO4 & MI4 & ST4 & WM4 & FN4).
  rewrite unsigned_lit in MU4, ST4 by lia.
  assert (HM4 : llvm_mem data D Sp lo B4 m0 m4 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo diginet_session_tick_FRAME B3 B4 m0 _ m4);
      [ exact HM3 | unfold diginet_session_tick_FRAME, LLVM_LOOP_K; lia | exact MU4 | exact WMO4
      | exact MI4 | exact ST4 | exact WM4 | exact FN4 ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU4 WMO4 MI4 ST4 WM4 HM3.
  pose proof HM4 as HM4c. unfold llvm_mem in HM4c.
  destruct HM4c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  (* ---- 0x13c48 li a0, 1; 0x13c4c jal settle (fuzz_transport.c:1184 settle(1)) ---- *)
  rewrite (ret_pc_even 0x13c48) by (first [lia | reflexivity]).
  do 2 zstep.
  eapply evt_cut.
  { eapply STC with (B := B4) (ticked := 1) (lo := lo).
    - reflexivity.
    - lia.
    - exact HWM.
    - exact HB5.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (k0 & k1 & k2 & l0 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & n3 & n4 & n5 & n6 & m5 &
                     -> & MU5 & WMO5 & MI5 & ST5 & EB & WM5).
  rewrite unsigned_lit in MU5, ST5 by lia.
  subst B5.
  assert (HM5 : llvm_mem data D Sp lo B4 m0 m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo settle_FRAME B4 B4 m0 m4 m5);
      [ exact HM4 | unfold settle_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU5
      | exact WMO5 | exact MI5 | exact ST5 | exact WM5 | exact HFN ]. }
  (* ---- 0x13c50 j 0x1428c, the latch ---- *)
  rewrite (ret_pc_even 0x13c50) by (first [lia | reflexivity]).
  zstep.
  apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC3|]. exact HM5.
Qed.

(* 0x13b94-0x13c1c: op_begin (the two memsets, OW.desk_off, M.fail) and fuzz_u16 for t, a byte at a time
   (fuzz_transport.c:1180-1181). s0 holds the scale the table gave, s3 / s6 the cursor after the scale byte. *)
Lemma llvm_op3_mid : forall Sp lo ops c2 c3 t scale B B1 B3 B4 B5 r
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    rz gp tp e0 e1 e2 wsc q0 q1 q2 q3 q4 q5 q6 q7 w19 x20 w22 x23 e3 e4 e5 e6,
  memset_contract -> m_tick_contract -> diginet_session_tick_contract -> settle_contract ->
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c2 -> 0 <= ops < OPS_MAX ->
  w19 = Z_to_bv 64 (data + fi_off c2) -> w22 = Z_to_bv 64 (fi_n c2) ->
  bv_unsigned wsc = scale ->
  op_begin_m B = Some (B1, tt) ->
  fuzz_u16_m D c2 = (c3, t) ->
  m_tick_m (set_g_now B1 ((g_now B1 + scale * t) mod 2^64)) = Some (B3, tt) ->
  diginet_session_tick_m timg_plain None B3 (g_now B3) = Some (B4, r) ->
  settle_m B4 1 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c3 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 wsc (Z_to_bv 64 7) q0 q1 q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) w19 x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22 x23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13b94) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c2 c3 t scale B B1 B3 B4 B5 r ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    rz gp tp e0 e1 e2 wsc q0 q1 q2 q3 q4 q5 q6 q7 w19 x20 w22 x23 e3 e4 e5 e6
    MSC MTC DTC STC HM HC2 HOPS H19 H22 HSC HB1 HU16 HB3 HB4 HB5 HK.
  subst w19 w22.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_OW. wk_eq_fact OFF_GOT.
  wk_eq_fact OFF_M. wk_eq_fact A_M_fail. wk_eq_fact A_OW_desk_off. wk_eq_fact SZ_OW. wk_eq_fact SZ_GOT.
  (* ---- 0x13b94-0x13ba0: memset(&OW, 0, 0x130) (op_begin, fuzz_transport.c:390) ---- *)
  do 4 zstep.
  assert (CW1 : rw_cells rsegs m (W_BASE_PLAIN + OFF_OW) [CB (Z.to_nat 304) (sub B OFF_OW 304)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m B OFF_OW 304 (W_BASE_PLAIN + OFF_OW) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B OFF_OW 304).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) by lia. exact CW1.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) in MU1, CZ1 by lia.
  cbn [Z.to_nat] in CZ1.
  assert (HM1 : llvm_mem data D Sp lo (upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) m0 m1
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo B m0 m m1);
      [ exact HM0 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_OW in *; lia).
    exact HFN. }
  clear HM0 HD HSTK HMI HRO HWM HRW HFN CW1 CZ1 MU1 WMO1 MI1.
  (* ---- 0x13ba4-0x13bb0: memset(&GOT, 0, 0xe0) (op_begin, fuzz_transport.c:391) ---- *)
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Ba := upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) in *.
  assert (LBa : Z.of_nat (length Ba) = W_LEN)
    by (unfold Ba; rewrite length_upd; [exact LBz | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13ba4) by (first [lia | reflexivity]).
  do 4 zstep.
  assert (CW2 : rw_cells rsegs m1 (W_BASE_PLAIN + OFF_GOT) [CB (Z.to_nat 224) (sub Ba OFF_GOT 224)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m1 Ba OFF_GOT 224 (W_BASE_PLAIN + OFF_GOT) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub Ba OFF_GOT 224).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) by lia. exact CW2.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 &
                     -> & MU2 & WMO2 & MI2 & CZ2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) in MU2, CZ2 by lia.
  cbn [Z.to_nat] in CZ2.
  assert (HM2 : llvm_mem data D Sp lo (upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) m0 m2
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo Ba m0 m1 m2);
      [ exact HM1 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_GOT in *; lia).
    exact HFN. }
  clear HD HSTK HMI HRO HWM HRW HFN CW2 CZ2 MU2 WMO2 MI2 HM1.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Bb := upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) in *.
  assert (LBb : Z.of_nat (length Bb) = W_LEN)
    by (unfold Bb; rewrite length_upd; [exact LBa | lia | rewrite repeat_length; lia]).
  (* the world after op_begin, in the binary's store order *)
  assert (EB1 : upd (upd Bb 65544 (put 4 (-1))) 88 (put 4 (u_at Bb OFF_g_fail_next 1)) = B1).
  { rewrite (op3_begin_world B Bb LBz eq_refl) in HB1. congruence. }
  rewrite (ret_pc_even 0x13bb4) by (first [lia | reflexivity]).
  (* ---- 0x13bb4 lbu a0, g_fail_next; 0x13bb8 li a1, -1; 0x13bbc sw a1, OW.desk_off; 0x13bc0 sw a0, M.fail
     (op_begin, fuzz_transport.c:392-393) ---- *)
  assert (EFNa : OFF_g_fail_next = 64968) by reflexivity.
  assert (EWLa : W_LEN = 65616) by reflexivity.
  assert (LB1a : Z.of_nat (length (upd Bb 65544 (put 4 (-1)))) = W_LEN)
    by (apply op3_len_put; [exact LBb | lia | cbn [Z.of_nat]; lia]).
  assert (FN1 : g_fail_next B1 = g_fail_next Bb).
  { rewrite <- EB1.
    rewrite op3_fn_put by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite op3_fn_put by (first [exact LBb | cbn [Z.of_nat]; lia]).
    reflexivity. }
  unfold off_world in HOW. unfold off_window in HOWIN.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m2) as MU6.
  pose proof (wmono_refl rsegs m2) as WMO6.
  do 4 zstep.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    replace W with B1 in H by (rewrite <- EB1; reflexivity) end.
  lazymatch goal with H : rw_cells rsegs ?m6 W_BASE_PLAIN [CB _ B1] |- _ =>
    assert (HM6 : llvm_mem data D Sp lo B1 m0 m6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
  { eapply (llvm_mem_after_call data D Sp lo 0 Bb B1 m0 m2);
      [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6 | assumption | assumption
      | assumption | rewrite FN1; exact HFN ]. }
  clear HM2 MU6 WMO6.
  try clear HD; try clear HSTK; try clear HMI; try clear HRO; try clear HWM; try clear HRW; try clear HFN.
  pose proof HM6 as HM6c. unfold llvm_mem in HM6c.
  destruct HM6c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  unfold llvm_cursor in HC2.
  pose proof (bytes_at_bound rsegs _ data D HD) as HDB.
  assert (HC3 : forall c3', c3' = fst (fuzz_u16_m D c2) -> llvm_cursor D c3').
  { intros c3' ->. unfold llvm_cursor, fuzz_u16_m, fuzz_u8_m.
    destruct (Z.eqb_spec (fi_n c2) 0); cbn [fi_off fi_n fst];
      [destruct (Z.eqb_spec (fi_n c2) 0); cbn [fi_off fi_n fst]; lia|].
    destruct (Z.eqb_spec (fi_n c2 - 1) 0); cbn [fi_off fi_n fst]; lia. }
  (* ---- 0x13bc4 beqz s6: fuzz_u16's first fuzz_u8 (fuzz.h:40-46), n == 0 ---- *)
  zstep.
  if_cases K; zify_cond K.
  - (* n == 0: both bytes are 0 and the cursor stays (0x13be0 a0 = 0, a1 = 0, j 0x13c20) *)
    assert (EU : fuzz_u16_m D c2 = (c2, 0)).
    { unfold fuzz_u16_m, fuzz_u8_m. rewrite K. cbn. rewrite K. reflexivity. }
    pose proof (HC3 c2 ltac:(rewrite EU; reflexivity)) as HC3'.
    rewrite EU in HU16. injection HU16 as Ec3 Et. subst c3 t.
    do 3 zstep.
    eapply llvm_op3_tail with (c3 := c2) (t := 0);
      [ exact MTC | exact DTC | exact STC | exact HM6 | exact HC3' | exact HOPS | reflexivity | reflexivity
      | exact HSC | | exact HB3 | exact HB4 | exact HB5 | exact HK ].
    rewrite !unsigned_lit by lia. reflexivity.
  - (* n >= 1: the low byte (0x13bc8 lbu a0, 0(s3)) *)
    assert (HK0 : (Z.to_nat (fi_off c2) + 1 <= length D)%nat) by lia.
    pose proof (bytes_at_read rsegs _ data D (fi_off c2) 1 HD ltac:(lia) HK0) as HR0.
    rewrite disp_sub1 in HR0 by lia.
    set (b0 := nth (Z.to_nat (fi_off c2)) D (b8 0)) in *.
    assert (Hb0 : 0 <= bv_unsigned b0 < 256).
    { pose proof (bv_unsigned_in_range 8 b0) as R. unfold bv_modulus in R.
      change (2 ^ Z.of_N 8) with 256 in R. lia. }
    zstep.
    (* 0x13bcc bne s6, s8 (s8 = 1): fuzz_u16's second fuzz_u8, n == 0 after the first *)
    zstep.
    if_cases K1; zify_cond K1.
    + (* n >= 2: the high byte (0x13c10 lbu a1, 1(s3); s6 -= 2; s3 += 2; a1 <<= 8) *)
      assert (HK1 : (Z.to_nat (fi_off c2 + 1) + 1 <= length D)%nat) by lia.
      pose proof (bytes_at_read rsegs _ data D (fi_off c2 + 1) 1 HD ltac:(lia) HK1) as HR1.
      rewrite disp_sub1 in HR1 by lia.
      set (b1 := nth (Z.to_nat (fi_off c2 + 1)) D (b8 0)) in *.
      assert (Hb1 : 0 <= bv_unsigned b1 < 256).
      { pose proof (bv_unsigned_in_range 8 b1) as R. unfold bv_modulus in R.
        change (2 ^ Z.of_N 8) with 256 in R. lia. }
      assert (EU : fuzz_u16_m D c2 =
                   (FuzzIn (fi_off c2 + 1 + 1) (fi_n c2 - 1 - 1),
                    Z.lor (bv_unsigned b0) (Z.shiftl (bv_unsigned b1) 8) mod 2 ^ 16)).
      { unfold fuzz_u16_m, fuzz_u8_m. destruct (Z.eqb_spec (fi_n c2) 0) as [E|E]; [lia|].
        cbn [fi_n fi_off]. destruct (Z.eqb_spec (fi_n c2 - 1) 0) as [E'|E']; [lia|]. reflexivity. }
      pose proof (HC3 _ ltac:(rewrite EU; reflexivity)) as HC3'.
      rewrite EU in HU16. injection HU16 as Ec3 Et. subst c3 t.
      do 4 zstep.
      eapply llvm_op3_tail with (c3 := FuzzIn (fi_off c2 + 1 + 1) (fi_n c2 - 1 - 1))
          (t := Z.lor (bv_unsigned b0) (Z.shiftl (bv_unsigned b1) 8) mod 2 ^ 16);
        [ exact MTC | exact DTC | exact STC | exact HM6 | exact HC3' | exact HOPS | | | exact HSC | 
        | exact HB3 | exact HB4 | exact HB5 | exact HK ].
      * cbn [fi_off]. f_equal. lia.
      * cbn [fi_n]. f_equal. lia.
      * (* t = lo | hi << 8, the model's Z.lor lo (Z.shiftl hi 8) mod 2^16 *)
        assert (S8 : 0 <= Z.shiftl (bv_unsigned b1) 8 < 65536).
        { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. }
        rewrite !unsigned_lit by lia.
        rewrite Z.lor_comm. rewrite lor_shiftl8_add by lia.
        change (2 ^ 16) with 65536. rewrite Z.mod_small by lia. reflexivity.
    + (* n == 1: the high byte is 0 (0x13bd0 s6 = 0, a1 = 0, s3 += 1) *)
      assert (EU : fuzz_u16_m D c2 =
                   (FuzzIn (fi_off c2 + 1) (fi_n c2 - 1), Z.lor (bv_unsigned b0) (Z.shiftl 0 8) mod 2 ^ 16)).
      { unfold fuzz_u16_m, fuzz_u8_m. destruct (Z.eqb_spec (fi_n c2) 0) as [E|E]; [lia|].
        cbn [fi_n fi_off]. destruct (Z.eqb_spec (fi_n c2 - 1) 0) as [E'|E']; [|lia]. reflexivity. }
      pose proof (HC3 _ ltac:(rewrite EU; reflexivity)) as HC3'.
      rewrite EU in HU16. injection HU16 as Ec3 Et. subst c3 t.
      do 4 zstep.
      eapply llvm_op3_tail with (c3 := FuzzIn (fi_off c2 + 1) (fi_n c2 - 1))
          (t := Z.lor (bv_unsigned b0) (Z.shiftl 0 8) mod 2 ^ 16);
        [ exact MTC | exact DTC | exact STC | exact HM6 | exact HC3' | exact HOPS | | | exact HSC |
        | exact HB3 | exact HB4 | exact HB5 | exact HK ].
      * cbn [fi_off]. f_equal. lia.
      * cbn [fi_n]. f_equal. lia.
      * (* t = lo, the model's Z.lor lo (Z.shiftl 0 8) mod 2^16 *)
        rewrite !unsigned_lit by lia. rewrite Z.shiftl_0_l, Z.lor_0_l, Z.lor_0_r.
        change (2 ^ 16) with 65536. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma llvm_op3 : forall Sp lo ops c c1 c2 c3 sb t B B1 B3 B4 B5 r
    m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memset_contract -> m_tick_contract -> diginet_session_tick_contract -> settle_contract ->
  llvm_case data D m0 gp tp 3 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  fuzz_u8_m D c1 = (c2, sb) ->
  op_begin_m B = Some (B1, tt) ->
  fuzz_u16_m D c2 = (c3, t) ->
  m_tick_m (set_g_now B1 ((g_now B1 + nth (Z.to_nat (sb mod 4)) LLVMFuzzerTestOneInput_SCALE 0 * t) mod 2^64))
    = Some (B3, tt) ->
  diginet_session_tick_m timg_plain None B3 (g_now B3) = Some (B4, r) ->
  settle_m B4 1 = Some (B5, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c3 B5
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 c2 c3 sb t B B1 B3 B4 B5 r m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MSC MTC DTC STC H HU8 HB1 HU16 HB3 HB4 HB5 HK.
  destruct H as (rz & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  pose proof HM as HM0.
  unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  (* the op byte's fuzz_u8 (the dispatch's c1): the cursor one byte on *)
  assert (EC1 : c1 = FuzzIn (fi_off c + 1) (fi_n c - 1)).
  { rewrite HC1. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  clear HC1. subst c1.
  assert (HC1 : llvm_cursor D (FuzzIn (fi_off c + 1) (fi_n c - 1))) by (unfold llvm_cursor; cbn; lia).
  assert (HN1 : 0 <= fi_n c - 1 < 2 ^ 64) by lia.
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
  cbn [fi_off fi_n].
  (* ---- 0x139cc beqz s6: the scale byte's fuzz_u8 (fuzz_transport.c:1179), n == 0 ---- *)
  zstep.
  if_cases K; zify_cond K.
  - (* n == 0: the scale index is 0 and the cursor stays (0x13b7c mv a0, zero) *)
    assert (E2 : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) = (FuzzIn (fi_off c + 1) (fi_n c - 1), 0)).
    { unfold fuzz_u8_m. cbn [fi_n]. destruct (Z.eqb_spec (fi_n c - 1) 0); [reflexivity|lia]. }
    rewrite E2 in HU8. injection HU8 as Ec2 Esb. subst c2 sb.
    (* 0x13b7c a0 = 0; 0x13b80 slli a0, a0, 3; 0x13b84-0x13b88 a1 = SCALE (0x10440, the symbol
       LLVMFuzzerTestOneInput.SCALE, 4 x u64 {1, 1000, 100000, 1000000}); 0x13b8c add; 0x13b90 ld s0 *)
    do 6 zstep.
    eapply llvm_op3_mid with (c2 := FuzzIn (fi_off c + 1) (fi_n c - 1))
        (scale := nth (Z.to_nat (0 mod 4)) LLVMFuzzerTestOneInput_SCALE 0);
      [ exact MSC | exact MTC | exact DTC | exact STC | exact HM0 | exact HC1 | exact HOPS
      | cbn [fi_off]; reflexivity | cbn [fi_n]; reflexivity | reflexivity
      | exact HB1 | exact HU16 | exact HB3 | exact HB4 | exact HB5 | exact HK ].
  - (* n >= 1: the scale byte (0x139d0 lbu a0, 1(s4)), s6 = n - 2, s3 = cursor + 2, a0 &= 3 *)
    assert (HK1 : (Z.to_nat (fi_off c + 1) + 1 <= length D)%nat) by lia.
    pose proof (bytes_at_read rsegs m data D (fi_off c + 1) 1 HD ltac:(lia) HK1) as HR.
    rewrite disp_sub1 in HR by lia.
    set (b := nth (Z.to_nat (fi_off c + 1)) D (b8 0)) in *.
    assert (Hb : 0 <= bv_unsigned b < 256).
    { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
      change (2 ^ Z.of_N 8) with 256 in R. lia. }
    assert (E2 : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) =
                 (FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1), bv_unsigned b)).
    { unfold fuzz_u8_m. cbn [fi_n fi_off]. destruct (Z.eqb_spec (fi_n c - 1) 0); [lia|reflexivity]. }
    rewrite E2 in HU8. injection HU8 as Ec2 Esb. subst c2 sb.
    (* 0x139d0 lbu a0, 1(s4); 0x139d4 s6 = n - 2; 0x139d8 s3 = cursor + 2; 0x139dc andi a0, a0, 3 *)
    do 4 zstep.
    (* the table index sb mod 4 (fuzz_transport.c:1179 SCALE[fuzz_u8(&in) % 4]): one case per entry, so the
       load at 0x13b90 reads a fixed table slot *)
    assert (HL3 : Z.land (bv_unsigned b) 3 = bv_unsigned b mod 4).
    { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
    rewrite HL3.
    assert (HC2 : llvm_cursor D (FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1))) by (unfold llvm_cursor; cbn; lia).
    assert (HQ : bv_unsigned b mod 4 = 0 \/ bv_unsigned b mod 4 = 1 \/
                 bv_unsigned b mod 4 = 2 \/ bv_unsigned b mod 4 = 3).
    { pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)). lia. }
    (* 0x139e0 j 0x13b80; 0x13b80 slli a0, a0, 3; 0x13b84-0x13b88 a1 = SCALE (0x10440); 0x13b8c add;
       0x13b90 ld s0, the entry SCALE[sb mod 4] *)
    destruct HQ as [E|[E|[E|E]]]; rewrite E;
      do 6 zstep;
      (eapply llvm_op3_mid with (c2 := FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1))
          (scale := nth (Z.to_nat (bv_unsigned b mod 4)) LLVMFuzzerTestOneInput_SCALE 0);
        [ exact MSC | exact MTC | exact DTC | exact STC | exact HM0 | exact HC2 | exact HOPS
        | cbn [fi_off]; f_equal; lia | cbn [fi_n]; f_equal; lia | rewrite E; reflexivity
        | exact HB1 | exact HU16 | exact HB3 | exact HB4 | exact HB5 | exact HK ]).
Qed.

End OP3.
