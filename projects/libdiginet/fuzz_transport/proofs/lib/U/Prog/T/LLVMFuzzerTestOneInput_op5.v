(* Case 5 of the op loop of LLVMFuzzerTestOneInput in the ubsan image, 0x13b74-0x13bc8, then the shared tail
   0x1456c-0x14570 (fuzz_transport.c:1193-1199 `case 5: op_begin(); want = m_wake(); rc = diginet_session_wake(&g_s,
   g_now); check_state_wake_code(rc, want); settle(0); break;`):
     0x13b74 memset(&OW, 0, 0x130)         op_begin :390, the world upd B OFF_OW (304 zeros)
     0x13b84 memset(&GOT, 0, 0xe0)         op_begin :391, upd . OFF_GOT (224 zeros)
     0x13b94 lbu g_fail_next; sw -1 at OW.desk_off (65544); sw g_fail_next at M.fail (88)   op_begin :392-393
     0x13ba4 jal m_wake                    want in a0, kept in s4
     0x13ba8 ld g_now; a0 = &g_s; jal diginet_session_wake
     0x13bbc a1 = want; s4 = 7 (the switch bound again); jal check_state_wake_code(rc, want)
     0x13bc8 j 0x1456c; a0 = 0; jal settle; the latch 0x14574.
   The model's case 5 (TModel/TOps.v LLVMFuzzerTestOneInput_op_m) fixes every callee's result; the cursor after the
   op is the cursor after the op byte (c1, s3 / s6 untouched). The invariant llvm_mem is carried by
   LLVMFuzzerTestOneInput_fr.v (llvm_mem_after_fill for the two memsets, llvm_mem_after_call for the stores, K = 0,
   and for the four callees). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TSess0 TCb TSess TOps TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  m_wake_c diginet_session_wake_c check_state_wake_code_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the model *)

(* The helper lemmas live in a module of their own, so that a file importing this one (the SR glue, the other op
   files) sees only llvm_op5_holds. *)
Module Op5Lib.

(* The model's case 5, cut at its calls (no injection on a world-carrying option: every world is a variable here). *)
Lemma op5_inv : forall I B A D c k B1 c2 k1,
  snd (fuzz_u8_m D c) mod 9 = 5 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c2, k1)) ->
  c2 = fst (fuzz_u8_m D c) /\
  exists Bb B2 want B3 rc B4,
    op_begin_m B = Some (Bb, tt) /\ m_wake_m Bb = Some (B2, want) /\
    diginet_session_wake_m I None B2 (g_now B2) = Some (B3, rc) /\
    check_state_wake_code_m B3 rc want = Some (B4, tt) /\ settle_m B4 0 = Some (B1, tt).
Proof.
  intros I B A D c k B1 c2 k1 Hop H.
  unfold LLVMFuzzerTestOneInput_op_m in H.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in Hop |- *.
  rewrite Hop in H. cbv beta iota zeta delta [Z.eqb Pos.eqb] in H.
  destruct (op_begin_m B) as [[Bb u]|] eqn:E1; cbv beta iota in H; [|discriminate H]. destruct u.
  destruct (m_wake_m Bb) as [[B2 want]|] eqn:E2; cbv beta iota in H; [|discriminate H].
  destruct (diginet_session_wake_m I None B2 (g_now B2)) as [[B3 rc]|] eqn:E3; cbv beta iota in H;
    [|discriminate H].
  destruct (check_state_wake_code_m B3 rc want) as [[B4 u]|] eqn:E4; cbv beta iota in H; [|discriminate H].
  destruct u.
  destruct (settle_m B4 0) as [[B5 u]|] eqn:E5; cbv beta iota in H; [|discriminate H]. destruct u.
  apply some_pair_inv in H. destruct H as [EB H]. subst B5.
  pose proof (f_equal fst H) as Ec. cbn [fst] in Ec.
  split; [symmetry; exact Ec|].
  exists Bb, B2, want, B3, rc, B4.
  split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. exact E5.
Qed.

(* op_begin (TCb.v:340-344), its world written out *)
Lemma op_begin_inv : forall B Bb, op_begin_m B = Some (Bb, tt) ->
  Bb = set_M_fail (set_OW_desk_off (upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) OFF_GOT
                                          (repeat (b8 0) (Z.to_nat SZ_GOT))) (-1))
         (g_fail_next (set_OW_desk_off (upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) OFF_GOT
                                              (repeat (b8 0) (Z.to_nat SZ_GOT))) (-1))).
Proof.
  intros B Bb H. unfold op_begin_m in H. cbv zeta in H.
  apply some_pair_inv in H. destruct H as [H _]. symmetry. exact H.
Qed.

(* m_wake's code is an int *)
Lemma m_wake_r_range : forall B B' r, m_wake_m B = Some (B', r) -> -2^31 <= r < 2^31.
Proof.
  intros B B' r H. unfold m_wake_m in H. gk_split H.
  all: apply some_pair_inv in H; destruct H as [_ <-]; unfold SPEC_E_ARG, SPEC_E_REFUSED, SPEC_OK, EIO; lia.
Qed.

(* check_state_wake_code passes only when rc = want, and keeps the world *)
Lemma cswc_eq : forall B B' rc want, check_state_wake_code_m B rc want = Some (B', tt) -> rc = want /\ B' = B.
Proof.
  intros B B' rc want H. unfold check_state_wake_code_m in H.
  destruct (Z.eqb_spec rc want) as [E|E]; cbn [negb] in H; [|discriminate H].
  apply some_pair_inv in H. destruct H as [H _]. split; [exact E | symmetry; exact H].
Qed.

(* the byte of g_fail_next outside a write *)
Lemma gfn_upd : forall X k v, length X = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd X k v) = g_fail_next X.
Proof.
  intros X k v HL Hk Hkv Hd. unfold g_fail_next.
  apply u_at_upd_out.
  - exact Hk.
  - unfold OFF_g_fail_next. lia.
  - change (Z.of_nat 1) with 1. destruct Hd as [Hd|Hd]; [right; exact Hd | left; exact Hd].
  - rewrite HL, Z2Nat.id by (unfold W_LEN; lia). exact Hkv.
Qed.

Lemma len_upd_w : forall X k v, length X = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd X k v) = Z.to_nat W_LEN.
Proof.
  intros X k v HL Hk Hkv. rewrite length_upd; [exact HL | exact Hk |].
  rewrite HL, Z2Nat.id by (unfold W_LEN; lia). exact Hkv.
Qed.

(* op_begin keeps g_fail_next and the length of the world *)
Lemma op_begin_gk : forall B Bb, length B = Z.to_nat W_LEN -> op_begin_m B = Some (Bb, tt) -> gkeep B Bb.
Proof.
  intros B Bb HL H. rewrite (op_begin_inv B Bb H). pose proof (len_w B HL) as HLz.
  unfold set_M_fail, set_OW_desk_off.
  assert (L1 : Z.of_nat (length (repeat (b8 0) (Z.to_nat SZ_OW))) = 304)
    by (rewrite repeat_length; reflexivity).
  assert (L2 : Z.of_nat (length (repeat (b8 0) (Z.to_nat SZ_GOT))) = 224)
    by (rewrite repeat_length; reflexivity).
  assert (L4 : forall v, Z.of_nat (length (put 4 v)) = 4) by (intros v; rewrite length_put; reflexivity).
  apply gkeep_upd; [| unfold A_M_fail, OFF_M; lia | rewrite L4, HLz; unfold A_M_fail, OFF_M, W_LEN; lia
                    | left; rewrite L4; unfold A_M_fail, OFF_M, OFF_g_fail_next; lia].
  apply gkeep_upd; [| unfold A_OW_desk_off, OFF_OW; lia
                    | rewrite L4, HLz; unfold A_OW_desk_off, OFF_OW, W_LEN; lia
                    | right; unfold A_OW_desk_off, OFF_OW, OFF_g_fail_next; lia].
  apply gkeep_upd; [| unfold OFF_GOT; lia | rewrite L2, HLz; unfold OFF_GOT, W_LEN; lia
                    | right; unfold OFF_GOT, OFF_g_fail_next; lia].
  apply gkeep_upd; [| unfold OFF_OW; lia | rewrite L1, HLz; unfold OFF_OW, W_LEN; lia
                    | right; unfold OFF_OW, OFF_g_fail_next; lia].
  apply gkeep_refl.
Qed.

(* op_begin's last two writes as the machine does them (0x13b94-0x13ba0, the model's order): OW.desk_off = -1 at
   65544, then M.fail at 88 with the g_fail_next byte read before; the first write misses that byte. *)
Lemma op5_world : forall X, length X = Z.to_nat W_LEN ->
  upd (upd X 65544 (put 4 (-1))) 88 (put 4 (u_at X 64968 1))
  = set_M_fail (set_OW_desk_off X (-1)) (g_fail_next (set_OW_desk_off X (-1))).
Proof.
  intros X HL. unfold set_M_fail, set_OW_desk_off.
  rewrite (gfn_upd X A_OW_desk_off (put 4 (-1)) HL);
    [| unfold A_OW_desk_off, OFF_OW; lia | rewrite length_put; unfold A_OW_desk_off, OFF_OW, W_LEN; lia
     | right; unfold A_OW_desk_off, OFF_OW, OFF_g_fail_next; lia].
  reflexivity.
Qed.

(* the cursor after the op byte *)
Lemma cursor_u8 : forall D c, llvm_cursor D c -> fi_n c <> 0 -> llvm_cursor D (fst (fuzz_u8_m D c)).
Proof.
  intros D c (H1 & H2 & H3) HN. unfold llvm_cursor, fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|E]; [contradiction|]. cbn [fst fi_off fi_n]. lia.
Qed.

End Op5Lib.
Import Op5Lib.

(* ---------------------------------------------------------------- the walk *)

Local Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* the memory facts a step or a call needs, read off llvm_mem *)
Local Ltac lm_get HM ST MI RR WM :=
  let H := fresh "HMx" in pose proof HM as H; unfold llvm_mem in H;
  destruct H as (_ & _ & _ & _ & _ & ST & _ & _ & _ & MI & RR & WM & _).

Theorem llvm_op5_holds : memset_contract -> m_wake_contract -> diginet_session_wake_contract ->
  check_state_wake_code_contract -> settle_contract -> llvm_op_stmt 5.
Proof.
  intros MSET MWAKE SWAKE CSWC SETTLE.
  unfold memset_contract, MEMSET in MSET.
  unfold m_wake_contract, m_wake_ENTRY, m_wake_FRAME in MWAKE.
  unfold diginet_session_wake_contract, diginet_session_wake_ENTRY, diginet_session_wake_FRAME in SWAKE.
  unfold check_state_wake_code_contract, check_state_wake_code_ENTRY, check_state_wake_code_FRAME in CSWC.
  unfold settle_contract, settle_ENTRY, settle_FRAME in SETTLE.
  unfold llvm_op_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms A k B1 c2 k1 HC HOP.
  destruct HC as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                  m & j10 & jio & j60 & -> & HOPS & HN & HCUR & HC1 & HMOD & HM).
  destruct (op5_inv timg_ubsan B A D c k B1 c2 k1 HMOD HOP)
    as (Hc2 & Bb & B2 & want & B3 & rc & B4 & E1 & E2 & E3 & E4 & E5).
  clear HOP HMOD.
  rewrite Hc2, <- HC1. clear Hc2 c2.
  (* numeric facts of the invariant *)
  pose proof HM as HMx. unfold llvm_mem in HMx.
  destruct HMx as (_ & _ & _ & _ & HSP & _ & HLO & HSP2 & HWL & _ & _ & HWM0 & HFN & _).
  pose proof (wm_len _ _ _ _ HWM0) as LB. clear HWM0.
  assert (NLO : 275280 <= lo) by (unfold W_BASE_UBSAN, W_LEN in HWL; lia).
  assert (NSP : lo + 9936 <= Sp) by (unfold LH_K in HLO; lia).
  assert (NSP2 : Sp + 240 <= 2 ^ 63) by (unfold LH_FRAME in HSP2; lia).
  clear HLO HSP2 HWL.
  assert (USP : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  (* the registers that hold world addresses, as literals *)
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312).
  change (LH_CASE 5) with 0x13b74.
  (* ---- 0x13b74 memset(&OW, 0, 0x130) ---- *)
  lm_get HM ST MI RR WM. clear RR.
  step. step. step. step.                      (* addi a0, s9, 0x158; li a2, 0x130; li a1, 0; jal memset *)
  assert (DST : rw_cells rsegs m (W_BASE_UBSAN + OFF_OW) [CB (Z.to_nat SZ_OW) (sub B OFF_OW (Z.to_nat SZ_OW))])
    by (apply (wm_piece rsegs W_BASE_UBSAN m B OFF_OW SZ_OW);
        [exact WM | reflexivity | unfold OFF_OW; lia | unfold SZ_OW; lia | unfold OFF_OW, SZ_OW, W_LEN; lia]).
  eapply evt_cut.
  { eapply (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
               (sub B OFF_OW (Z.to_nat SZ_OW))); [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 &
                  -> & MU1 & WMO1 & MI1 & CZ1).
  assert (HM1 : llvm_mem data D regs0 m0 Sp lo (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) m1 j10 jio j60).
  { apply (llvm_mem_after_fill data D regs0 m0 Sp lo B m m1 OFF_OW SZ_OW (repeat (b8 0) (Z.to_nat SZ_OW))
             j10 jio j60 HM MU1 WMO1 MI1 CZ1);
      [unfold OFF_OW; lia | unfold SZ_OW; lia | unfold OFF_OW, SZ_OW, W_LEN; lia |].
    rewrite (gfn_upd B OFF_OW _ LB); [exact HFN | unfold OFF_OW; lia
      | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia
      | right; unfold OFF_OW, OFF_g_fail_next; lia]. }
  clear HM DST MU1 WMO1 MI1 CZ1 ST MI WM.
  set (Ba := upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) in *.
  assert (LBa : length Ba = Z.to_nat W_LEN)
    by (apply len_upd_w; [exact LB | unfold OFF_OW; lia | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia]).
  assert (FBa : g_fail_next Ba = g_fail_next B)
    by (apply gfn_upd; [exact LB | unfold OFF_OW; lia | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia
                       | right; unfold OFF_OW, OFF_g_fail_next; lia]).
  (* ---- 0x13b84 memset(&GOT, 0, 0xe0) ---- *)
  fix_ret.
  lm_get HM1 ST MI RR WM. clear RR.
  step. step. step. step.                      (* addi a0, s9, 0x74; li a2, 0xe0; li a1, 0; jal memset *)
  assert (DST : rw_cells rsegs m1 (W_BASE_UBSAN + OFF_GOT)
                  [CB (Z.to_nat SZ_GOT) (sub Ba OFF_GOT (Z.to_nat SZ_GOT))])
    by (apply (wm_piece rsegs W_BASE_UBSAN m1 Ba OFF_GOT SZ_GOT);
        [exact WM | reflexivity | unfold OFF_GOT; lia | unfold SZ_GOT; lia | unfold OFF_GOT, SZ_GOT, W_LEN; lia]).
  eapply evt_cut.
  { eapply (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
               (sub Ba OFF_GOT (Z.to_nat SZ_GOT))); [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 &
                  -> & MU2 & WMO2 & MI2 & CZ2).
  assert (HM2 : llvm_mem data D regs0 m0 Sp lo (upd Ba OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT))) m2
                  j10 jio j60).
  { apply (llvm_mem_after_fill data D regs0 m0 Sp lo Ba m1 m2 OFF_GOT SZ_GOT (repeat (b8 0) (Z.to_nat SZ_GOT))
             j10 jio j60 HM1 MU2 WMO2 MI2 CZ2);
      [unfold OFF_GOT; lia | unfold SZ_GOT; lia | unfold OFF_GOT, SZ_GOT, W_LEN; lia |].
    rewrite (gfn_upd Ba OFF_GOT _ LBa); [rewrite FBa; exact HFN | unfold OFF_GOT; lia
      | rewrite repeat_length; unfold OFF_GOT, SZ_GOT, W_LEN; lia
      | right; unfold OFF_GOT, OFF_g_fail_next; lia]. }
  clear HM1 DST MU2 WMO2 MI2 CZ2 ST MI WM.
  set (Bx := upd Ba OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT))) in *.
  assert (LBx : length Bx = Z.to_nat W_LEN)
    by (apply len_upd_w; [exact LBa | unfold OFF_GOT; lia | rewrite repeat_length; unfold OFF_GOT, SZ_GOT, W_LEN; lia]).
  assert (FBx : g_fail_next Bx = g_fail_next B)
    by (rewrite <- FBa; apply gfn_upd; [exact LBa | unfold OFF_GOT; lia
                       | rewrite repeat_length; unfold OFF_GOT, SZ_GOT, W_LEN; lia
                       | right; unfold OFF_GOT, OFF_g_fail_next; lia]).
  (* ---- 0x13b94 lbu a0, g_fail_next; li a1, -1; sw a1, OW.desk_off; sw a0, M.fail ---- *)
  fix_ret.
  lm_get HM2 ST MI RR WM. clear RR.
  pose proof (munch_refl [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m2) as MUs.
  pose proof (wmono_refl rsegs m2) as WMOs.
  step. step. step. step.                      (* the world is now op_begin's, written as the machine wrote it *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  destruct (op_begin_gk B Bb LB E1) as [LBb GBb].
  assert (EW : Bb = upd (upd Bx 65544 (put 4 (-1))) 88 (put 4 (u_at Bx 64968 1)))
    by (rewrite (op_begin_inv B Bb E1); symmetry; exact (op5_world Bx LBx)).
  lazymatch goal with H : rw_cells rsegs m3 W_BASE_UBSAN [CB _ _] |- _ => rewrite <- EW in H; rename H into WMs end.
  assert (HM3 : llvm_mem data D regs0 m0 Sp lo Bb m3 j10 jio j60).
  { apply (llvm_mem_after_call data D regs0 m0 Sp lo 0 Bx Bb m2 m3 j10 jio j60 HM2);
      [unfold LH_K; lia | | exact WMOs | exact MI | exact ST | exact WMs | rewrite GBb; exact HFN].
    replace (Sp - 0) with Sp by lia.
    exact (lh_munch_span_in_world W_BASE_UBSAN W_LEN m2 m3 MUs ltac:(lia) ltac:(lia) Sp). }
  clear HM2 MUs WMOs ST MI WMs EW.
  (* ---- 0x13ba4 jal m_wake: want in a0 ---- *)
  lm_get HM3 ST MI RR WM. clear RR.
  step.
  eapply evt_cut.
  { eapply (MWAKE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo Bb B2 want);
      [ rewrite USP; exact HSP | rewrite USP; exact ST | rewrite USP; lia
      | unfold w_off_stack; rewrite USP; unfold W_BASE_UBSAN, W_LEN; lia | exact MI | exact WM | exact E2 ]. }
  intros ms' PO.
  destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 &
                  -> & MU4 & WMO4 & MI4 & ST4 & WM4).
  rewrite USP in MU4, ST4.
  destruct (m_wake_gk B LB Bb B2 want (op_begin_gk B Bb LB E1) E2) as [LB2 GB2].
  assert (HM4 : llvm_mem data D regs0 m0 Sp lo B2 m4 j10 jio j60)
    by (apply (llvm_mem_after_call data D regs0 m0 Sp lo 16 Bb B2 m3 m4 j10 jio j60 HM3);
        [unfold LH_K; lia | exact MU4 | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | rewrite GB2; exact HFN]).
  clear HM3 MU4 WMO4 MI4 ST4 WM4 ST MI WM.
  (* ---- 0x13ba8 ld a1, g_now; mv s4, a0; a0 = &g_s; jal diginet_session_wake: rc in a0 ---- *)
  fix_ret.
  lm_get HM4 ST MI RR WM.
  step.
  change (u_at B2 65000 8) with (g_now B2).
  step. step. step. step.
  assert (HNOW : 0 <= g_now B2 < 2 ^ 64).
  { pose proof (u_at_range B2 OFF_g_now 8) as R. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. exact R. }
  eapply evt_cut.
  { eapply (SWAKE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4 lo (g_now B2) rc B2 B3 None);
      [ reflexivity | reflexivity | exact HNOW | exact WM | rewrite GB2; exact HFN | exact E3 | exact I | exact RR
      | rewrite USP; exact HSP | rewrite USP; exact ST | rewrite USP; lia
      | unfold w_off_stack; rewrite USP; unfold W_BASE_UBSAN, W_LEN; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 &
                  -> & MU5 & WMO5 & MI5 & ST5 & WM5 & GF5).
  rewrite USP in MU5, ST5.
  assert (HM5 : llvm_mem data D regs0 m0 Sp lo B3 m5 j10 jio j60)
    by (apply (llvm_mem_after_call data D regs0 m0 Sp lo 752 B2 B3 m4 m5 j10 jio j60 HM4);
        [unfold LH_K; lia | exact MU5 | exact WMO5 | exact MI5 | exact ST5 | exact WM5 | exact GF5]).
  clear HM4 MU5 WMO5 MI5 ST5 WM5 ST MI RR WM.
  (* ---- 0x13bbc mv a1, s4; li s4, 7; jal check_state_wake_code (rc = want: both ints) ---- *)
  fix_ret.
  lm_get HM5 ST MI RR WM. clear RR.
  step. step. step.
  destruct (cswc_eq B3 B4 rc want E4) as [Erc EB4].
  pose proof (m_wake_r_range Bb B2 want E2) as Rw.
  eapply evt_cut.
  { eapply (CSWC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 lo B3 B4 rc want);
      [ reflexivity | reflexivity | rewrite Erc; exact Rw | exact Rw | exact WM | exact E4
      | rewrite USP; exact HSP | rewrite USP; exact ST | rewrite USP; lia
      | unfold w_off_stack; rewrite USP; unfold W_BASE_UBSAN, W_LEN; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m6 &
                  -> & MU6 & WMO6 & MI6 & ST6 & _ & WM6).
  rewrite USP in MU6, ST6.
  subst B4.
  assert (HM6 : llvm_mem data D regs0 m0 Sp lo B3 m6 j10 jio j60)
    by (apply (llvm_mem_after_call data D regs0 m0 Sp lo 16 B3 B3 m5 m6 j10 jio j60 HM5);
        [unfold LH_K; lia | apply lh_munch_add_world; exact MU6 | exact WMO6 | exact MI6 | exact ST6 | exact WM6
        | exact GF5]).
  clear HM5 MU6 WMO6 MI6 ST6 WM6 ST MI WM.
  (* ---- 0x13bc8 j 0x1456c; 0x1456c mv a0, zero; 0x14570 jal settle ---- *)
  fix_ret.
  lm_get HM6 ST MI RR WM. clear RR.
  step. step. step.
  eapply evt_cut.
  { eapply (SETTLE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m6 lo B3 B1 0);
      [ reflexivity | lia | exact WM | exact E5
      | rewrite USP; exact HSP | rewrite USP; exact ST | rewrite USP; lia
      | unfold w_off_stack; rewrite USP; unfold W_BASE_UBSAN, W_LEN; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m7 &
                  -> & MU7 & WMO7 & MI7 & ST7 & EB1 & WM7).
  rewrite USP in MU7, ST7.
  subst B1.
  assert (HM7 : llvm_mem data D regs0 m0 Sp lo B3 m7 j10 jio j60)
    by (apply (llvm_mem_after_call data D regs0 m0 Sp lo 96 B3 B3 m6 m7 j10 jio j60 HM6);
        [unfold LH_K; lia | apply lh_munch_add_world; exact MU7 | exact WMO7 | exact MI7 | exact ST7 | exact WM7
        | exact GF5]).
  (* ---- 0x14574: the latch, with the cursor after the op byte ---- *)
  fix_ret.
  apply evt_done. unfold llvm_latch. do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [rewrite HC1; apply cursor_u8; [exact HCUR | exact HN]|].
  exact HM7.
Qed.
