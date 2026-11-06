(* Case 4 of the ubsan LLVMFuzzerTestOneInput (op_submit inlined, fuzz_transport.c:1068-1122): the interface between
   the prefix / raw path (LLVMFuzzerTestOneInput_op4.v, _op4_pre.v, _op4_raw.v) and the tagged path
   (_op4_tag.v). The tagged path starts at 0x141a4 (`lw s0, 0x10(s9)`, g_ncmd), reached from 0x13fc0 and 0x14198
   after `sd s0, 0x18(sp)` (before = s->queued) and the cursor moves in s4 / s7.

   - op4_raw_m / op4_tagged_m: the two arms of op_submit_m (TOps.v:226-275) after op_begin and the three bytes
     kb, ab, db; op_submit_split states op_submit_m through them (by conversion).
   - llvm_op4_mid: the machine at 0x141a4. Registers: s1 = 1, s4 = the cursor's n, s7 = its address, s8 / s9 / s10 /
     s11 as at the loop head (s10 = &g_s), gp / tp the entry's; s0, s2, s3, s5, s6, a0-a7, t0-t6, ra free. Memory:
     llvm_mem with the world B1 (op_begin_m's), sp+0x18 = the 8 bytes of (int)before sign-extended, the 32-byte
     struct diginet_cmd at sp+0x60 = cmd_struct (24 zero bytes) 0 display key, the 8 bytes after it free.
   - llvm_op4_tag_stmt: the tagged path's statement (0x141a4 .. the latch 0x14574).
   - rw_cells_app, llvm_frame_close: splitting / joining a frame's cells, and folding a frame of finer cells back
     into llvm_frame; llvm_mem_store_frame: llvm_mem after stores / a callee confined to the loop's own frame.
   - submit_gfn, submit_rc: diginet_session_submit_m keeps g_fail_next and returns a small int. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* the option monad of TOps.v *)
Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* ---------------------------------------------------------------- the model's two arms *)

(* fuzz_transport.c:1078-1083, op_submit_m's raw arm (g_raw != 0): B1 = op_begin_m's world, c3 = the cursor after
   the three bytes, before = S_queued of the world op_submit started from. *)
Definition op4_raw_m (B1 D : list byte) (c3 : fuzz_in) (before display key : Z) : option (list byte * fuzz_in) :=
    let (c4, w) := fuzz_u16_m D c3 in
    let '(c5, off, t) := fuzz_take_m c4 (w mod (SPEC_CMD_MAX + 1)) in
    let len := t mod 2^8 in
    let cbytes := sub D off (Z.to_nat len) ++ repeat (b8 0) (Z.to_nat (24 - len)) in
    let cs := cmd_struct cbytes len display key in
    let? (B2, rc) := diginet_session_submit_m B1 cs in
    let? (B3, _) := check_refusal_submit_m B2 cs rc before in
    let? (B4, _) := settle_m B3 0 in
    Some (B4, c5).

(* fuzz_transport.c:1085-1121, op_submit_m's tagged arm (g_raw == 0). *)
Definition op4_tagged_m (B1 D : list byte) (c3 : fuzz_in) (before display key : Z) : option (list byte * fuzz_in) :=
    let serial := g_ncmd B1 in
    if CMDS_MAX <=? serial then None
    else
    let B2 := upd B1 (A_Cmd_st serial) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) in
    let (c4, lb) := fuzz_u8_m D c3 in
    let len := lb mod 22 + 3 in
    let '(c5, off, n) := fuzz_take_m c4 (len - 3) in
    let cbytes := [b8 TAG; b8 (Z.land serial 0x7f); b8 (Z.land (Z.shiftr serial 7) 0x7f)]
                  ++ sub D off (Z.to_nat n) ++ repeat (b8 0) (Z.to_nat (21 - n)) in
    let sys := system_at (firstn (Z.to_nat len) cbytes) in
    let? at_ :=
      if negb (h_coalescable_m key =? 0)
      then submit_find_at (S (Z.to_nat CMDS_MAX)) B2 key 0
      else Some (-1) in
    let want := if sys then SPEC_E_REFUSED
                else if (at_ <? 0) && (g_nq B2 =? QUEUE_MAX) then SPEC_E_SPACE
                else SPEC_OK in
    let cs := cmd_struct cbytes len display key in
    let? (B3, rc) := diginet_session_submit_m B2 cs in
    let? (B4, _) := check_refusal_submit_m B3 cs rc before in
    let? (B5, _) := if sys then Some (B4, tt) else check_latest_submit_m B4 rc want in
    let? B6 :=
      if want =? SPEC_OK then
        let Bw := set_Cmd_bytes
                    (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 serial PENDING) serial key)
                                    serial display) serial len)
                    serial (firstn (Z.to_nat len) cbytes) in
        if 0 <=? at_ then
          let q := Q_at Bw at_ in
          if CMDS_MAX <=? q then None
          else Some (set_Q_at (set_Cmd_st Bw q REPLACED) at_ serial)
        else
          let nq := g_nq Bw in
          if CMDS_MAX <=? nq then None
          else Some (set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2^32))
      else Some B5 in
    let B7 := set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2^32) in
    let? (B8, _) := settle_m B7 0 in
    Some (B8, c5).

Lemma op_submit_split : forall B D c, op_submit_m B D c =
  match op_begin_m B with
  | Some (B1, _) =>
      let (c1, kb) := fuzz_u8_m D c in
      let (c2, ab) := fuzz_u8_m D c1 in
      let (c3, db) := fuzz_u8_m D c2 in
      if negb (g_raw B1 =? 0) then op4_raw_m B1 D c3 (S_queued B) (Z.land db 1) (KEY (kb mod 9 + 1) ab)
      else op4_tagged_m B1 D c3 (S_queued B) (Z.land db 1) (KEY (kb mod 9 + 1) ab)
  | None => None
  end.
Proof. intros B D c. reflexivity. Qed.

(* ---------------------------------------------------------------- the machine at 0x141a4 *)

Definition LH_OP4_MID : Z := 0x141a4.

Definition llvm_op4_mid (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops before : Z) (c3 : fuzz_in) (B1 : list byte) (display key : Z)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jlo jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (fi_n c3)) s5 s6 (Z_to_bv 64 (data + fi_off c3))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LH_OP4_MID) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor D c3 /\
    0 <= before < 2 ^ 32 /\ 0 <= display <= 1 /\ 0 <= key < 2 ^ 32 /\
    length jlo = 8%nat /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B1 m (jlo ++ le8 (Z_to_bv 64 (bv_swrap 32 before))) jio
      (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi).

(* The tagged path, 0x141a4 .. the latch 0x14574 (its settle(0) at 0x14570 included). *)
Definition llvm_op4_tag_stmt : Prop :=
  forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms B8 c5,
    llvm_op4_mid data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
    op4_tagged_m B1 D c3 before display key = Some (B8, c5) ->
    evt rsegs (llvm_latch data D regs0 m0 Sp lo ops c5 B8 F fc) ms.

(* ---------------------------------------------------------------- small model facts *)

(* the inversion of a pair option, by name (never injection on a world) *)
Lemma opt_pair_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a' = a /\ b' = b.
Proof. intros X Y a a' b b' H. inversion H. split; reflexivity. Qed.

Lemma submit_find_m_lt : forall B key fuel j i, submit_find_m B key j fuel = Some (Some i) -> j <= i < S_queue_N.
Proof.
  intros B key fuel. induction fuel as [|f IH]; intros j i H; cbn [submit_find_m] in H; [discriminate|].
  destruct (S_queue_N <=? j) eqn:E1; [discriminate|]. apply Z.leb_gt in E1.
  destruct (S_queue_key B j =? key).
  - injection H as <-. lia.
  - apply IH in H. lia.
Qed.

Lemma submit_gf_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next -> g_fail_next (upd B k v) = g_fail_next B /\ length (upd B k v) = length B.
Proof.
  intros B v k LB Hk Hv. split.
  - unfold g_fail_next. apply u_at_upd_out; rewrite ?LB; unfold OFF_g_fail_next, W_LEN in *; lia.
  - apply length_upd; [exact Hk|]. rewrite LB. unfold OFF_g_fail_next, W_LEN in *; lia.
Qed.

(* destructs the condition of the if a hypothesis H : (if b then _ else _) = _ starts with *)
Ltac dest_if H := lazymatch type of H with (if ?b then _ else _) = _ => destruct b end.

(* diginet_session_submit writes only g_s (its queue, s->queued, two counters) *)
Lemma submit_gfn : forall B c B' r, length B = Z.to_nat W_LEN -> length c = 32%nat ->
  diginet_session_submit_m B c = Some (B', r) -> g_fail_next B' = g_fail_next B.
Proof.
  intros B c B' r LB LC H. unfold diginet_session_submit_m in H. cbv zeta in H.
  dest_if H.
  { apply opt_pair_inv in H. destruct H as [-> _]. reflexivity. }
  dest_if H.
  { apply opt_pair_inv in H. destruct H as [-> _]. unfold set_S_stats_refused.
    apply submit_gf_upd; [exact LB | unfold A_S_stats_refused, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_refused, OFF_g_s, OFF_g_fail_next; cbn; lia]. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|] eqn:EF; [| |discriminate H].
  - apply opt_pair_inv in H. destruct H as [-> _].
    assert (Hi : 0 <= i < S_queue_N).
    { destruct (coalescable_m (cmd_key_of c) =? 0); [discriminate EF|]. apply submit_find_m_lt in EF. lia. }
    unfold S_queue_N in Hi.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes i) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes i) c) = length B).
    { apply submit_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_stats_coalesced. rewrite <- G1.
    apply submit_gf_upd; [rewrite L1; exact LB | unfold A_S_stats_coalesced, OFF_g_s; lia |
      rewrite length_put; unfold A_S_stats_coalesced, OFF_g_s, OFF_g_fail_next; cbn; lia].
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply opt_pair_inv in H. destruct H as [-> _]. reflexivity. }
    destruct (S_queue_N <=? S_queued B) eqn:EQ; [discriminate H|]. apply Z.leb_gt in EQ.
    apply opt_pair_inv in H. destruct H as [-> _].
    pose proof (u_at_range B A_S_queued 4) as RQ. change (u_at B A_S_queued 4) with (S_queued B) in RQ.
    unfold S_queue_N in EQ.
    assert (GL : g_fail_next (upd B (A_S_queue_bytes (S_queued B)) c) = g_fail_next B /\
                 length (upd B (A_S_queue_bytes (S_queued B)) c) = length B).
    { apply submit_gf_upd; [exact LB | unfold A_S_queue_bytes, OFF_g_s; lia |
        rewrite LC; unfold A_S_queue_bytes, OFF_g_s, OFF_g_fail_next; lia]. }
    destruct GL as [G1 L1].
    unfold set_S_queued. rewrite <- G1.
    apply submit_gf_upd; [rewrite L1; exact LB | unfold A_S_queued, OFF_g_s; lia |
      rewrite length_put; unfold A_S_queued, OFF_g_s, OFF_g_fail_next; cbn; lia].
Qed.

(* its return value is one of 0, -1, -5, -10 *)
Ltac rc_small := cbv [DIGINET_E_ARG DIGINET_E_SPACE DgnLib.DIGINET_E_REFUSED DgnLib.DIGINET_OK]; lia.
Lemma submit_rc : forall B c B' r, diginet_session_submit_m B c = Some (B', r) -> -10 <= r <= 0.
Proof.
  intros B c B' r H. unfold diginet_session_submit_m in H. cbv zeta in H.
  dest_if H.
  { apply opt_pair_inv in H. destruct H as [_ ->]. rc_small. }
  dest_if H.
  { apply opt_pair_inv in H. destruct H as [_ ->]. rc_small. }
  destruct (if coalescable_m (cmd_key_of c) =? 0 then Some None else submit_find_m B (cmd_key_of c) 0 (Z.to_nat (S_queued B)))
    as [[i|]|]; [| |discriminate H].
  - apply opt_pair_inv in H. destruct H as [_ ->]. rc_small.
  - destruct (S_queued B =? DIGINET_QUEUE_MAX).
    { apply opt_pair_inv in H. destruct H as [_ ->]. rc_small. }
    destruct (S_queue_N <=? S_queued B); [discriminate H|].
    apply opt_pair_inv in H. destruct H as [_ ->]. rc_small.
Qed.

(* ---------------------------------------------------------------- frame cells *)

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_bytes_app, cells_size_app. split.
  - intros [[HWF HB] (Ha & Hn & HW)].
    apply (proj1 (cells_wf_app cs1 cs2)) in HWF. destruct HWF as [W1 W2].
    apply (proj1 (bytes_at_app rsegs m A (cells_bytes cs1) (cells_bytes cs2))) in HB. destruct HB as [HB1 HB2].
    rewrite (cells_bytes_length cs1 W1) in HB2.
    split; split; [split; [exact W1 | exact HB1] | | split; [exact W2 | exact HB2] |].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply HW. lia.
  - intros [[[W1 HB1] (Ha & Hn & HW1)] [[W2 HB2] (Ha2 & Hn2 & HW2)]].
    split; [split|].
    + apply (proj2 (cells_wf_app cs1 cs2)). split; [exact W1 | exact W2].
    + apply (proj2 (bytes_at_app rsegs m A (cells_bytes cs1) (cells_bytes cs2))).
      split; [exact HB1|]. rewrite (cells_bytes_length cs1 W1). exact HB2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L].
      * apply HW1. lia.
      * replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
        apply HW2. lia.
Qed.

Lemma rw_cells_wf : forall m A cs, rw_cells rsegs m A cs -> cells_wf cs.
Proof. intros m A cs [[W _] _]. exact W. Qed.

(* a frame of finer cells folds back into llvm_frame: the cells of [sp+0x10, sp+0x20), [sp+0x40, sp+0x60) and
   [sp+0x60, sp+0x88) become the three byte lists *)
Lemma llvm_frame_close : forall regs0 m Sp c10 cio c60,
  cells_size c10 = 16%nat -> cells_size cio = 32%nat -> cells_size c60 = 40%nat ->
  rw_cells rsegs m Sp
    ([C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))] ++ c10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
      C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))] ++ cio ++ c60 ++
     llvm_saved regs0) ->
  rw_cells rsegs m Sp (llvm_frame regs0 Sp (cells_bytes c10) (cells_bytes cio) (cells_bytes c60)) /\
  length (cells_bytes c10) = 16%nat /\ length (cells_bytes cio) = 32%nat /\ length (cells_bytes c60) = 40%nat.
Proof.
  intros regs0 m Sp c10 cio c60 S10 Sio S60 H.
  pose proof (rw_cells_wf m Sp _ H) as WF.
  apply (proj1 (cells_wf_app _ _)) in WF. destruct WF as [_ WF].
  apply (proj1 (cells_wf_app _ _)) in WF. destruct WF as [W10 WF].
  apply (proj1 (cells_wf_app _ _)) in WF. destruct WF as [_ WF].
  apply (proj1 (cells_wf_app _ _)) in WF. destruct WF as [Wio WF].
  apply (proj1 (cells_wf_app _ _)) in WF. destruct WF as [W60 _].
  split; [| rewrite (cells_bytes_length c10 W10), (cells_bytes_length cio Wio), (cells_bytes_length c60 W60);
            split; [exact S10|]; split; [exact Sio | exact S60]].
  set (P1 := [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3))]) in *.
  set (P2 := [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
              C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))]) in *.
  set (S := llvm_saved regs0) in *.
  replace (P1 ++ c10 ++ P2 ++ cio ++ c60 ++ S) with ((P1 ++ c10 ++ P2 ++ cio) ++ c60 ++ S) in H
    by (rewrite <- !app_assoc; reflexivity).
  apply (rw_cells_merge rsegs m Sp (P1 ++ c10 ++ P2 ++ cio) c60 S) in H.
  replace ((P1 ++ c10 ++ P2 ++ cio) ++ CB (cells_size c60) (cells_bytes c60) :: S)
    with ((P1 ++ c10 ++ P2) ++ cio ++ CB (cells_size c60) (cells_bytes c60) :: S) in H
    by (rewrite <- !app_assoc; reflexivity).
  apply (rw_cells_merge rsegs m Sp (P1 ++ c10 ++ P2) cio _) in H.
  replace ((P1 ++ c10 ++ P2) ++ CB (cells_size cio) (cells_bytes cio) :: CB (cells_size c60) (cells_bytes c60) :: S)
    with (P1 ++ c10 ++ P2 ++ CB (cells_size cio) (cells_bytes cio) :: CB (cells_size c60) (cells_bytes c60) :: S) in H
    by (rewrite <- !app_assoc; reflexivity).
  apply (rw_cells_merge rsegs m Sp P1 c10 _) in H.
  rewrite S10, Sio, S60 in H.
  exact H.
Qed.

(* llvm_mem after writes confined to the loop's own frame [Sp, Sp + 240) (stack stores, a memcpy into sp+0x60):
   the frame's three scratch lists are the ones the new frame cell gives; everything else is carried. *)
Lemma llvm_mem_store_frame : forall data D regs0 m0 Sp lo B m m' j10 jio j60 j10' jio' j60',
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(Sp, Sp + LH_FRAME)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' Sp (llvm_frame regs0 Sp j10' jio' j60') ->
  length j10' = 16%nat -> length jio' = 32%nat -> length j60' = 40%nat ->
  llvm_mem data D regs0 m0 Sp lo B m' j10' jio' j60'.
Proof.
  intros data D regs0 m0 Sp lo B m m' j10 jio j60 j10' jio' j60' HM MU WMO MI HRW' L1 L2 L3.
  unfold llvm_mem in HM |- *.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  assert (MUw : munch [(Sp, Sp + 240); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m')
    by (apply lh_munch_add_world; exact MU).
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HOW|].
  split.
  { eapply bytes_at_transport; [exact HD | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact HSP|].
  split.
  { eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact HLO|]. split; [exact HSP2|]. split; [exact HWL|].
  split; [exact MI|].
  split; [eapply lh_relro_munch; [exact HRO | exact MUw | lia]|].
  split.
  { eapply rw_cells_transport; [exact HWM | exact MU | exact WMO |].
    cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (unfold W_LEN; lia).
    unfold W_BASE_UBSAN, W_LEN in *. split; [lia | exact I]. }
  split; [exact HFN|].
  split.
  { eapply munch_trans; [exact HMU|]. eapply munch_weaken; [|exact MU].
    intros x Hx. cbn [outside] in *. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ HWMO WMO)|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  exact HRW'.
Qed.
