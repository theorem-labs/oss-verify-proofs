(* The premises of the library contracts hold at real call states of fuzz_wire (ubsan 6e91fe0b5555): one closed lemma per
   contract, at one call site, with the caller's register values and a memory of the shape the caller has there.
   The memory: the fuzz_dup heap block holding the frame at SAT_F, the stack window [SAT_LO, SAT_HI) mapped (zero
   bytes), and the loaded image everywhere else (mrd reads seg_rom where the overlay holds nothing). The image's
   segments end below 0x50000 (last PT_LOAD 0x1e318 + 0x30e40), so neither the heap block nor the stack meets them.
   The frame: a 2-channel REAC audio frame of 124 bytes (52 + 2 * 36; EtherType 0x8819 at bytes 12-13, frame type
   00 00 at bytes 16-17), as LLVMFuzzerTestOneInput passes it on for an input of 125 bytes.
   The sp of every lemma follows the one convention of the fuzz_wire sat lemmas: SAT_SP =
   0x7fffffffe700 is LLVMFuzzerTestOneInput's ENTRY sp, and each callee's entry sp is its caller's entry sp minus the
   caller's frame size at that call, read from the disassembly (the `addi sp, sp, -N` of each prologue). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Image.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c
  rp_slot_width_c reac_frame_is_reac_c rp_slot_read_c.
Import ListNotations.
Open Scope Z_scope.

Definition SAT_HI : Z := 0x7ffffffff700.
Definition SAT_LO : Z := SAT_HI - 0x10000.
Definition SAT_SP : Z := SAT_HI - 0x1000.
Definition SAT_F : Z := 0x100000.

(* Entry sps under the convention (frame sizes: LLVMFuzzerTestOneInput 0x40 at 0x12dc0, check_width 0x10 at
   0x1328c, check_read 0xa0 at 0x13300, rp_slot_read 0x50 at 0x13acc). *)
Definition SAT_CHK_SP : Z := SAT_SP - 0x40.      (* every check_*'s entry sp: 0x7fffffffe6c0 *)
Definition SAT_FC_SP : Z := SAT_CHK_SP - 0x10.   (* rp_frame_channels's entry sp at check_width's call: 0x7fffffffe6b0 *)
Definition SAT_SR_SP : Z := SAT_CHK_SP - 0xa0.   (* rp_slot_read's entry sp at check_read's call: 0x7fffffffe620;
                                                    check_read's v[12] starts there too (its `mv a3, sp`) *)
Definition SAT_SW_SP : Z := SAT_SR_SP - 0x50.    (* rp_slot_width's entry sp at rp_slot_read's call: 0x7fffffffe5d0 *)

Lemma sat_sp_values : SAT_SP = 0x7fffffffe700 /\ SAT_CHK_SP = 0x7fffffffe6c0 /\ SAT_FC_SP = 0x7fffffffe6b0 /\
  SAT_SR_SP = 0x7fffffffe620 /\ SAT_SW_SP = 0x7fffffffe5d0.
Proof. vm_compute. repeat split. Qed.

Ltac sat_num := unfold SAT_SW_SP, SAT_SR_SP, SAT_FC_SP, SAT_CHK_SP, SAT_SP, SAT_LO, SAT_HI, SAT_F.

Definition sat_frame : list byte :=
  map (fun i => Z_to_bv 8 (if i =? 12 then 0x88 else if i =? 13 then 0x19 else 0)) (map Z.of_nat (seq 0 124)).

Lemma sat_frame_length : length sat_frame = 124%nat.
Proof. reflexivity. Qed.

Definition sat_mem (bs : list byte) : word -> option byte := fun a =>
  let z := bv_unsigned a in
  if (SAT_F <=? z) && (z <? SAT_F + Z.of_nat (length bs)) then nth_error bs (Z.to_nat (z - SAT_F))
  else if (SAT_LO <=? z) && (z <? SAT_HI) then Some (Z_to_bv 8 0) else None.

Lemma sat_mem_far : forall bs a, 0 <= a < SAT_F -> sat_mem bs (wa a) = None.
Proof.
  intros bs a Ha. cbv beta zeta delta [sat_mem]. rewrite wa_unsigned by (unfold SAT_F in Ha; lia).
  rewrite (proj2 (Z.leb_gt SAT_F a)) by lia. cbn [andb].
  rewrite (proj2 (Z.leb_gt SAT_LO a)) by (unfold SAT_LO, SAT_HI, SAT_F in *; lia). reflexivity.
Qed.

Lemma sat_mem_stack : forall bs a, Z.of_nat (length bs) <= 0x10000 -> SAT_LO <= a < SAT_HI ->
  sat_mem bs (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros bs a L Ha. cbv beta zeta delta [sat_mem]. rewrite wa_unsigned by (unfold SAT_LO, SAT_HI in Ha; lia).
  rewrite (proj2 (Z.ltb_ge a (SAT_F + Z.of_nat (length bs)))) by (unfold SAT_LO, SAT_HI, SAT_F in *; lia).
  rewrite andb_false_r.
  rewrite (proj2 (Z.leb_le SAT_LO a)), (proj2 (Z.ltb_lt a SAT_HI)) by lia. reflexivity.
Qed.

Lemma sat_frame_at : forall bs, Z.of_nat (length bs) <= 0x10000 -> bytes_at rsegs (sat_mem bs) SAT_F bs.
Proof.
  intros bs L. split; [unfold SAT_F; lia|]. split; [unfold SAT_F; lia|].
  intros i Hi. cbv beta zeta delta [mrd sat_mem]. rewrite wa_unsigned by (unfold SAT_F; lia).
  rewrite (proj2 (Z.leb_le SAT_F (SAT_F + Z.of_nat i))) by lia.
  rewrite (proj2 (Z.ltb_lt (SAT_F + Z.of_nat i) (SAT_F + Z.of_nat (length bs)))) by lia.
  cbn [andb]. replace (SAT_F + Z.of_nat i - SAT_F) with (Z.of_nat i) by lia. rewrite Nat2Z.id.
  destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma sat_stk : forall bs lo hi, Z.of_nat (length bs) <= 0x10000 -> SAT_LO <= lo -> hi <= SAT_HI ->
  stk rsegs (sat_mem bs) lo hi.
Proof.
  intros bs lo hi L H1 H2. split; [unfold SAT_LO, SAT_HI in *; lia|]. split; [unfold SAT_HI in *; lia|].
  intros a Ha. assert (E : sat_mem bs (wa a) = Some (Z_to_bv 8 0)) by (apply sat_mem_stack; [exact L | lia]).
  split.
  - unfold wview. rewrite E. discriminate.
  - exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
Qed.

Lemma sat_wr : forall bs a n, Z.of_nat (length bs) <= 0x10000 -> SAT_LO <= a -> a + n <= SAT_HI ->
  wr_at rsegs (sat_mem bs) a n.
Proof.
  intros bs a n L H1 H2. split; [unfold SAT_LO, SAT_HI in *; lia|]. split; [unfold SAT_HI in *; lia|].
  intros i Hi. unfold wview. rewrite sat_mem_stack by (first [exact L | lia]). discriminate.
Qed.

(* Every loaded segment ends at or below SAT_F, so no address of the heap block or of the stack window is in one. *)
Lemma rsegs_below : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? SAT_F) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_above : forall segs a n,
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? SAT_F) segs = true ->
  SAT_F <= a -> 0 < n -> find_segment segs a n = None.
Proof.
  induction segs as [|seg segs IH]; intros a n H Ha Hn; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  match goal with |- context [Z.leb (a + n) ?t] =>
    replace (Z.leb (a + n) t) with false by (symmetry; apply Z.leb_gt; lia) end.
  rewrite andb_false_r. apply IH; assumption.
Qed.

(* The call memory holds overlay bytes only off the image: the invariant every reachable state keeps. *)
Lemma sat_mem_inv : forall bs, Z.of_nat (length bs) <= 0x10000 -> mem_inv rsegs (sat_mem bs).
Proof.
  intros bs L a b H. unfold ro_addr.
  assert (Ha : SAT_F <= bv_unsigned a).
  { revert H. cbv beta zeta delta [sat_mem].
    destruct (Z.leb_spec SAT_F (bv_unsigned a)) as [E|E]; [intros _; exact E|]. cbn [andb].
    destruct (Z.leb_spec SAT_LO (bv_unsigned a)) as [E2|E2]; [unfold SAT_LO, SAT_HI, SAT_F in *; lia|].
    cbn [andb]. intros E3; discriminate E3. }
  rewrite (find_segment_above rsegs (bv_unsigned a) 1 rsegs_below Ha ltac:(lia)). reflexivity.
Qed.

(* A read-only image range read through an overlay that holds nothing there. *)
Lemma rom_bytes_at : forall m A bs,
  ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (A + Z.of_nat i)) = None) ->
  bytes_at rsegs m A bs.
Proof.
  intros m A bs Hb HA Hl Hn. pose proof (ro_bytes_b_sound rsegs bs A Hb) as R.
  split; [exact HA|]. split; [exact Hl|]. intros i Hi.
  unfold mrd. rewrite (Hn i Hi). cbv beta iota.
  destruct (nth_error bs i) as [b|] eqn:E.
  - exact (proj1 (ro_bytes_nth rsegs bs A i b R E)).
  - apply nth_error_None in E. lia.
Qed.

Lemma sat_consts : forall bs,
  bytes_at rsegs (sat_mem bs) A_M (le8 (Z_to_bv 64 KM)) /\
  bytes_at rsegs (sat_mem bs) A_T (le8 (Z_to_bv 64 KT)) /\
  bytes_at rsegs (sat_mem bs) A_K36 (le8 (Z_to_bv 64 K36)).
Proof.
  intros bs.
  split; [|split]; (apply rom_bytes_at;
    [ vm_compute; reflexivity
    | unfold A_M, A_T, A_K36; lia
    | rewrite length_le8; change (Z.of_nat 8) with 8; unfold A_M, A_T, A_K36; lia
    | intros i Hi; rewrite length_le8 in Hi; apply sat_mem_far; unfold A_M, A_T, A_K36, SAT_F; lia ]).
Qed.

(* reac_frame_clean_len at rp_frame_channels's call (ubsan 0x1394c `jal reac_frame_clean_len`: a0 = len >= 0,
   ra = 0x13950, sp = its entry sp SAT_FC_SP - 0x10 = 0x7fffffffe6a0). Its premises are the two constants only;
   none mentions sp. *)
Lemma reac_frame_clean_len_sat :
  let m := sat_mem sat_frame in
  bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) /\ bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)).
Proof. cbv zeta. destruct (sat_consts sat_frame) as (C1 & C2 & _). split; assumption. Qed.

(* rp_frame_channels at check_width's first call (ubsan 0x1329c `jal rp_frame_channels`: a0 = s0 = n = 124,
   ra = 0x132a0, sp = rp_frame_channels's entry sp SAT_FC_SP = check_width's entry sp
   SAT_CHK_SP - check_width's frame 0x10); the call returns 2 channels. *)
Lemma rp_frame_channels_sat :
  let m := sat_mem sat_frame in let sp := Z_to_bv 64 SAT_FC_SP in let a0 := Z_to_bv 64 124 in
  mem_inv rsegs m /\ stk rsegs m SAT_LO (bv_unsigned sp) /\ SAT_LO + 16 <= bv_unsigned sp /\
  rp_frame_channels_model (bv_signed a0) = 2.
Proof.
  cbv zeta. rewrite (unsigned_lit SAT_FC_SP) by (sat_num; lia).
  split; [apply sat_mem_inv; rewrite sat_frame_length; lia|]. split.
  - apply sat_stk; [rewrite sat_frame_length; lia | lia | sat_num; lia].
  - split; [sat_num; lia | vm_compute; reflexivity].
Qed.

(* rp_slot_width at rp_slot_read's call (ubsan 0x13af8 `jal rp_slot_width`: a0 = f, a1 = n, a2 = slot as rp_slot_read
   got them, ra = 0x13afc, sp = rp_slot_width's entry sp SAT_SW_SP = rp_slot_read's entry sp
   SAT_SR_SP - rp_slot_read's frame 0x50), rp_slot_read being called by check_read with the
   fuzz_dup block f = SAT_F of the 124-byte frame, n = 124, slot = 0; the call returns 2 channels. *)
Lemma rp_slot_width_sat :
  let m := sat_mem sat_frame in let sp := Z_to_bv 64 SAT_SW_SP in
  let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in let a2 := Z_to_bv 64 0 in
  mem_inv rsegs m /\ stk rsegs m SAT_LO (bv_unsigned sp) /\ SAT_LO + 32 <= bv_unsigned sp /\
  (50 <= bv_unsigned a1 ->
     bv_unsigned a0 <> 0 /\ (18 <= length sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) sat_frame /\
     (bv_unsigned a0 + Z.of_nat (length sat_frame) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)) /\
  50 <= bv_unsigned a1 /\
  rp_slot_width_model (bv_unsigned a1) sat_frame (bv_signed a2) = 2.
Proof.
  cbv zeta. rewrite (unsigned_lit SAT_SW_SP) by (sat_num; lia).
  rewrite (unsigned_lit SAT_F) by (unfold SAT_F; lia). rewrite (unsigned_lit 124) by lia.
  split; [apply sat_mem_inv; rewrite sat_frame_length; lia|]. split.
  - apply sat_stk; [rewrite sat_frame_length; lia | lia | sat_num; lia].
  - split; [sat_num; lia|]. split; [|split; [lia | vm_compute; reflexivity]].
    intros _. rewrite sat_frame_length. split; [unfold SAT_F; lia|]. split; [lia|]. split.
    + apply sat_frame_at. rewrite sat_frame_length. lia.
    + left. sat_num. lia.
Qed.

(* reac_frame_is_reac at rp_copy_untag's call (ubsan 0x13a04 `jal reac_frame_is_reac`: a0 = s1 = c,
   a1 = s0 = n, ra = 0x13a08), rp_copy_untag being called by check_copy on the
   fuzz_dup block c = SAT_F of the untagged 124-byte frame, n = 124; the call returns 1 (EtherType 0x8819). *)
Lemma reac_frame_is_reac_sat :
  let m := sat_mem sat_frame in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (bv_unsigned a0 <> 0 -> 14 <= bv_unsigned a1 ->
     (14 <= length sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) sat_frame) /\
  bv_unsigned a0 <> 0 /\ 14 <= bv_unsigned a1 /\
  is_reac_result (bv_unsigned a0) (bv_unsigned a1) sat_frame = 1.
Proof.
  cbv zeta. rewrite (unsigned_lit SAT_F) by (unfold SAT_F; lia). rewrite (unsigned_lit 124) by lia.
  split; [|split; [unfold SAT_F; lia | split; [lia | vm_compute; reflexivity]]].
  intros _ _. rewrite sat_frame_length. split; [lia|]. apply sat_frame_at. rewrite sat_frame_length. lia.
Qed.

(* rp_slot_read at check_read's call (ubsan 0x133bc `jal rp_slot_read`: a0 = s0 = c, a1 = len, a2 = s1 = slot,
   a3 = sp = v, ra = 0x133c0, sp = rp_slot_read's entry sp SAT_SR_SP = check_read's entry sp SAT_CHK_SP -
   check_read's frame 0xa0; v[12] is check_read's stack array at that sp), check_read
   being called from LLVMFuzzerTestOneInput on the fuzz_dup block f = SAT_F of the 124-byte frame, len = 124,
   slot = 0; the call reads the slot and returns 1. *)
Lemma rp_slot_read_sat :
  let m := sat_mem sat_frame in let sp := Z_to_bv 64 SAT_SR_SP in
  let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in let a2 := Z_to_bv 64 0 in let a3 := sp in
  mem_inv rsegs m /\ stk rsegs m SAT_LO (bv_unsigned sp) /\ SAT_LO + 112 <= bv_unsigned sp /\
  (50 <= bv_unsigned a1 ->
     bv_unsigned a0 <> 0 /\ bv_unsigned a1 <= Z.of_nat (length sat_frame) /\ bytes_at rsegs m (bv_unsigned a0) sat_frame /\
     (bv_unsigned a0 + Z.of_nat (length sat_frame) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)) /\
  (0 <= rp_slot_width_model (bv_unsigned a1) sat_frame (bv_signed a2) ->
     bv_unsigned a3 <> 0 /\ bv_unsigned a3 mod 4 = 0 /\ wr_at rsegs m (bv_unsigned a3) 48 /\
     (bv_unsigned a3 + 48 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a3) /\
     (bv_unsigned a3 + 48 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length sat_frame) <= bv_unsigned a3)) /\
  50 <= bv_unsigned a1 /\ 0 <= rp_slot_width_model (bv_unsigned a1) sat_frame (bv_signed a2) /\
  rp_slot_read_model (bv_unsigned a1) sat_frame (bv_signed a2) = 1.
Proof.
  cbv zeta. rewrite (unsigned_lit SAT_SR_SP) by (sat_num; lia).
  rewrite (unsigned_lit SAT_F) by (unfold SAT_F; lia). rewrite (unsigned_lit 124) by lia.
  split; [apply sat_mem_inv; rewrite sat_frame_length; lia|]. split.
  - apply sat_stk; [rewrite sat_frame_length; lia | lia | sat_num; lia].
  - split; [sat_num; lia|]. split; [|split; [|split; [lia | split; vm_compute; first [discriminate | reflexivity]]]].
    + intros _. rewrite sat_frame_length. split; [unfold SAT_F; lia|]. split; [lia|]. split.
      * apply sat_frame_at. rewrite sat_frame_length. lia.
      * left. sat_num. lia.
    + intros _. split; [sat_num; lia|]. split; [sat_num; reflexivity|].
      split; [apply sat_wr; [rewrite sat_frame_length; lia | sat_num; lia | sat_num; lia]|].
      split; [right; lia|]. right. rewrite sat_frame_length. sat_num. lia.
Qed.
