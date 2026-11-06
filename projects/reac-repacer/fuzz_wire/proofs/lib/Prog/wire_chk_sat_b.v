(* The premises of check_read's and check_copy's contracts hold at the real call states in LLVMFuzzerTestOneInput (fuzz_wire.c:253-282,
   plain c8763dfc4e81 at 0x12d78): one closed lemma per contract and call site, with the caller's register values and a
   memory of the shape the caller has there.
   LLVMFuzzerTestOneInput saves ra / s0..s6 in a 64-byte frame, so each check_* runs at sp = SB_SP - 64, SB_SP being its
   own entry sp: 0x7fffffffe700, in the stack window above 0x7fff80000000 that a reachable state has (the allocator's
   call_pre needs alloc_ceiling + 8192 <= sp), so check_* is entered at 0x7fffffffe6c0. The memory: the fuzz_dup copy f
   of the frame at SB_F, the fuzz_dup copy c of f at SB_C (made after
   check_read's first call, fuzz_wire.c:274), the stack window [SB_LO, SB_HI) mapped, and nothing else in the overlay (an
   mrd outside reads the loaded image). The image's segments end below SB_F (rsegs_below_sb), so the overlay holds no byte
   of a read-only segment (mem_inv). The frame: a 2-channel REAC audio frame of 124 bytes (52 + 2 * 36; EtherType 0x8819
   at bytes 12-13, frame type 00 00 at bytes 16-17), the input of 125 bytes whose flag byte data[0] = 4 gives bcast 0,
   slot 0. check_copy keeps it untagged, so got = 124 and c holds the same 124 bytes at check_read's second call. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import check_read_c rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.

Definition SB_HI : Z := 0x7ffffffff700.
Definition SB_LO : Z := SB_HI - 0x10000.
Definition SB_SP : Z := SB_HI - 0x1000.
Definition SB_F : Z := 0x100000.
Definition SB_C : Z := 0x101000.

Definition sb_frame : list byte :=
  map (fun i => Z_to_bv 8 (if i =? 12 then 0x88 else if i =? 13 then 0x19 else 0)) (map Z.of_nat (seq 0 124)).

Lemma sb_frame_length : length sb_frame = 124%nat.
Proof. reflexivity. Qed.

(* f's n bytes at SB_F, c's at SB_C, the stack window, nothing else. *)
Definition sb_mem (fb cb : list byte) : word -> option byte := fun a =>
  let z := bv_unsigned a in
  if (SB_F <=? z) && (z <? SB_F + Z.of_nat (length fb)) then nth_error fb (Z.to_nat (z - SB_F))
  else if (SB_C <=? z) && (z <? SB_C + Z.of_nat (length cb)) then nth_error cb (Z.to_nat (z - SB_C))
  else if (SB_LO <=? z) && (z <? SB_HI) then Some (Z_to_bv 8 0) else None.

Lemma sb_stack : forall fb cb, (length fb <= 0x1000)%nat -> (length cb <= 0x1000)%nat ->
  forall a, SB_LO <= a < SB_HI -> sb_mem fb cb (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros fb cb Hfb Hcb a Ha. unfold sb_mem. rewrite wa_unsigned by (unfold SB_LO, SB_HI in Ha; lia).
  rewrite (proj2 (Z.ltb_ge a (SB_F + Z.of_nat (length fb)))) by (unfold SB_LO, SB_HI, SB_F in *; lia).
  rewrite andb_false_r.
  rewrite (proj2 (Z.ltb_ge a (SB_C + Z.of_nat (length cb)))) by (unfold SB_LO, SB_HI, SB_C in *; lia).
  rewrite andb_false_r.
  rewrite (proj2 (Z.leb_le SB_LO a)), (proj2 (Z.ltb_lt a SB_HI)) by lia. reflexivity.
Qed.

Lemma sb_bytes_f : forall fb cb, (length fb <= 0x1000)%nat -> (length cb <= 0x1000)%nat ->
  bytes_at rsegs (sb_mem fb cb) SB_F fb.
Proof.
  intros fb cb Hfb Hcb. split; [unfold SB_F; lia|]. split; [unfold SB_F; lia|].
  intros i Hi. unfold mrd, sb_mem. rewrite wa_unsigned by (unfold SB_F; lia).
  rewrite (proj2 (Z.leb_le SB_F (SB_F + Z.of_nat i))) by lia.
  rewrite (proj2 (Z.ltb_lt (SB_F + Z.of_nat i) (SB_F + Z.of_nat (length fb)))) by lia.
  cbn [andb]. replace (SB_F + Z.of_nat i - SB_F) with (Z.of_nat i) by lia. rewrite Nat2Z.id.
  destruct (nth_error fb i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma sb_bytes_c : forall fb cb, (length fb <= 0x1000)%nat -> (length cb <= 0x1000)%nat ->
  bytes_at rsegs (sb_mem fb cb) SB_C cb.
Proof.
  intros fb cb Hfb Hcb. split; [unfold SB_C; lia|]. split; [unfold SB_C; lia|].
  intros i Hi. unfold mrd, sb_mem. rewrite wa_unsigned by (unfold SB_C; lia).
  rewrite (proj2 (Z.leb_le SB_F (SB_C + Z.of_nat i))) by (unfold SB_F, SB_C; lia).
  rewrite (proj2 (Z.ltb_ge (SB_C + Z.of_nat i) (SB_F + Z.of_nat (length fb)))) by (unfold SB_F, SB_C; lia).
  cbn [andb].
  rewrite (proj2 (Z.leb_le SB_C (SB_C + Z.of_nat i))) by lia.
  rewrite (proj2 (Z.ltb_lt (SB_C + Z.of_nat i) (SB_C + Z.of_nat (length cb)))) by lia.
  cbn [andb]. replace (SB_C + Z.of_nat i - SB_C) with (Z.of_nat i) by lia. rewrite Nat2Z.id.
  destruct (nth_error cb i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma sb_stk : forall fb cb, (length fb <= 0x1000)%nat -> (length cb <= 0x1000)%nat ->
  forall lo hi, SB_LO <= lo -> hi <= SB_HI -> stk rsegs (sb_mem fb cb) lo hi.
Proof.
  intros fb cb Hfb Hcb lo hi H1 H2. split; [unfold SB_LO, SB_HI in *; lia|]. split; [unfold SB_HI in *; lia|].
  intros a Ha. assert (E : sb_mem fb cb (wa a) = Some (Z_to_bv 8 0)) by (apply sb_stack; [exact Hfb | exact Hcb | lia]).
  split.
  - unfold wview. rewrite E. discriminate.
  - exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
Qed.

(* Every loaded segment ends at or below SB_F, so no address of the heap blocks or of the stack window is in one. *)
Lemma rsegs_below_sb : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? SB_F) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sb_find_segment : forall segs a n,
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? SB_F) segs = true ->
  SB_F <= a -> 0 < n -> find_segment segs a n = None.
Proof.
  induction segs as [|seg segs IH]; intros a n H Ha Hn; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  match goal with |- context [Z.leb (a + n) ?t] =>
    replace (Z.leb (a + n) t) with false by (symmetry; apply Z.leb_gt; lia) end.
  rewrite andb_false_r. apply IH; assumption.
Qed.

Lemma sb_mem_inv : forall fb cb, mem_inv rsegs (sb_mem fb cb).
Proof.
  intros fb cb a b H. unfold ro_addr.
  assert (Ha : SB_F <= bv_unsigned a).
  { revert H. unfold sb_mem.
    destruct (Z.leb_spec SB_F (bv_unsigned a)) as [E|E]; [intros _; exact E|]. cbn [andb].
    destruct (Z.leb_spec SB_C (bv_unsigned a)) as [E2|E2]; [unfold SB_C, SB_F in *; lia|]. cbn [andb].
    destruct (Z.leb_spec SB_LO (bv_unsigned a)) as [E3|E3]; [unfold SB_LO, SB_HI, SB_F in *; lia|].
    cbn [andb]. intros E4; discriminate E4. }
  rewrite (sb_find_segment rsegs (bv_unsigned a) 1 rsegs_below_sb Ha ltac:(lia)). reflexivity.
Qed.


(* check_read at its first call (plain 0x12e54 `jal check_read`: a0 = s0 = f, a1 = s1 = n = 124, a2 = s2 = slot,
   sp = SB_SP - 64); f is the only heap block yet, c is not made (its bytes in the memory are those of a later state). *)
Lemma check_read_sat_1 :
  let m := sb_mem sb_frame [] in let sp := Z_to_bv 64 (SB_SP - 64) in
  let a0 := Z_to_bv 64 SB_F in let a1 := Z_to_bv 64 124 in
  mem_inv rsegs m /\ stk rsegs m SB_LO (bv_unsigned sp) /\ SB_LO + CHECK_READ_STACK <= bv_unsigned sp /\
  bv_unsigned a1 <= 1600 /\ Z.of_nat (length sb_frame) = bv_unsigned a1 /\ bytes_at rsegs m (bv_unsigned a0) sb_frame /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_READ_STACK \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. unfold CHECK_READ_STACK.
  rewrite (unsigned_lit (SB_SP - 64)) by (unfold SB_SP, SB_HI; lia).
  rewrite (unsigned_lit SB_F) by (unfold SB_F; lia). rewrite (unsigned_lit 124) by lia.
  assert (L : (length sb_frame <= 0x1000)%nat) by (rewrite sb_frame_length; lia).
  assert (L0 : (length (@nil byte) <= 0x1000)%nat) by (cbn; lia).
  split; [apply sb_mem_inv|]. split; [apply (sb_stk _ _ L L0); unfold SB_SP; lia|].
  split; [unfold SB_LO, SB_SP; lia|]. split; [lia|]. split; [reflexivity|].
  split; [apply (sb_bytes_f _ _ L L0)|]. left. unfold SB_F, SB_SP, SB_HI. lia.
Qed.

(* check_read at its second call (plain 0x12e9c: a0 = s3 = c, a1 = check_copy's result 124, a2 = s2 = slot,
   sp = SB_SP - 64), with f at SB_F and its copy c at SB_C. The last two conjuncts: check_copy's post
   (check_copy_c.v) gives this state, a1 = copy_untag_result 124 sb_frame = 124 and c holding
   cu_bytes 124 sb_frame = sb_frame (rp_copy_untag_c.v). *)
Lemma check_read_sat_2 :
  let m := sb_mem sb_frame sb_frame in let sp := Z_to_bv 64 (SB_SP - 64) in
  let a0 := Z_to_bv 64 SB_C in let a1 := Z_to_bv 64 124 in
  mem_inv rsegs m /\ stk rsegs m SB_LO (bv_unsigned sp) /\ SB_LO + CHECK_READ_STACK <= bv_unsigned sp /\
  bv_unsigned a1 <= 1600 /\ Z.of_nat (length sb_frame) = bv_unsigned a1 /\ bytes_at rsegs m (bv_unsigned a0) sb_frame /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_READ_STACK \/ bv_unsigned sp <= bv_unsigned a0) /\
  copy_untag_result 124 sb_frame = 124 /\ cu_bytes 124 sb_frame = sb_frame.
Proof.
  cbv zeta. unfold CHECK_READ_STACK.
  rewrite (unsigned_lit (SB_SP - 64)) by (unfold SB_SP, SB_HI; lia).
  rewrite (unsigned_lit SB_C) by (unfold SB_C; lia). rewrite (unsigned_lit 124) by lia.
  assert (L : (length sb_frame <= 0x1000)%nat) by (rewrite sb_frame_length; lia).
  split; [apply sb_mem_inv|]. split; [apply (sb_stk _ _ L L); unfold SB_SP; lia|].
  split; [unfold SB_LO, SB_SP; lia|]. split; [lia|]. split; [reflexivity|].
  split; [apply (sb_bytes_c _ _ L L)|]. split; [left; unfold SB_C, SB_SP, SB_HI; lia|].
  split; vm_compute; reflexivity.
Qed.

(* ---- check_copy (check_copy_c.v), called once, at plain 0x12e88 `jal check_copy` (fuzz_wire.c:275) ----
   Its premises are about the allocator state, so the witness is stated for any allocator model over this image
   (check_copy_sat_gen) and at this image's own allocator (check_copy_sat: src0_msyms, zlib_API; FrameProof.v's
   zlib_frame_allocator holds for it), from the facts LLVMFuzzerTestOneInput has at the call:
   f = fuzz_dup(data + 1, n) and c = fuzz_dup(f, n) are two blocks of fuzz_dup_size n bytes (the malloc_ret of
   Contract.v, then fuzz_dup's memcpy), both holding the n frame bytes, the allocator initialised, the budget the
   entry budget b0 with those two blocks live, sp = 0x7fffffffe6c0, a0 = c (s3), a1 = f (s0), a2 = n (s1),
   ra = 0x12e8c. An entry budget (cc_entry_room): live <= 64, bytes <= 2^28, 128 <= cap <= CAPMAX,
   the bound of AgreeShape.v's ag_room_g, so it holds for the frame's budget (FrameAPI.v lib_room, cap = CAPMAX) and
   for the agree runs' (cap = CAP_AG = 1024, SlotAgree.v); the driver's real budget SBD (DriverSlots.v) is one
   (cc_SBD_entry). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YL0i YH02 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Contract ZAllocator.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FuzzDup check_copy_c.

Definition cc_entry_room (b : sbound) : Prop := sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

Lemma cc_SBD_entry : cc_entry_room SBD.
Proof. unfold cc_entry_room, SBD, CAPMAX. cbn [sb_live sb_bytes sb_cap]. lia. Qed.

(* the budget at check_copy's own fuzz_dup: f and c live *)
Definition cc_b2 (b0 : sbound) (n : Z) : sbound := sb_malloc (sb_malloc b0 (fuzz_dup_size n)) (fuzz_dup_size n).

Lemma cc_room_at_call : forall b0 n, cc_entry_room b0 -> 0 <= n <= 1600 -> room_slots (cc_b2 b0 n) (fuzz_dup_size n).
Proof.
  intros b0 n (H1 & H2 & H3) Hn. pose proof (fuzz_dup_size_range n ltac:(lia)) as (S1 & S2).
  apply fuzz_dup_room; unfold cc_b2, sb_malloc in *; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Theorem check_copy_sat_gen : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B)
    L A regs mem md (c f n : Z) (bs : list byte) b0,
  let segs := ms_segs B in
  ms_segs B = rsegs ->
  cc_entry_room b0 -> res_ok_slots A (cc_b2 b0 n) ->
  0 <= n <= 1600 -> Z.of_nat (length bs) = n ->
  aa_MR API L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  In (f, fuzz_dup_size n) (blocks L A) -> In (c, fuzz_dup_size n) (blocks L A) -> f <> c ->
  Mem.bytes_at segs mem c bs -> Mem.bytes_at segs mem f bs -> ro_agree segs mem -> frm_zero fp_csr ->
  getr regs 1 = Z_to_bv 64 0x12e8c -> getr regs 2 = Z_to_bv 64 0x7fffffffe6c0 -> getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 f -> getr regs 12 = Z_to_bv 64 n ->
  (forall a, 0x7fffffffe6c0 - CC_STACK <= a < 0x7fffffffe6c0 -> writable_at segs mem a) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) ->
  ms_segs B = rsegs /\
  call_pre_k B (aa_MR API) CC_STACK L A regs mem md /\
  st_init_done A = true /\
  getr regs 10 = Z_to_bv 64 c /\ getr regs 11 = Z_to_bv 64 f /\ getr regs 12 = Z_to_bv 64 n /\
  n <= 1600 /\ Z.of_nat (length bs) = n /\
  In (c, fuzz_dup_size n) (blocks L A) /\ n <= fuzz_dup_size n /\
  (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) /\
  Mem.bytes_at segs mem c bs /\ Mem.bytes_at segs mem f bs /\ ro_agree segs mem /\ frm_zero fp_csr /\
  res_ok_slots A (cc_b2 b0 n) /\ room_slots (cc_b2 b0 n) (fuzz_dup_size n).
Proof.
  intros rc fx B API L A regs mem md c f n bs b0 segs HSG Hb0 Hres Hn HL HM HW HB Hinit Hf Hc Hfc BC BF RO FRM
    G1 G2 G4 G10 G11 G12 HSW HEW.
  pose proof (@alloc_ceiling_value rc) as Hac. pose proof (fuzz_dup_size_range n ltac:(lia)) as (S1 & S2).
  assert (SP : spZ regs = 0x7fffffffe6c0%Z) by (unfold spZ; rewrite G2; apply MState.unsigned_lit; lia).
  split; [exact HSG|].
  split.
  { split; [exact HM|]. split; [exact HW|]. split; [exact HB|].
    split; [rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP; reflexivity|].
    split; [rewrite SP; unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia|].
    split; [rewrite SP; lia|].
    split; [intros a Ha; rewrite SP in Ha; exact (HSW a Ha)|].
    split; [exact G4|].
    split; [exact HEW|].
    intros E. rewrite Hinit in E. discriminate. }
  split; [exact Hinit|].
  split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
  split; [lia|]. split; [exact HL|].
  split; [exact Hc|].
  split; [unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia|].
  split; [exists f, (fuzz_dup_size n); split; [exact Hf|]; split; [exact Hfc|]; split; [lia|];
          unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia|].
  split; [exact BC|]. split; [exact BF|]. split; [exact RO|]. split; [exact FRM|].
  split; [exact Hres | exact (cc_room_at_call b0 n Hb0 Hn)].
Qed.

(* the same at this image's own allocator *)
Corollary check_copy_sat : forall (rc : RunCeil) (fx : FPState) L A regs mem md (c f n : Z) (bs : list byte) b0,
  let segs := ms_segs src0_msyms in
  cc_entry_room b0 -> res_ok_slots A (cc_b2 b0 n) ->
  0 <= n <= 1600 -> Z.of_nat (length bs) = n ->
  aa_MR (@zlib_API rc) L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  In (f, fuzz_dup_size n) (blocks L A) -> In (c, fuzz_dup_size n) (blocks L A) -> f <> c ->
  Mem.bytes_at segs mem c bs -> Mem.bytes_at segs mem f bs -> ro_agree segs mem -> frm_zero fp_csr ->
  getr regs 1 = Z_to_bv 64 0x12e8c -> getr regs 2 = Z_to_bv 64 0x7fffffffe6c0 -> getr regs 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
  getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 f -> getr regs 12 = Z_to_bv 64 n ->
  (forall a, 0x7fffffffe6c0 - CC_STACK <= a < 0x7fffffffe6c0 -> writable_at segs mem a) ->
  (forall a, errno_addr src0_msyms <= a < errno_addr src0_msyms + 4 -> writable_at segs mem a) ->
  ms_segs src0_msyms = rsegs /\
  call_pre_k src0_msyms (aa_MR (@zlib_API rc)) CC_STACK L A regs mem md /\
  st_init_done A = true /\
  getr regs 10 = Z_to_bv 64 c /\ getr regs 11 = Z_to_bv 64 f /\ getr regs 12 = Z_to_bv 64 n /\
  n <= 1600 /\ Z.of_nat (length bs) = n /\
  In (c, fuzz_dup_size n) (blocks L A) /\ n <= fuzz_dup_size n /\
  (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) /\
  Mem.bytes_at segs mem c bs /\ Mem.bytes_at segs mem f bs /\ ro_agree segs mem /\ frm_zero fp_csr /\
  res_ok_slots A (cc_b2 b0 n) /\ room_slots (cc_b2 b0 n) (fuzz_dup_size n).
Proof.
  intros rc fx L A regs mem md c f n bs b0 segs.
  exact (check_copy_sat_gen rc fx src0_msyms (@zlib_API rc) L A regs mem md c f n bs b0 eq_refl).
Qed.
