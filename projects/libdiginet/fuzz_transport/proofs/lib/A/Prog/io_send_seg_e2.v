(* io_send_seg_e2: the retry and E2 arms of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the frozen statement is lib/A/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), 0x830e8 .. 0x8315c = transport_text + IOS_E2DATA .. + 0x3fc.

   The code (io_send_cg.v header lines 111-119), with sp = the walk's sp (the entry sp less IOSEND_FRAME = 160),
   M = TA_M and GOT = TA_GOT:
     0x830e8 - 0x830ec  E2 / DATA (:838-840): f.retry (the 2-byte load at sp + 38, io_send's own frame, no
                        instrumented check) = 0 goes to 0x83124;
     0x830f0 - 0x83120  retry (:841-843): a0 = p, a1 = len, a2 = sp + 8; `jal` check_inflight_retry at 0x830fc,
                        return address 0x83100; M.fly.retries (M + 108) + 1 stored back (4 bytes); the 8-byte store
                        of g_now at M + 112 (M.fly.sent); then to 0x83384 (IOS_EPI);
     0x83124 - 0x8315c  E2 (:846-852): s5 <> 0xe2 goes to 0x83160 (the DATA arm, another segment's); `jal`
                        check_state_wake at 0x8312c, return address 0x83130 (no argument); a0 = sp + 8, `jal`
                        check_latest_control at 0x83134, return address 0x83138; GOT.e2 (GOT + 196) + 1 stored
                        back; the 4-byte store of f.send (sp + 40) at g_last_counter; s3 & 1 = 0 goes to 0x83338
                        (= transport_text + IOS_FLY), else to 0x83384 (= transport_text + IOS_EPI).

   The lemma ios_e2_seg is SELF-CONTAINED: its premises are the record facts and the three callee contracts
   (ios_e2_laws), the entry facts of the walk that this stretch reads (ios_e2_fix), and the state at the cut
   (ios_e2_at at the world ios_B0 Bw); it concludes, in continuation form, the three exits (ios_e2_at again, at
   the world the model leaves at each).

   The model side is lib/A/Prog/io_send_segs.v: ios_arm_retry and ios_arm_e2 read the dispatch, giving the model
   calls (check_inflight_retry_m, check_state_wake_m, check_latest_control_m), the int_inc of GOT.e2 (so the
   machine's 32-bit increment does not overflow) and the world each arm leaves. `TW.g_fail_next Bw <= 1` is what
   makes the machine's `s3 & 1` the model's `truth fail`.

   How: lib/A/Prog/DgnTransportPaLib.v paj_run_tok / paj_run_to_tok per straight stretch over the G journal
   (TransportGRunA.v paj_run_x / paj_run_to_x), psrr_branch_tok at each branch; the DONOR call of
   check_inflight_retry through TransportGCg.v gx_call_cg (its post, DgnTransportCg.v decode_cg_post, read as
   dcg_post by decode_cg_post_dcg); the two LEAF calls through DgnTransportLeafb.v decode_leafb_journal. Every
   store of this stretch is a byte of G (W_journalG.v awr_ok_x_cons_g) and is in iosend_wr (io_send_seg_world.v
   ios_wr_fly_retries / ios_wr_fly_sent / ios_wr_got_e2 / ios_wr_lastc); the world after each is one ios_tw_step at
   the M, GOT or g_last_counter row of TWorldA.v TMAP_A.

   Across the donor call the frame facts are carried by DgnTransportCg.v trans_src_ok_acall_g, which asks
   trans_ro_rd_unowned / trans_rom_no_errno — facts the statement does not give. io_send's frame can never lie in
   TRANS_RO_RD: io_send_seg_frm.v ios_len60 makes it at least 60 bytes, and no contiguous run of TRANS_RO_RD is
   that long (ios_ro_gap, decided over the table), so ios_src_ok_acall_g carries it without them. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA DgnTransportLeafb CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src io_send_seg_csf.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg check_latest_frame_cg
  check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* A field of the struct spec_frame, as the engine and the leaves read it *)
(* ------------------------------------------------------------------ *)

(* Byte k of the little-endian value of a byte list is the list's byte k (0 past its end, where the value's bits
   are 0 too). This is what turns check_sent_frame_cg.v trans_sframe_at, which gives the struct's bytes as a list
   SB and each field as TW.u_at SB off n, into the per-byte form YI04.val_mem the symbolic chunks and the leaf
   contracts take. *)
Lemma ios_ble_shiftr : forall (l : list byte) (k : nat),
  Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
  induction l as [|b r IH]; intros k.
  - cbn [bytes_le_to_Z nth]. destruct k; rewrite Z.shiftr_0_l, Z_to_bv_unsigned; reflexivity.
  - assert (Hb : 0 <= bv_unsigned b < 256)
      by (pose proof (bv_unsigned_in_range 8 b) as Hr; change (bv_modulus 8) with 256 in Hr; lia).
    assert (HL : Z.log2 (bv_unsigned b) < 8).
    { destruct (Z.eq_dec (bv_unsigned b) 0) as [E|Hne];
        [rewrite E, Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
    cbn [bytes_le_to_Z].
    destruct k as [|k'].
    + cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      change 256 with (2 ^ 8).
      apply Z.bits_inj'. intros i Hi.
      destruct (Z_lt_le_dec i 8) as [Hl|Hl].
      * rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
        rewrite (Z.testbit_neg_r (bytes_le_to_Z r) (i - 8)) by lia. apply orb_false_r.
      * rewrite Z.mod_pow2_bits_high by lia. symmetry. apply Z.bits_above_log2; lia.
    + cbn [nth]. rewrite <- (IH k').
      f_equal.
      apply Z.bits_inj'. intros i Hi.
      rewrite !Z.shiftr_spec by lia.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.bits_above_log2 (bv_unsigned b) (i + 8 * Z.of_nat (S k'))) by lia.
      cbn [orb]. f_equal. lia.
Qed.

(* The sub-list TW.sub reads is the list's own bytes (TWorldLemmas.v ne_sub, as nth). *)
Lemma ios_nth_sub : forall (l : list byte) (off : Z) (n k : nat), 0 <= off -> (k < n)%nat ->
  (Z.to_nat off + n <= length l)%nat ->
  nth k (TW.sub l off n) (Z_to_bv 8 0) = nth (Z.to_nat off + k) l (Z_to_bv 8 0).
Proof.
  intros l off n k H0 Hk Hn.
  assert (HS : (k < length (TW.sub l off n))%nat)
    by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  assert (HL : (Z.to_nat off + k < length l)%nat) by lia.
  pose proof (TWL.ne_sub l off n k H0) as E.
  replace (k <? n)%nat with true in E by (symmetry; apply Nat.ltb_lt; lia).
  rewrite (nth_error_nth' (TW.sub l off n) (Z_to_bv 8 0) HS),
          (nth_error_nth' l (Z_to_bv 8 0) HL) in E.
  injection E as E. exact E.
Qed.

(* One byte, read as a one-byte little-endian value. *)
Lemma ios_le_byte1 : forall b : byte, YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* A field of a garr8 byte array, as YI04.val_mem of its little-endian value. *)
Lemma ios_val_of_garr8 : forall (m : word -> option byte) (fp off : Z) (SB : list byte) (n : nat),
  garr8 tfibsegs m fp (map (fun b : byte => bv_unsigned b) SB) -> 0 <= off ->
  (Z.to_nat off + n <= length SB)%nat ->
  YI04.val_mem tfibsegs m (fp + off) n (TW.u_at SB off n).
Proof.
  intros m fp off SB n HG H0 Hn k Hk.
  assert (Hj : ((Z.to_nat off + k) < length (map (fun b : byte => bv_unsigned b) SB))%nat)
    by (rewrite length_map; lia).
  destruct (HG (Z.to_nat off + k)%nat Hj) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in Hv.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by exact Hj.
  rewrite map_nth in Hv.
  replace (fp + off + Z.of_nat k) with (fp + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite Hv. f_equal. f_equal.
  rewrite ios_le_byte1.
  unfold YO0f.le_byte, TW.u_at.
  rewrite (Z.mod_small (bytes_le_to_Z (TW.sub SB off n)) (2 ^ (8 * Z.of_nat n)))
    by (apply TWL.ble_small, TWL.length_sub_le).
  rewrite ios_ble_shiftr, (ios_nth_sub SB off n k H0 Hk Hn). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state of the stretch                                   *)
(* ------------------------------------------------------------------ *)

(* The atoms beyond the 32 registers: the two struct fields the code loads and the three harness words.
   32 f.retry (sp + 38, 2 bytes), 33 f.send (sp + 40, 4), 34 M.fly.retries (M + 108, 4), 35 g_now (8),
   36 GOT.e2 (GOT + 196, 4).
   The regions: io_send's own frame cells sp + 38 .. sp + 44 (read only), M.fly.retries and M.fly.sent
   (M + 108 .. M + 120), g_now (read only), GOT.e2 and g_last_counter, which the code reaches as -12 from the
   %hi of object 54 (0x5df14c). A region is given its write window only on the stretch that stores into it (the
   booleans wf, we, wl), so that the run's frame_of keeps every other byte: the retry arm stores M.fly.retries
   and M.fly.sent, the E2 arm GOT.e2 and g_last_counter, and the other stretches store nothing. *)
Definition ios_e2_rstk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 38 44 38 38
    [YP09.mkChunk 38 (CVal 2 (SOff 32 0)); YP09.mkChunk 40 (CVal 4 (SOff 33 0))].
Definition ios_e2_rfly (wf : bool) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 108 120 (if wf then 108 else 0) (if wf then 120 else 0)
    [YP09.mkChunk 108 (CVal 4 (SOff 34 0))].
Definition ios_e2_rnow : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition ios_e2_re2 (we : bool) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 28)) 0 4 0 (if we then 4 else 0) [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition ios_e2_rlc (wl : bool) : YP09.region :=
  YP09.mkRegion (Some (A_HI 54)) (-12) (-8) (-12) (if wl then -8 else -12) [].
Definition ios_e2_regions (wf we wl : bool) : smem :=
  [ios_e2_rstk; ios_e2_rfly wf; ios_e2_rnow; ios_e2_re2 we; ios_e2_rlc wl].
(* The store of GOT.e2 is `sw a1, 620(a0)` with a0 the %hi of object 53 (0x5e5138); the load before it is the
   listing's PLdHi at object 28 (0x5e53a4 = 0x5e5138 + 620). The alias makes the engine read both in one region. *)
Definition ios_e2_facts : facts := mkFacts [] [] [(SOff (A_HI 53) 620, SOff (A_OBJ 28) 0)].
Definition ios_e2_Bx : sv := SOff 20 0.
Definition ios_e2_ss (wf we wl : bool) (pc : Z) : sstate :=
  mkSS pc sr_atoms (ios_e2_regions wf we wl) None ios_e2_facts.

(* Where the token engine stops on each stretch of this segment, and why: the measured code of io_send_cg.v's
   header, decided over the listing (lib/A/Prog/DgnTransportList.v). *)
Definition ios_e2_run (wf we wl : bool) (pc : Z) :=
  let ss := ios_e2_ss wf we wl pc in
  let K := run_K A_LIM ios_e2_Bx (@nil shent) ss in
  match sym_runN_pi_tok transport_tpi transport_tw K ios_e2_Bx YC4b.Bspan (@nil shent) FUEL ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.
Definition ios_e2_run_to (wf we wl : bool) (stop pc : Z) :=
  let ss := ios_e2_ss wf we wl pc in
  let K := run_K A_LIM ios_e2_Bx (@nil shent) ss in
  match sym_run_toN_pi_tok transport_tpi transport_tw K ios_e2_Bx YC4b.Bspan (@nil shent) FUEL stop ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.

(* f.retry at sp + 38, then the branch of 0x830ec. *)
Lemma ios_e2_stop_head :
  ios_e2_run false false false IOS_E2DATA =
  (IOS_AT 0x38c, PTS_stopped (SR_branch BC_EQ (SExt false 16 (SOff 32 0)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
(* The retry arm's call setup: it stops at the jal of check_inflight_retry (0x830fc), the state's pc being the
   return address 0x83100. *)
Lemma ios_e2_stop_cir :
  ios_e2_run false false false (IOS_AT 0x390) = (IOS_AT 0x3a0, PTS_call TS_check_inflight_retry).
Proof. vm_compute. reflexivity. Qed.
(* The retry arm's tail: M.fly.retries + 1 and M.fly.sent = g_now, then `j` to the epilogue. *)
Lemma ios_e2_stop_retry :
  ios_e2_run_to true false false IOS_EPI (IOS_AT 0x3a0) = (IOS_EPI, PTS_running).
Proof. vm_compute. reflexivity. Qed.
(* The E2 / DATA test of 0x83128. *)
Lemma ios_e2_stop_e2 :
  ios_e2_run false false false (IOS_AT 0x3c4) =
  (IOS_AT 0x3c8, PTS_stopped (SR_branch BC_NE (SOff 21 0) (SLit 226))).
Proof. vm_compute. reflexivity. Qed.
(* The two leaf calls of the E2 arm. *)
Lemma ios_e2_stop_csw :
  ios_e2_run false false false (IOS_AT 0x3cc) = (IOS_AT 0x3d0, PTS_call TS_check_state_wake).
Proof. vm_compute. reflexivity. Qed.
Lemma ios_e2_stop_clc :
  ios_e2_run false false false (IOS_AT 0x3d0) = (IOS_AT 0x3d8, PTS_call TS_check_latest_control).
Proof. vm_compute. reflexivity. Qed.
(* The E2 arm's tail: GOT.e2 + 1, g_last_counter = f.send, then the branch of 0x83158 on bit 0 of s3. *)
Lemma ios_e2_stop_tail :
  ios_e2_run false true true (IOS_AT 0x3d8) =
  (IOS_AT 0x3f8, PTS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SOff 19 0) (SLit 1)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.

Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* What this stretch is given                                          *)
(* ------------------------------------------------------------------ *)

(* The record facts, the allocator and meter laws, G inside the image and outside the allocator's statics and
   errno, and the contracts of the three callees of this stretch: a sub-list of the premises of io_send_cg.v
   transport_io_send_cg_holds_stmt. *)
Definition ios_e2_laws : Prop :=
  transport_cells B /\
  AR_laws segs B /\ ameter_laws MT /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS /\
  (forall fx' : YK11.FPState,
     @transport_check_inflight_retry_cg fx' rc B MT (transport_sigma TS_check_inflight_retry)) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx').

(* The state at a cut of this stretch, at its own world W2: io_send_seg_cut.v ios_at_csf, generalised in the
   world Bx the cut relates to and in the g_fail_next byte the entry read. At Bx = ios_B0 Bw and
   fail = TW.g_fail_next Bw it IS ios_at_csf, so the dispatch segment's E2 / DATA exit is this cut with no glue;
   s5 = f.cmd travels beside it, as that exit states it. *)
Definition ios_e2_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Bx : list byte) : Prop :=
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2 /\
  ios_saved W2 mem2 regs /\
  ios_regs regs regs2 p frame fail /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
  trans_src_ok B ly2 S2 W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE /\
  garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame) /\
  trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bx.

(* The cut is io_send_seg_cut.v's ios_at_csf, generalised: the dispatch segment's exit is this one. *)
Lemma ios_e2_at_csf : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    regs p frame Bw ly2 S2 (W2 : world segs) mem2 md2 regs2,
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw
    ly2 S2 W2 mem2 md2 regs2 ->
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
    ly2 S2 W2 mem2 md2 regs2 (ios_B0 Bw).
Proof. intros. exact H. Qed.

(* The DATA arm's head (0x83160), the one exit of this stretch io_send_seg_cut.v does not name. *)
Definition IOS_DATA : Z := IOS_AT 0x400.
Lemma ios_data_addr : transport_text + IOS_DATA = 0x83160.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at a cut of this stretch                         *)
(* ------------------------------------------------------------------ *)

(* The listing's values of the objects and the two %hi slots the code reaches. *)
Lemma ios_e2_vals :
  VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 27) = TA_g_now /\ VAL (A_OBJ 28) = TA_GOT + 196 /\
  VAL (A_HI 53) = TA_GOT + 196 - 620 /\ VAL (A_HI 54) = TA_g_last_counter + 12.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The walk's valuation: the 32 registers of the cut, then the five values the stretch reads. *)
Definition ios_e2_E (regs : bvmap 5 word) (rty snd4 flyr now e2 : Z) : env :=
  Eimg (PI := PI_transport)
    (Ereg regs [Z_to_bv 64 rty; Z_to_bv 64 snd4; Z_to_bv 64 flyr; Z_to_bv 64 now; Z_to_bv 64 e2]).

Lemma ios_e2_agree : forall regs rty snd4 flyr now e2,
  env_agree 32 (Ereg regs [Z_to_bv 64 rty; Z_to_bv 64 snd4; Z_to_bv 64 flyr; Z_to_bv 64 now; Z_to_bv 64 e2])
    (ios_e2_E regs rty snd4 flyr now e2).
Proof.
  intros. split; [intros n Hn; unfold ios_e2_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The state the token engine runs from: the five regions at their bases, the %hi alias of GOT.e2, and the
   registers as atoms. Every byte it names is a byte of G (writable at any memory, TransportGCg.v gx_rw_writable
   with TransportGRwA.v G_HARNESS_rw) or a cell of io_send's own frame. *)
Lemma ios_e2_state : forall (wf we wl : bool) (pc sp rty snd4 flyr now e2 : Z)
    (W : world segs) (regs : bvmap 5 word) mem,
  YK11.getr regs 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 ->
  0 <= rty < 2 ^ 16 -> 0 <= snd4 < 2 ^ 32 -> 0 <= flyr < 2 ^ 32 -> 0 <= now < 2 ^ 64 -> 0 <= e2 < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (sp + 38) 2 rty ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (sp + 40) 4 snd4 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_M + 108) 4 flyr ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_g_now + 0) 8 now ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_GOT + 196 + 0) 4 e2 ->
  st_ok_pi segs VAL (ios_e2_E regs rty snd4 flyr now e2) (ios_e2_ss wf we wl pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros wf we wl pc sp rty snd4 flyr now e2 W regs mem
    Hsp2 Hlo Hhi Hrty Hsnd Hflyr Hnow He2 V38 V40 V108 Vnow Ve2.
  assert (EM : TA_M = 6156640) by reflexivity.
  assert (EN : TA_g_now = 6156544) by reflexivity.
  assert (EG : TA_GOT = 6181600) by reflexivity.
  assert (EL : TA_g_last_counter = 6156608) by reflexivity.
  destruct ios_e2_vals as (V8 & V27 & V28 & V53 & V54).
  set (E := ios_e2_E regs rty snd4 flyr now e2).
  assert (EOB : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j))
    by (intros j Hj; unfold E, ios_e2_E; apply Eimg_img; exact Hj).
  assert (E2 : ew E 2 = YK11.getr regs 2)
    by (unfold E, ios_e2_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = sp)
    by (rewrite E2, Hsp2; apply unsigned_lit_small; lia).
  assert (X32 : ew E 32 = Z_to_bv 64 rty)
    by (unfold E, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (X33 : ew E 33 = Z_to_bv 64 snd4)
    by (unfold E, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (X34 : ew E 34 = Z_to_bv 64 flyr)
    by (unfold E, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (X35 : ew E 35 = Z_to_bv 64 now)
    by (unfold E, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (X36 : ew E 36 = Z_to_bv 64 e2)
    by (unfold E, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (U8 : base_val E (Some (A_OBJ 8)) = TA_M).
  { cbn [base_val]. rewrite (EOB (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V8.
    apply unsigned_lit_small. lia. }
  assert (U27 : base_val E (Some (A_OBJ 27)) = TA_g_now).
  { cbn [base_val]. rewrite (EOB (A_OBJ 27) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V27.
    apply unsigned_lit_small. lia. }
  assert (U28 : base_val E (Some (A_OBJ 28)) = TA_GOT + 196).
  { cbn [base_val]. rewrite (EOB (A_OBJ 28) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V28.
    apply unsigned_lit_small. lia. }
  assert (U54 : base_val E (Some (A_HI 54)) = TA_g_last_counter + 12).
  { cbn [base_val]. rewrite (EOB (A_HI 54) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), V54.
    apply unsigned_lit_small. lia. }
  assert (U53 : bv_unsigned (ew E (A_HI 53)) = TA_GOT + 196 - 620).
  { rewrite (EOB (A_HI 53) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), V53. apply unsigned_lit_small. lia. }
  assert (WG : forall a, inG TG.G_HARNESS a -> writable_at segs (mrestrict (w_H W) mem) a)
    by (intros a Ha; exact (gx_rw_writable segs TG.G_HARNESS a G_HARNESS_rw Ha _)).
  rewrite restrict_mkst_fx. unfold ios_e2_ss, ios_e2_regions.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - destruct wf, we, wl; vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + unfold ios_e2_rstk, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ sp 38 2 (SOff 32 0) rty);
          [cbn [sv_denot]; rewrite X32, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact V38].
      * apply (chunk_ok_val segs E _ sp 40 4 (SOff 33 0) snd4);
          [cbn [sv_denot]; rewrite X33, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact V40].
    + unfold ios_e2_rfly, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U8. split; [lia|]. split; [lia|]. split.
      * intros o Ho. destruct wf; [|cbn in Ho; lia].
        apply WG. apply (ios_inG_row _ _ _ _ TMAP_A_M). unfold TW.SZ_M. cbn in Ho. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ TA_M 108 4 (SOff 34 0) flyr);
          [cbn [sv_denot]; rewrite X34, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact V108].
    + unfold ios_e2_rnow, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 35 0) now);
        [cbn [sv_denot]; rewrite X35, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact Vnow].
    + unfold ios_e2_re2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U28. split; [lia|]. split; [lia|]. split.
      * intros o Ho. destruct we; [|cbn in Ho; lia].
        apply WG. apply (ios_inG_row _ _ _ _ TMAP_A_GOT). unfold TW.SZ_GOT. cbn in Ho. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (TA_GOT + 196) 0 4 (SOff 36 0) e2);
          [cbn [sv_denot]; rewrite X36, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact Ve2].
    + unfold ios_e2_rlc, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U54. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. destruct wl; [|cbn in Ho; lia].
      apply WG. apply (ios_inG_row _ _ _ _ TMAP_A_g_last_counter).
      unfold TW.SZ_g_last_counter. cbn in Ho. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ios_e2_rstk, ios_e2_rfly, ios_e2_rnow, ios_e2_re2, ios_e2_rlc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U8, U27, U28, U54. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold ios_e2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; [exact I|]. split; [|exact I].
    cbn [sv_denot]. rewrite U53, (EOB (A_OBJ 28) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V28.
    rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Carrying a cut across a stretch that writes only below sp           *)
(* ------------------------------------------------------------------ *)

(* A visible byte of two memories with the same view is the same byte, whatever world each is read at. *)
Lemma ios_mbyte_keep : forall (W W' : world segs) m m' a (b : byte),
  aview segs (w_H W') m' a = aview segs (w_H W) m a ->
  mbyte segs (mrestrict (w_H W) m) a = Some b ->
  mbyte segs (mrestrict (w_H W') m') a = Some b.
Proof.
  intros W W' m m' a b E H. unfold aview in E. rewrite H in E. cbn [option_map] in E.
  destruct (mbyte segs (mrestrict (w_H W') m') a) as [b'|] eqn:E'; [|discriminate E].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A garr8 array of the view survives a stretch that keeps its bytes. *)
Lemma ios_garr8_keep : forall (W W' : world segs) m m' base (l : list Z),
  (forall j, (j < length l)%nat ->
     aview segs (w_H W') m' (base + Z.of_nat j) = aview segs (w_H W) m (base + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W) m) base l -> garr8 segs (mrestrict (w_H W') m') base l.
Proof.
  intros W W' m m' base l KV HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk.
  specialize (Hv 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in Hv |- *.
  exact (ios_mbyte_keep W W' m m' _ _ (KV j Hj) Hv).
Qed.

(* The frames' shadow bytes of a state lie below 2 ^ 45: every live side-stack frame ends below alloc_ceiling. *)
Lemma ios_frame_shadow_lo : forall lyc Sc (W : world segs) memc mdc cid pos s,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) -> 0 <= s < 2 ^ 45.
Proof.
  intros lyc Sc W memc mdc cid pos s LAWS HAR Hin Hs.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (@YM05.alloc_ceiling_lt rc) as C1.
  unfold in_zr, shadow_addr, SHADOW_OFF in Hs. cbn [fst snd] in Hs.
  pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)) as D1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
  set (d := frame_addr lyc cid pos / 8) in *.
  set (e := fs_frame_bytes cid / 8) in *.
  clearbody d e. lia.
Qed.

(* A stretch that writes only inside [lo, hi) — a run that stores nothing, or a leaf's own frame — keeps every
   memory fact of the cut: the harness globals, the shadow band and the struct spec_frame lie outside it (the
   globals and the shadow band below 2 ^ 45, the struct and the saved words above sp - IOSEND_FRAME), and the
   frame lies outside io_send's whole stack window (ios_fix's decode_off_win). The journal, the registers and
   the world the stretch moves to come from the stretch itself. *)
Lemma ios_e2_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) (W4 : world segs) mem4 md4
    (regs4 : bvmap 5 word) Bx (lo hi : Z),
  AR_laws segs B ->
  0 < p -> 0 < Z.of_nat (length frame) ->
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  spZ regs - IOSEND_STK <= lo -> hi <= spZ regs - IOSEND_FRAME -> 2 ^ 45 <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W4 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W4 mem4 md4 regs4 Bx.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 W4 mem4 md4 regs4 Bx lo hi
    LAWS Hp0 Hn0 HOFF HSP Hlo Hhi H45 KV AT CUR RG R24.
  destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
  assert (EF : IOSEND_FRAME = 160) by reflexivity.
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ES : SF_SIZE = 80) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof CUR3 as (HJ3 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof (proj1 HJi3) as HAR3.
  (* where the frame lies: a heap block or a fake frame below alloc_ceiling, G, or the machine stack *)
  pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
                ltac:(lia)) as HPL.
  assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ (lo <= a < hi))
    by (intros a Ha; unfold decode_off_win in HOFF; lia).
  assert (KSF : forall a, spZ regs - IOSEND_FRAME + IOS_F_OFF <= a <
                          spZ regs - IOSEND_FRAME + IOS_F_OFF + SF_SIZE -> ~ (lo <= a < hi))
    by (intros a Ha; lia).
  assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                  aview segs (w_H W4) mem4 s = aview segs (w_H W3) mem3 s)
    by (intros s Hs; apply KV; lia).
  split; [exact CUR|].
  split.
  { (* the saved words *)
    unfold ios_saved in SAVED |- *. rewrite Forall_forall in SAVED |- *. intros o Ho.
    assert (Hfo : 0 < fst o <= 72).
    { unfold IOS_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- (SAVED o Ho). apply rdword_ext. intros kk Hkk. apply KV; lia. }
  split; [exact RG|]. split; [exact R24|].
  split.
  { (* the struct *)
    destruct SFR as (Hfp0 & Hfp8 & SB & HG & HL & HR). split; [exact Hfp0|]. split; [exact Hfp8|].
    exists SB. split; [|exact (conj HL HR)].
    refine (ios_garr8_keep W3 W4 mem3 mem4 _ _ _ HG). intros j Hj. rewrite length_map in Hj.
    apply KV; [lia | apply KSF; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W4 mem3 mem4
            (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
            (fun a Ha => KV a ltac:(lia) (KSF a Ha)) KSH). }
  split.
  { (* the frame *)
    refine (ios_garr8_keep W3 W4 mem3 mem4 _ _ _ GARR). intros j Hj. rewrite length_map in Hj.
    apply KV; [destruct HPL as [Pl|Pl]; lia | apply KFR; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W4 mem3 mem4 p (Z.of_nat (length frame)) SRCF
            (fun a Ha => KV a ltac:(destruct HPL as [Pl|Pl]; lia) (KFR a Ha)) KSH). }
  (* the world *)
  apply (tw_kept TMAP_A (aview segs (w_H W3) mem3) _ Bx HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KV; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The fixed facts of the walk this stretch reads, and the cut's values *)
(* ------------------------------------------------------------------ *)

(* The part of io_send_seg_cut.v ios_fix that names neither the memory nor the world: the frame's placement
   against io_send's stack window, and the window itself. *)
Definition ios_e2_fix (STK sp0 : Z) (regs : bvmap 5 word) (p : Z) (frame : list byte) : Prop :=
  0 < p /\ 0 < Z.of_nat (length frame) /\
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - IOSEND_STK /\ spZ regs <= sp0 /\
  alloc_ceiling <= spZ regs - IOSEND_STK /\ spZ regs <= 2 ^ 47 /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B).

(* The five values the stretch reads: two fields of the struct and three harness words. *)
Definition ios_e2_rty (frame : list byte) : Z := DSpec.sf_retry (TC.rf frame).
Definition ios_e2_snd (frame : list byte) : Z := DSpec.sf_send (TC.rf frame).
Definition ios_e2_flyr (Bx : list byte) : Z := TW.u_at Bx TW.A_M_fly_retries 4.
Definition ios_e2_now (Bx : list byte) : Z := TW.u_at Bx TW.OFF_g_now 8.
Definition ios_e2_e2v (Bx : list byte) : Z := TW.u_at Bx TW.A_GOT_e2 4.

(* Each is where the engine reads it: the struct's fields through check_sent_frame_cg.v trans_sframe_at and
   ios_val_of_garr8, the harness words through TWorldG.v tw_read_val at the M, g_now and GOT rows of TMAP_A. *)
Lemma ios_e2_cut_vals : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx,
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + 38) 2 (ios_e2_rty frame) /\
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + 40) 4 (ios_e2_snd frame) /\
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (TA_M + 108) 4 (ios_e2_flyr Bx) /\
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (TA_g_now + 0) 8 (ios_e2_now Bx) /\
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (TA_GOT + 196 + 0) 4 (ios_e2_e2v Bx) /\
  0 <= ios_e2_rty frame < 2 ^ 16 /\ 0 <= ios_e2_snd frame < 2 ^ 32 /\
  0 <= ios_e2_flyr Bx < 2 ^ 32 /\ 0 <= ios_e2_now Bx < 2 ^ 64 /\ 0 <= ios_e2_e2v Bx < 2 ^ 32.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem3 md3 regs3 Bx AT.
  destruct AT as (_ & _ & _ & _ & SFR & _ & _ & _ & HTW).
  destruct SFR as (_ & _ & SB & HG & HL & _ & _ & _ & _ & _ & _ & HRTY & HSND & _).
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ERTY : ios_e2_rty frame = TW.u_at SB 30 2) by (unfold ios_e2_rty; rewrite HRTY; reflexivity).
  assert (ESND : ios_e2_snd frame = TW.u_at SB 32 4) by (unfold ios_e2_snd; rewrite HSND; reflexivity).
  pose proof (ios_val_of_garr8 (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + IOS_F_OFF) 30 SB 2 HG
                ltac:(lia) ltac:(rewrite HL; cbn; lia)) as R30.
  pose proof (ios_val_of_garr8 (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + IOS_F_OFF) 32 SB 4 HG
                ltac:(lia) ltac:(rewrite HL; cbn; lia)) as R32.
  split. { rewrite ERTY. replace (spZ regs - IOSEND_FRAME + 38)
             with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 30) by lia. exact R30. }
  split. { rewrite ESND. replace (spZ regs - IOSEND_FRAME + 40)
             with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 32) by lia. exact R32. }
  split.
  { exact (tw_read_val segs (mrestrict (w_H W3) mem3) TMAP_A Bx TW.OFF_M TA_M TW.SZ_M 108 4
             TMAP_A_ok HTW TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)). }
  split.
  { exact (tw_read_val segs (mrestrict (w_H W3) mem3) TMAP_A Bx TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8
             TMAP_A_ok HTW TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)). }
  split.
  { exact (tw_read_val segs (mrestrict (w_H W3) mem3) TMAP_A Bx TW.OFF_GOT TA_GOT TW.SZ_GOT 196 4
             TMAP_A_ok HTW TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)). }
  pose proof (TWL.u_at_range SB 30 2) as Q1. pose proof (TWL.u_at_range SB 32 4) as Q2.
  pose proof (TWL.u_at_range Bx TW.A_M_fly_retries 4) as Q3.
  pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as Q4.
  pose proof (TWL.u_at_range Bx TW.A_GOT_e2 4) as Q5.
  change (8 * Z.of_nat 2) with 16 in Q1. change (8 * Z.of_nat 4) with 32 in Q2, Q3, Q5.
  change (8 * Z.of_nat 8) with 64 in Q4.
  unfold ios_e2_flyr, ios_e2_now, ios_e2_e2v. rewrite ERTY, ESND. repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The head of the stretch: f.retry and its branch (0x830e8 .. 0x830ec) *)
(* ------------------------------------------------------------------ *)

(* The two branches of this stretch test a value against 0. *)
Lemma ios_eqb0 : forall x, 0 <= x < 2 ^ 32 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x 0) as [->|Hne]; [reflexivity|].
  apply Z.eqb_neq. rewrite Zmod_0_l. intro E. Z.div_mod_to_equations. lia.
Qed.

(* The `lhu` of f.retry is the zero-extension of its 16-bit atom (YP0m.v zext_low_sound). *)
Lemma ios_e2_den_zext16 : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 16 ->
  sv_denot E (SExt false 16 (SOff n 0)) = Z_to_bv 64 u.
Proof.
  intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (zext_low_sound false 16 u). f_equal.
  assert (C : zcanon u = u) by (unfold zcanon, M64; apply Z.mod_small; lia).
  unfold zext_low. rewrite C. change (2 ^ Z.of_N 16) with 65536.
  rewrite (Z.mod_small u 65536) by lia. exact C.
Qed.

(* The registers this stretch's runs keep: sp, gp, tp, s0 = len, s1 = p, s3 = the g_fail_next byte, s4 = the
   shadow base, s5 = f.cmd, and s8 .. s11, which io_send never writes. *)
Definition ios_e2_kept : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma ios_e2_regs_step : forall regs (r3 r4 : bvmap 5 word) p frame fail cmd,
  ios_regs regs r3 p frame fail -> YK11.getr r3 21 = w64 cmd ->
  (forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall r : bv 5, In r ios_e2_kept -> YK11.getr r4 r = YK11.getr r3 r) ->
  ios_regs regs r4 p frame fail /\ YK11.getr r4 21 = w64 cmd /\
  (forall r, 24 <= r <= 27 -> YK11.getr r4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
Proof.
  intros regs r3 r4 p frame fail cmd HR G21 G24 M.
  destruct HR as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
  split; [|split].
  - unfold ios_regs.
    rewrite (M 2%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 3%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 4%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 8%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 9%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 19%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)),
            (M 20%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)).
    repeat split; assumption.
  - rewrite (M 21%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)). exact G21.
  - assert (E24 : Z_to_bv 5 24 = 24%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E25 : Z_to_bv 5 25 = 25%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E26 : Z_to_bv 5 26 = 26%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E27 : Z_to_bv 5 27 = 27%bv) by (apply bv_eq; vm_compute; reflexivity).
    intros r Hr.
    assert (HR4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct HR4 as [E|[E|[E|E]]]; subst r.
    + rewrite E24, (M 24%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), <- E24.
      exact (G24 24 ltac:(lia)).
    + rewrite E25, (M 25%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), <- E25.
      exact (G24 25 ltac:(lia)).
    + rewrite E26, (M 26%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), <- E26.
      exact (G24 26 ltac:(lia)).
    + rewrite E27, (M 27%bv ltac:(unfold ios_e2_kept; cbn [In]; tauto)), <- E27.
      exact (G24 27 ltac:(lia)).
Qed.

(* The 2-byte load of f.retry at sp + 38 (io_send's own frame, no instrumented check) and the branch of 0x830ec:
   f.retry = 0 goes to 0x83124, else on to the call setup at 0x830f0. The stretch stores nothing, so its state
   takes no write window and ios_e2_keep carries the cut with an empty one. *)
Lemma ios_e2_head : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail cmd : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc W memc mdc ->
  ios_e2_fix STK sp0 regs p frame ->
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YK11.getr regs3 21 = w64 cmd ->
  (forall mem4 md4 regs4,
     ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4 Bx ->
     YK11.getr regs4 21 = w64 cmd -> ios_e2_rty frame <> 0 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x390) regs4 mem4 md4) Q) ->
  (forall mem4 md4 regs4,
     ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4 Bx ->
     YK11.getr regs4 21 = w64 cmd -> ios_e2_rty frame = 0 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3c4) regs4 mem4 md4) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_E2DATA) regs3 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail cmd
    ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc FIX AT R21 KNZ KZ.
  pose proof AT as AT0.
  destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47 & Hra & Hra4 & Hgp & Htp).
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (ios_e2_cut_vals STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
              ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & V40 & V108 & Vnow & Ve2 & Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8496) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  pose proof (ios_e2_state false false false IOS_E2DATA (spZ regs - IOSEND_FRAME)
                (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx) (ios_e2_e2v Bx)
                W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z1 Z2 Z3 Z4 Z5 V38 V40 V108 Vnow Ve2) as HS.
  set (E0 := ios_e2_E regs3 (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx)
               (ios_e2_e2v Bx)) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_e2_E; apply Eimg_env).
  assert (SHOK : sh_ok segs ios_e2_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
  assert (X32 : ew E0 32 = Z_to_bv 64 (ios_e2_rty frame))
    by (unfold E0, ios_e2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
                TG.G_HARNESS HGX 0 []) as RUN.
  pose proof (paj_branch (PI := PI_transport)) as BR.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_E2DATA)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
      LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) ltac:(lia) ltac:(lia)). }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS (ios_e2_agree regs3 _ _ _ _ _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  destruct (ios_e2_regs_step regs regs3 (ms_regs ms1) p frame fail cmd RG R21 R24 KR)
    as (RG1 & R211 & R241).
  assert (AT1 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx).
  { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx
             (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
             LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(intros a Ha _; exact (KV a Ha)) AT0 CUR1 RG1 R241). }
  assert (ZR : 0 <= ios_e2_rty frame < 2 ^ 32)
    by (change (2 ^ 16) with 65536 in Z1; change (2 ^ 32) with 4294967296; lia).
  pose proof CUR1 as (HJ1 & HFR1 & HPM1 & HMO1 & HKEPT1).
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
                TG.G_HARNESS HGX 0 []) as RUNTO.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* f.retry = 0: the branch is taken, on to the E2 / DATA test at 0x83124 *)
    rewrite (ios_e2_den_zext16 E0 32 (ios_e2_rty frame) X32 Z1) in Hc.
    cbn [branch_taken sv_denot] in Hc. rewrite (ios_eqb0 _ ZR) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x3c4).
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
      apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a [])
        ltac:(lia) ltac:(lia)). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS
                  (ios_e2_agree regs3 _ _ _ _ _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R21 R24 KR2)
      as (RG2 & R212 & R242).
    assert (AT2 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) W3 (ms_mem ms2) md5 (ms_regs ms2) Bx
               (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
               LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(intros a Ha _; exact (KV2 a Ha)) AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3c4) rg mm mdx) Q) end.
    exact (KZ _ _ _ AT2 R212 Hc).
  - (* f.retry <> 0: the call setup of check_inflight_retry at 0x830f0 *)
    rewrite (ios_e2_den_zext16 E0 32 (ios_e2_rty frame) X32 Z1) in Hc.
    cbn [branch_taken sv_denot] in Hc. rewrite (ios_eqb0 _ ZR) in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x390).
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
      apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a [])
        ltac:(lia) ltac:(lia)). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS
                  (ios_e2_agree regs3 _ _ _ _ _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R21 R24 KR2)
      as (RG2 & R212 & R242).
    assert (AT2 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) W3 (ms_mem ms2) md5 (ms_regs ms2) Bx
               (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
               LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(intros a Ha _; exact (KV2 a Ha)) AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x390) rg mm mdx) Q) end.
    exact (KNZ _ _ _ AT2 R212 Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* The E2 / DATA test (0x83124 .. 0x83128)                             *)
(* ------------------------------------------------------------------ *)

Lemma ios_eqb_lit : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. change (2 ^ 32) with 4294967296 in Hx, Hy.
  unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma ios_e2_den_off0 : forall (E : env) n u, ew E n = Z_to_bv 64 u ->
  sv_denot E (SOff n 0) = Z_to_bv 64 u.
Proof.
  intros E n u Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* `li a0, 0xe2` and the branch of 0x83128: s5 <> 0xe2 goes to 0x83160, the DATA arm's head; else on to the
   first leaf call of the E2 arm at 0x8312c. Like the head, the stretch stores nothing. *)
Lemma ios_e2_test : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail cmd : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc W memc mdc ->
  ios_e2_fix STK sp0 regs p frame ->
  ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YK11.getr regs3 21 = w64 cmd -> 0 <= cmd < 256 ->
  (forall mem4 md4 regs4,
     ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4 Bx ->
     YK11.getr regs4 21 = w64 cmd -> cmd <> TC.SPEC_CMD_E2 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_DATA) regs4 mem4 md4) Q) ->
  (forall mem4 md4 regs4,
     ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4 Bx ->
     YK11.getr regs4 21 = w64 cmd -> cmd = TC.SPEC_CMD_E2 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3cc) regs4 mem4 md4) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3c4) regs3 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail cmd
    ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc FIX AT R21 HC256 KDATA KE2.
  pose proof AT as AT0.
  destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47 & Hra & Hra4 & Hgp & Htp).
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (ios_e2_cut_vals STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
              ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & V40 & V108 & Vnow & Ve2 & Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8496) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  pose proof (ios_e2_state false false false (IOS_AT 0x3c4) (spZ regs - IOSEND_FRAME)
                (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx) (ios_e2_e2v Bx)
                W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z1 Z2 Z3 Z4 Z5 V38 V40 V108 Vnow Ve2) as HS.
  set (E0 := ios_e2_E regs3 (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr Bx) (ios_e2_now Bx)
               (ios_e2_e2v Bx)) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_e2_E; apply Eimg_env).
  assert (SHOK : sh_ok segs ios_e2_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
  assert (X21 : ew E0 21 = Z_to_bv 64 cmd)
    by (unfold E0, ios_e2_E; rewrite (ew_Eimg_Ereg_nat regs3 _ 21%nat 21%bv eq_refl); exact R21).
  assert (DC : sv_denot E0 (SOff 21 0) = Z_to_bv 64 cmd) by exact (ios_e2_den_off0 E0 21 cmd X21).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
                TG.G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
                TG.G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transport)) as BR.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x3c4)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
      LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) ltac:(lia) ltac:(lia)). }
  pose proof CUR1 as (HJ1 & HFR1 & HPM1 & HMO1 & HKEPT1).
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS (ios_e2_agree regs3 _ _ _ _ _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  destruct (ios_e2_regs_step regs regs3 (ms_regs ms1) p frame fail cmd RG R21 R24 KR)
    as (RG1 & R211 & R241).
  assert (AT1 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx).
  { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx
             (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
             LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(intros a Ha _; exact (KV a Ha)) AT0 CUR1 RG1 R241). }
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* s5 <> 0xe2: the branch is taken, the DATA arm's head at 0x83160 *)
    rewrite DC in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ios_eqb_lit cmd 226 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_DATA.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
      apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a [])
        ltac:(lia) ltac:(lia)). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS
                  (ios_e2_agree regs3 _ _ _ _ _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R21 R24 KR2)
      as (RG2 & R212 & R242).
    assert (AT2 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) W3 (ms_mem ms2) md5 (ms_regs ms2) Bx
               (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
               LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(intros a Ha _; exact (KV2 a Ha)) AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_DATA) rg mm mdx) Q) end.
    exact (KDATA _ _ _ AT2 R212 Hc).
  - (* s5 = 0xe2: on to check_state_wake at 0x8312c *)
    rewrite DC in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ios_eqb_lit cmd 226 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (IOS_AT 0x3cc).
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      repeat (apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
      apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a [])
        ltac:(lia) ltac:(lia)). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS
                  (ios_e2_agree regs3 _ _ _ _ _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ios_e2_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R21 R24 KR2)
      as (RG2 & R212 & R242).
    assert (AT2 : ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { apply (ios_e2_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) W3 (ms_mem ms2) md5 (ms_regs ms2) Bx
               (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
               LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(intros a Ha _; exact (KV2 a Ha)) AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3cc) rg mm mdx) Q) end.
    exact (KE2 _ _ _ AT2 R212 Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

(* The entry is the dispatch segment's E2 / DATA exit: io_send_seg_cut.v ios_at_csf at the world W2 that
   check_sent_frame left, with s5 = f.cmd beside it. Each exit is at the world its own stretch leaves: the DATA
   arm's head and the frame in flight at W2, since neither reaches a donor call; the epilogue at a world W3,
   which the retry arm's check_inflight_retry creates. *)
Definition ios_e2_seg_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs : bvmap 5 word) (p : Z) (frame : list byte) (cmd : Z) (Bw Bw' : list byte)
         ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
    ios_e2_laws ->
    ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
    ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw
      ly2 S2 W2 mem2 md2 regs2 ->
    YK11.getr regs2 21 = w64 cmd ->
    cmd = DSpec.sf_cmd (TC.rf frame) -> 0 <= cmd < 256 ->
    (cmd = TC.SPEC_CMD_E2 \/ cmd = TC.SPEC_CMD_DATA) ->
    TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
    ios_arm Bw frame = Some (Bw', tt) ->
    (* the DATA arm's head at 0x83160 (another segment's): no call and no store on the way *)
    (forall ly3 S3 mem3 md3 regs3,
       cmd = TC.SPEC_CMD_DATA -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
       ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw
         ly3 S3 W2 mem3 md3 regs3 ->
       YK11.getr regs3 21 = w64 cmd ->
       SRr segs W2 (@cfg_at fx segs (transport_text + IOS_DATA) regs3 mem3 md3) Q) ->
    (* the frame in flight (transport_text + IOS_FLY): the E2 arm with bit 0 of the entry g_fail_next clear.
       Its two callees are leaves, so the world is still W2. *)
    (forall ly3 S3 mem3 md3 regs3 B5,
       cmd = TC.SPEC_CMD_E2 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
       TC.truth (TW.g_fail_next Bw) = false -> Bw' = ios_fly frame B5 ->
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly3 S3 W2 mem3 md3 regs3 B5 ->
       YK11.getr regs3 21 = w64 cmd ->
       SRr segs W2 (@cfg_at fx segs (transport_text + IOS_FLY) regs3 mem3 md3) Q) ->
    (* the epilogue (transport_text + IOS_EPI): the retry arm, whose donor call leaves the world W3, and the E2
       arm with that bit set, which stays at W2 *)
    (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
       ios_e2_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
         ly3 S3 W3 mem3 md3 regs3 Bw' ->
       SRr segs W3 (@cfg_at fx segs (transport_text + IOS_EPI) regs3 mem3 md3) Q) ->
    SRr segs W2 (@cfg_at fx segs (transport_text + IOS_E2DATA) regs2 mem2 md2) Q.

End e2.
