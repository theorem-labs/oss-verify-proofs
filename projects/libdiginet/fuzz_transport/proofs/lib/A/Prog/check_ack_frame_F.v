From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_ack_frame_c check_ack_frame_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_ack_frame_contract_F (image A, entry 0x8415c, frame 16 bytes), with StepF's step: each data access
   is closed from the rng premise of the range it touches.

   The walk (listing DgnTransportList.v, slots 3006-3049):
     0x8415c-0x84160  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x84164-0x8416c  auipc a1; ld a1,..(a1); ld a2,0(a1): a1 = CELL_K (the 8 bytes at GOT_CELL_K), a2 = 0x7fff8000
                      (the 8 bytes at CELL_K), both from asan_cells.
     0x84170-0x84180  addi a1,a0,36; srli a3,a1,3; add a3,a3,a2; lb a3,0(a3); bnez a3,0x841e0: the shadow byte of
                      fp + 36. fp mod 8 = 0, so [fp + 36, fp + 40) holds byte 7 of its granule, and addressable gives
                      that byte's shadow 0: the branch falls through.
     0x84184          lw a1,0(a1): f->ack, sign-extended.
     0x84188-0x8418c  auipc a3; lw a3,..(a3): the 4 bytes at 0x5e53e0 = g_rx_send, by tw_at sub Bw OFF_g_rx_send 4,
                      sign-extended: s32_at Bw OFF_g_rx_send (lw_world).
     0x84190          bne a1,a3,0x841d8: not taken. The model gives sf_ack = g_rx_send Bw = u_at Bw OFF_g_rx_send 4,
                      which is below 2^32, so both registers hold Z_to_bv 64 (s32_at Bw OFF_g_rx_send).
     0x84194-0x841a4  the shadow byte of fp + 56 (lbu): fp + 56 is 8-aligned, so the byte is 0 and bnez falls through.
     0x841a8-0x841ac  ld a1,0(a1): f->body_len = 0 (model); bnez a1 falls through.
     0x841b0-0x841c0  the shadow byte of fp + 30 (lb): [fp + 30, fp + 32) holds byte 7 of its granule, so it is 0.
     0x841c4-0x841c8  lhu a0,0(a0): f->retry = 0 (model); bnez a0 falls through.
     0x841cc-0x841d4  ld ra,8(sp); addi sp,sp,16; ret.
   The compares at 0x841e0 / 0x841f4, the calls of the report entries (0x841f0, 0x84200, 0x84208) and the trap path
   (0x841d8 __asan_handle_no_return, 0x841dc abort) are never reached.

   The world after: the run writes only its frame (munch), which lies outside the hull of the 18 payload ranges
   (off_stk premise), so TMAP_A_kept keeps tw_at with the same Bw. *)

(* All the bytes bs at a, read at once. *)
Lemma caf_rd : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* The same read at a register value w whose number is a. *)
Lemma caf_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). exact (caf_rd m a bs n H L).
Qed.

(* A byte whose signed value is 0 has unsigned value 0. *)
Lemma caf_signed0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (byte_range k) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

(* An addressable range of n bytes at a that holds byte 7 of the granule of a: the shadow byte of a is 0. *)
Lemma caf_shadow0 : forall m a n, addressable m a n -> 7 - a mod 8 < n ->
  app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ bv_signed k = 0 /\ bv_unsigned k = 0.
Proof.
  intros m a n (P0 & N0 & PE & AB) Hn.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  destruct (AB 0 ltac:(lia)) as (APP & _). rewrite Z.add_0_r in APP.
  destruct (AB (7 - a mod 8) ltac:(lia)) as (_ & k & MK & SK).
  assert (E : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  assert (M7 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in MK. rewrite E in MK. unfold shadow_ok in SK. rewrite M7 in SK.
  assert (S0 : bv_signed k = 0) by lia.
  split; [exact APP|]. exists k. split; [exact MK|]. split; [exact S0 | exact (caf_signed0 k S0)].
Qed.

(* The shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma caf_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

Theorem check_ack_frame_holds_F : check_ack_frame_contract_F.
Proof.
  unfold check_ack_frame_contract_F, CHECK_ACK_FRAME, CHECK_ACK_FRAME_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fp lo frame Bw Bw' HP0 HP8 B36 B56 B30 HW HMOD ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D36 A36 D56 A56 D30 A30
    RFR RGOT RCELL RS36 R36 RRX RS56 R56 RS30 R30.
  (* the model: ack = g_rx_send, body_len = 0, retry = 0 (fuzz_transport.c:428-429), and Bw' = Bw *)
  assert (HM : sf_ack (TC.rf frame) = TW.g_rx_send Bw /\ sf_body_len (TC.rf frame) = 0 /\
               sf_retry (TC.rf frame) = 0 /\ Bw' = Bw).
  { revert HMOD. unfold TC.check_ack_frame_m. cbv zeta.
    destruct (Z.eqb_spec (sf_ack (TC.rf frame)) (TW.g_rx_send Bw)) as [E1|E1];
      destruct (Z.eqb_spec (sf_body_len (TC.rf frame)) 0) as [E2|E2];
      destruct (Z.eqb_spec (sf_retry (TC.rf frame)) 0) as [E3|E3];
      cbn [negb orb]; intros HMOD; try discriminate HMOD.
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HMOD)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HM as (EA & EL & ER & ->). clear HMOD.
  (* the machine compares the sign extensions of the two 32-bit words; the model's equality gives them *)
  assert (XEQ : sx32 (Z_to_bv 64 (sf_ack (TC.rf frame))) = Z_to_bv 64 (TW.s32_at Bw TW.OFF_g_rx_send)).
  { unfold sx32, TW.s32_at. rewrite EA. unfold TW.g_rx_send.
    pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_rx_send 4) as R. change (8 * Z.of_nat 4) with 32 in R.
    rewrite unsigned_lit by lia. reflexivity. }
  (* fp as the number of the register a0 *)
  pose proof (bytes_at_bound rsegs m _ _ B56) as BB. rewrite TWorldLemmas.length_put in BB.
  change (Z.of_nat 8) with 8 in BB.
  remember (Z_to_bv 64 fp) as a0 eqn:E0.
  assert (U0 : bv_unsigned a0 = fp) by (subst a0; apply unsigned_lit; lia).
  clear E0. subst fp.
  (* the three fields in the cell forms of the load step *)
  rewrite <- TWorldLemmas.le4_put in B36.
  rewrite EL, <- TWorldLemmas.le8_put in B56.
  rewrite ER, <- TWorldLemmas.le2_put in B30.
  (* the shadow byte of each field is 0 *)
  destruct (caf_shadow0 m _ 4 A36 ltac:(Z.div_mod_to_equations; lia)) as (APP36 & k36 & MK36 & S36 & _).
  destruct (caf_shadow0 m _ 8 A56 ltac:(Z.div_mod_to_equations; lia)) as (APP56 & k56 & MK56 & _ & Z56).
  destruct (caf_shadow0 m _ 2 A30 ltac:(Z.div_mod_to_equations; lia)) as (APP30 & k30 & MK30 & S30 & _).
  clear A36 A56 A30.
  unfold off_stk in D36, D56, D30, DGOT, DCELL.
  unfold GOT_CELL_K, CELL_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RS36, RS56, RS30.
  rewrite check_ack_frame_rx_send_at in RRX.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  (* the 4 bytes of g_rx_send, as raw memory *)
  assert (L4 : length (TW.sub Bw TW.OFF_g_rx_send 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_rx_send; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_g_rx_send, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_rx_send TA_g_rx_send TW.SZ_g_rx_send 0 4 TMAP_A_ok HW
    TMAP_A_g_rx_send ltac:(lia) ltac:(unfold TW.SZ_g_rx_send; lia)) as BF.
  change (TA_g_rx_send + 0) with 0x5e53e0 in BF. change (TW.OFF_g_rx_send + 0) with TW.OFF_g_rx_send in BF.
  (* keep the byte facts off transport_chunks: they are carried past the ra store by hand *)
  pose proof (conj BF (conj B36 (conj B56 B30))) as KEEP. clear BF B36 B56 B30.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x8415c-0x84160: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  destruct KEEP as (BF & B36 & B56 & B30).
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (GCK0 : bytes_at rsegs m0 0xa4090 (le8 (wa 0xac9f8)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 0xac9f8 (le8 (wa 0x7fff8000)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  pose proof (caf_rd m0 _ _ 8 GCK0 (length_le8 _)) as RDG.
  pose proof (caf_rd m0 _ _ 8 CK0 (length_le8 _)) as RDS.
  clear GCK0 CK0 GCK CK.
  assert (BF0 : bytes_at rsegs m0 0x5e53e0 (TW.sub Bw TW.OFF_g_rx_send 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite L4; lia | exact BF]).
  pose proof (caf_rd m0 _ _ 4 BF0 L4) as RDF.
  assert (B36' : bytes_at rsegs m0 (bv_unsigned a0 + 36) (le4 (Z_to_bv 64 (sf_ack (TC.rf frame)))))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le4; lia | exact B36]).
  assert (B56' : bytes_at rsegs m0 (bv_unsigned a0 + 56) (le8 (Z_to_bv 64 0)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact B56]).
  assert (B30' : bytes_at rsegs m0 (bv_unsigned a0 + 30) (le2 (Z_to_bv 64 0)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le2; lia | exact B30]).
  clear BF BF0 B36 B56 B30.
  pose proof (caf_shadow_tp m m0 _ _ _ k36 MU1 ltac:(lia) APW1 APW2 APP36 MK36) as M36.
  pose proof (caf_shadow_tp m m0 _ _ _ k56 MU1 ltac:(lia) APW1 APW2 APP56 MK56) as M56.
  pose proof (caf_shadow_tp m m0 _ _ _ k30 MU1 ltac:(lia) APW1 APW2 APP30 MK30) as M30.
  unfold ASAN_K in M36, M56, M30. clear MK36 MK56 MK30.
  (* 0x84164-0x8416c: a1 = CELL_K, a2 = 0x7fff8000 *)
  step. step. step.
  (* 0x84170-0x8417c: the shadow byte of fp + 36 *)
  step. gen_addi a0 w36 U36.
  pose proof (rng_sub' _ _ _ (bv_unsigned w36) 4 R36 ltac:(lia)) as RW36.
  step. gen_shr w36 g36 G36. rewrite U36 in G36.
  step. gen_addi g36 h36 H36.
  pose proof (rng_sub' _ _ _ (bv_unsigned h36) 1 RS36 ltac:(lia)) as RH36.
  pose proof (rdw0 m0 h36 _ _ M36 ltac:(lia)) as R. step. clear R.
  (* 0x84180: the shadow byte is 0, on to the load *)
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) S36). cbn [negb].
  (* 0x84184: a1 = f->ack *)
  pose proof (caf_rdw m0 w36 _ _ 4 B36' (length_le4 _) ltac:(lia)) as R. step. clear R.
  rewrite XEQ.
  (* 0x84188-0x8418c: a3 = g_rx_send *)
  step. step. rewrite lw_world.
  remember (TW.s32_at Bw TW.OFF_g_rx_send) as vrx eqn:Evrx.
  (* 0x84190: bne a1,a3 falls through *)
  step. if_false.
  (* 0x84194-0x841a0: the shadow byte of fp + 56 *)
  step. gen_addi a0 w56 U56.
  pose proof (rng_sub' _ _ _ (bv_unsigned w56) 8 R56 ltac:(lia)) as RW56.
  step. gen_shr w56 g56 G56. rewrite U56 in G56.
  step. gen_addi g56 h56 H56.
  pose proof (rng_sub' _ _ _ (bv_unsigned h56) 1 RS56 ltac:(lia)) as RH56.
  pose proof (rdw0 m0 h56 _ _ M56 ltac:(lia)) as R. step. clear R.
  (* 0x841a4: the shadow byte is 0, on to the load *)
  step. if_cases HS56; [exfalso; zify_cond HS56; rewrite ?zxb_u in HS56; first [lia | Z.div_mod_to_equations; lia] |].
  (* 0x841a8-0x841ac: a1 = f->body_len = 0; bnez falls through *)
  pose proof (caf_rdw m0 w56 _ _ 8 B56' (length_le8 _) ltac:(lia)) as R. step. clear R.
  step. if_false.
  (* 0x841b0-0x841bc: the shadow byte of fp + 30 *)
  step. gen_addi a0 w30 U30.
  pose proof (rng_sub' _ _ _ (bv_unsigned w30) 2 R30 ltac:(lia)) as RW30.
  step. gen_shr w30 g30 G30. rewrite U30 in G30.
  step. gen_addi g30 h30 H30.
  pose proof (rng_sub' _ _ _ (bv_unsigned h30) 1 RS30 ltac:(lia)) as RH30.
  pose proof (rdw0 m0 h30 _ _ M30 ltac:(lia)) as R. step. clear R.
  (* 0x841c0: the shadow byte is 0, on to the load *)
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) S30). cbn [negb].
  (* 0x841c4-0x841c8: a0 = f->retry = 0; bnez falls through *)
  pose proof (caf_rdw m0 w30 _ _ 2 B30' (length_le2 _) ltac:(lia)) as R. step. clear R.
  step. if_false.
  (* 0x841cc-0x841d4: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (TMAP_A_kept (segs := rsegs) m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.
