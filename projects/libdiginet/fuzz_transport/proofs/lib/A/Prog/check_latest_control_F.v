From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_control_c check_latest_control_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldAKept.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_latest_control_contract_F (image A, entry 0x8420c, frame 16 bytes), with StepF's step: each data
   access is closed from the rng premise of exactly the range it touches.

   The walk:
     0x8420c-0x84210  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x84214-0x8421c  a1 = the 8-byte load at GOT_CELL_K, then the 8-byte load at CELL_K: 0x7fff8000.
     0x84220-0x8422c  a0 = fp + 32; a2 = a0 >> 3; a2 = a2 + 0x7fff8000; a1 = the signed shadow byte k at a2.
     0x84230          bnez a1: k = 0 falls through to the load; k <> 0 goes to 0x84250-0x84258 (a2 = (a0 & 7) + 3,
                      blt a2,a1 back to 0x84234), as fp + 32 is 8-aligned and addressable for 4 bytes gives 3 < k.
     0x84234          a0 = the 4-byte load at fp + 32, sign-extended: send.
     0x84238-0x8423c  a1 = the 4-byte load at 0x5df1b4, sign-extended: M.host_counter.
     0x84240          bne a0,a1 falls through: the model premise gives send = M.host_counter, so the member's 4 bytes
                      are the world's 4 bytes at A_M_host_counter and the two loads read the same bytes.
     0x84244-0x8424c  ld ra; addi sp; ret.
   The report call (0x8425c) and the trap path (0x84260 / 0x84264) are never reached.

   The world relation after the run: the run writes only its frame (munch), which lies outside the hull of the
   harness globals (off_stk premise), so tw_at holds of the same Bw (TWorldAKept.csw_kept). *)

(* The 4 bytes of a 32-bit world field, written back as put 4 of their value. *)
Lemma put_u_at4 : forall (B : list byte) k, 0 <= k -> k + 4 <= Z.of_nat (length B) ->
  TW.put 4 (TW.u_at B k 4) = TW.sub B k 4.
Proof.
  intros B k Hk Hl. pose proof (TWorldLemmas.length_sub B k 4 Hk Hl) as L. unfold TW.put, TW.u_at.
  remember (TW.sub B k 4) as s eqn:Es. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* All the bytes bs at a, read at once. *)
Lemma ka_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* The same read at a register value w whose number is a. *)
Lemma ka_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). apply ka_rd_all; assumption.
Qed.

(* The shadow byte of an 8-aligned 4-byte addressable range: 0, or above 3 (the range's last byte, a + 3). *)
Lemma ka_addr4 : forall m a, addressable m a 4 -> a mod 8 = 0 ->
  0 <= a /\ a + 4 <= APPMEM_END /\ app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\
            (bv_signed k = 0 \/ (3 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m a (P0 & N0 & PE & AB) M8.
  destruct (AB 0 ltac:(lia)) as (APP & _). rewrite Z.add_0_r in APP.
  destruct (AB 3 ltac:(lia)) as (_ & k & MK & SK).
  assert (E : (a + 3) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  assert (M3 : (a + 3) mod 8 = 3) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in MK. rewrite E in MK. unfold shadow_ok in SK. rewrite M3 in SK.
  split; [lia|]. split; [lia|]. split; [exact APP|]. exists k. split; [exact MK | exact SK].
Qed.

(* A shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma ka_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

Theorem check_latest_control_holds_F : check_latest_control_contract_F.
Proof.
  unfold check_latest_control_contract_F, CHECK_LATEST_CONTROL, CHECK_LATEST_CONTROL_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' fp frame HA0 HP0 HP8 BSEND HW HM ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D32 A32
    RFR RGOT RCELL RS32 R32 RHOST.
  (* the model: send = M.host_counter and Bw' = Bw *)
  assert (HF : DgnSpec.sf_send (TC.rf frame) = TW.M_host_counter Bw /\ Bw' = Bw).
  { unfold TC.check_latest_control_m in HM.
    destruct (Z.eqb_spec (DgnSpec.sf_send (TC.rf frame)) (TW.M_host_counter Bw)) as [E|E]; cbn [negb] in HM;
      [|discriminate HM].
    split; [exact E|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as [HS ->]. clear HM.
  (* the 4 bytes of M.host_counter, as raw memory, and the member's bytes are the same list *)
  pose proof (tw_len TMAP_A _ Bw HW) as LW.
  assert (L4 : length (TW.sub Bw TW.A_M_host_counter 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_host_counter, TW.OFF_M; lia|].
    rewrite LW. unfold TW.A_M_host_counter, TW.OFF_M, TW.W_LEN. lia. }
  rewrite HS in BSEND. unfold TW.M_host_counter in BSEND.
  rewrite put_u_at4 in BSEND
    by (unfold TW.A_M_host_counter, TW.OFF_M; try rewrite LW; unfold TW.W_LEN; lia).
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 84 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BH.
  change (TA_M + 84) with 6156724 in BH. change (TW.OFF_M + 84) with TW.A_M_host_counter in BH.
  rewrite check_latest_control_host_at in RHOST.
  (* the argument as a register value *)
  destruct (ka_addr4 m _ A32 ltac:(Z.div_mod_to_equations; lia)) as (P32 & E32 & APP32 & k32 & MK32 & SK32).
  clear A32.
  unfold APPMEM_END in E32.
  assert (U0 : bv_unsigned a0 = fp) by (subst a0; apply unsigned_lit; lia).
  clear HA0. subst fp.
  (* the byte facts stay on m: the store of ra would transport or drop them *)
  assert (KEEP : bytes_at rsegs m (bv_unsigned a0 + 32) (TW.sub Bw TW.A_M_host_counter 4) /\
                 bytes_at rsegs m 6156724 (TW.sub Bw TW.A_M_host_counter 4)) by (split; assumption).
  clear BSEND BH.
  unfold off_stk in DGOT, DCELL, D32.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  unfold GOT_CELL_K, CELL_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RS32.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x8420c-0x84210: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (GCK0 : bytes_at rsegs m0 671888 (le8 (wa 707064)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 707064 (le8 (wa 2147450880)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  pose proof (ka_rd_all m0 _ _ 8 GCK0 (length_le8 _)) as RDG.
  pose proof (ka_rd_all m0 _ _ 8 CK0 (length_le8 _)) as RDS.
  clear GCK0 CK0 GCK CK.
  pose proof (ka_shadow_tp m m0 _ _ _ k32 MU1 ltac:(lia) APW1 APW2 APP32 MK32) as M32. unfold ASAN_K in M32.
  destruct KEEP as (BS & BH).
  assert (BS0 : bytes_at rsegs m0 (bv_unsigned a0 + 32) (TW.sub Bw TW.A_M_host_counter 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite L4; lia | exact BS]).
  assert (BH0 : bytes_at rsegs m0 6156724 (TW.sub Bw TW.A_M_host_counter 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite L4; lia | exact BH]).
  pose proof (ka_rd_all m0 _ _ 4 BH0 L4) as RDH.
  clear BS BH.
  (* 0x84214-0x8421c: a1 = 0x7fff8000 *)
  step. step. step.
  (* 0x84220-0x8422c: the shadow byte of fp + 32 *)
  step. gen_addi a0 w32 U32.
  pose proof (rng_sub' _ _ _ (bv_unsigned w32) 4 R32 ltac:(lia)) as RW32.
  step. gen_shr w32 g32 G32.
  rewrite U32 in G32.
  step. gen_addi g32 h32 H32.
  pose proof (rng_sub' _ _ _ (bv_unsigned h32) 1 RS32 ltac:(lia)) as RH32.
  pose proof (rdw0 m0 h32 _ _ M32 ltac:(lia)) as R. step. clear R.
  (* 0x84230: bnez on k *)
  step.
  assert (M0 : (bv_unsigned a0 + 32) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  destruct SK32 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k32) 0) ltac:(lia)); cbn [negb]; step; step; step;
     rewrite ?land7, ?U32, ?M0, ?unsigned_lit by lia; rewrite ?Z.add_0_l;
     rewrite (lts_low 3 k32 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  (* 0x84234: a0 = send; 0x84238-0x8423c: a1 = M.host_counter: the same 4 bytes *)
  all: pose proof (ka_rdw m0 w32 _ _ 4 BS0 L4 U32) as R; step; clear R.
  all: step; step.
  all: rewrite !lw_world.
  (* 0x84240: bne falls through *)
  all: step; if_false.
  (* 0x84244-0x8424c: ld ra; addi sp; ret *)
  all: step; step; step.
  all: apply evtF_done; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  all: split; [reflexivity|].
  all: apply (TWorldAKept.csw_kept m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
Qed.

Print Assumptions check_latest_control_holds_F.
