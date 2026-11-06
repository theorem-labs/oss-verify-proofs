(* check_inflight_retry_seg_run: the three footprint runs (lib/Lib/ExecF.v evtF) of check_inflight_retry in image A
   (fuzz_transport.asan, entry 0x84268 = transport_sigma TS_check_inflight_retry, 66 words; listing
   lib/A/Prog/DgnTransportList.v, slots 3073 .. 3138), cut at its two calls of the bcmp wrapper:
     cir_run1_F  0x84268 .. the call at 0x842c8: the frame (`addi sp,sp,-48`, ra and s0 .. s4 saved at sp - 8 ..
                 sp - 48), s1 = len, s3 = M, the load of M.fly.on (M + 96) and its `beqz` to the trap, s2 = fa,
                 `bltu s1,28` to the trap, the load of M.fly.len (M + 1640) and its `bne` to the trap, s0 = fp, the
                 shadow base through its GOT word into s4, then a0 = fa, a1 = M + 120, a2 = 26 and the call;
     cir_run2_F  0x842cc .. the call at 0x842dc: `bnez a0` to the trap (the first call answered 0), then a0 = fa + 28,
                 a2 = len - 28, a1 = M + 148 and the call;
     cir_run3_F  0x842e0 .. the `ret` at 0x84354: `bnez a0` to the trap (the second call answered 0), the instrumented
                 check of the 2-byte load at fp + 30 (its shadow byte is 0), M.fly.retries (M + 108) + 1 against
                 f->retry, g_cfg.max_retries (g_cfg + 32) against f->retry, g_now - M.fly.sent (M + 112) against
                 g_cfg.ack_timeout_ms (g_cfg + 28) * 1000, then the epilogue.
   Every test that goes to the trap at 0x84358 is decided by its premise (the facts the model premise gives,
   lib/A/Prog/check_inflight_retry_cgW.v), so the trap and the error path at 0x8436c are not reached. The functional
   content is the plain walk lib/Prog/T/check_inflight_retry.v (its build-independent lemmas through PWR). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_inflight_retry.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module PWR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.check_inflight_retry.

(* ---- the addresses: the entry and the trampoline are the listing's names, every interior point an offset ---- *)

Definition CIR_ENTRY : Z := transport_sigma TS_check_inflight_retry.
Definition CIR_AT (off : Z) : Z := CIR_ENTRY + off.
Definition CIR_BCMP : Z := transport_sigma TS___interceptor_trampoline_bcmp.
Definition CIR_P_BODY : Z := CIR_AT 0x1c.   (* 0x84284 `mv s1,a1`, after the prologue *)
Definition CIR_RET1 : Z := CIR_AT 0x64.     (* 0x842cc, the first call returns here *)
Definition CIR_RET2 : Z := CIR_AT 0x78.     (* 0x842e0, the second call returns here *)

(* The 48-byte frame: s4, s3, s2, s1, s0 and ra at sp - 48 .. sp - 8 (`sd ra,40(sp)` 0x8426c .. `sd s4,0(sp)`
   0x84280, after `addi sp,sp,-48`). *)
Definition cir_fr (c4 c3 c2 c1 c0 cra : word) : list cell := [C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The start pc of a piece is a CIR_AT name; StepF's step reads a literal. *)
Ltac cir_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let v := eval vm_compute in pc in change pc with v
  end.

(* A test the run does not take: its condition is false. *)
Ltac cir_brf tac := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac]
  end.

(* ---- the prologue: 0x84268 .. 0x84284 ---- *)

Lemma cir_pro_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CIR_P_BODY) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (cir_fr s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIR_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO RFR.
  cir_pc.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. exact FR.
Qed.

(* ---- run 1 after the prologue: 0x84284 .. the call at 0x842c8 ---- *)

Lemma cir_body1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fa len fp : Z) (Bw : list byte),
    ov_read_bytes rsegs m (wa (TA_M + 96)) 4 = Some (TW.sub Bw 96 4) ->
    ov_read_bytes rsegs m (wa (TA_M + 1640)) 8 = Some (TW.sub Bw 1640 8) ->
    ov_read_bytes rsegs m (wa GOT_CELL_K) 8 = Some (le8 (wa CELL_K)) ->
    ov_read_bytes rsegs m (wa CELL_K) 8 = Some (le8 (wa ASAN_K)) ->
    ExecF.rng RNG (TA_M + 96) 4 -> ExecF.rng RNG (TA_M + 1640) 8 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    TW.s32_at Bw 96 <> 0 -> len = TW.u_at Bw 1640 8 -> 28 <= len < 2 ^ 63 ->
    0 <= fa < 2 ^ 63 -> 0 <= fp < 2 ^ 63 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 CIR_RET1) sp gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                              (Z_to_bv 64 fa) (Z_to_bv 64 (TA_M + 120)) (Z_to_bv 64 26) a3 a4 a5 a6 a7
                              (Z_to_bv 64 fa) (Z_to_bv 64 TA_M) (Z_to_bv 64 ASAN_K) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 CIR_BCMP) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 len) (Z_to_bv 64 fp) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIR_P_BODY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fa len fp Bw RON RLEN RGC RCK GON GLEN GGC GCK HON HLEN HL28 HFA HFP.
  cir_pc. unfold GOT_CELL_K, CELL_K, ASAN_K, wa in *.
  change (TA_M + 96) with 6156736 in *. change (TA_M + 1640) with 6158280 in *.
  step. step. step.
  step. rewrite lw_world.
  step.
  pose proof (TWorldLemmas.s32_range Bw 96) as R96.
  pose proof (TWorldLemmas.u_at_range Bw 1640 8) as R1640. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R1640.
  (* 0x84294 beqz a1: M.fly.on <> 0 *)
  cir_brf ltac:(rewrite PWR.cir_eqb0_s32 by lia; apply Z.eqb_neq; exact HON).
  (* 0x84298 mv s2,a0; 0x8429c li a0,28; 0x842a0 bltu s1,a0: 28 <= len *)
  step. step. step.
  cir_brf ltac:(rewrite PWR.cir_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x842a4 ld a0,1640(s3): M.fly.len; 0x842a8 bne s1,a0: len = M.fly.len *)
  step. rewrite ld_world.
  step.
  cir_brf ltac:(rewrite <- HLEN, bv_eqb_refl; reflexivity).
  (* 0x842ac mv s0,a2; 0x842b0 auipc a0; 0x842b4 ld a0 (GOT_CELL_K); 0x842b8 ld s4,0(a0) (CELL_K): s4 = the shadow
     base *)
  step. step. step. step.
  (* 0x842bc addi a1,s3,120; 0x842c0 li a2,26; 0x842c4 mv a0,s2; 0x842c8 the call *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The bytes the run reads, as the load step reads them, past a write of [lo, hi) that misses them. *)
Lemma cir_rd_tp : forall (m m' : word -> option byte) lo hi a bs (n : nat),
  munch [(lo, hi)] m m' -> length bs = n -> a + Z.of_nat n <= lo \/ hi <= a ->
  bytes_at rsegs m a bs -> ov_read_bytes rsegs m' (wa a) n = Some bs.
Proof.
  intros m m' lo hi a bs n MU L D H.
  pose proof (bytes_tp m m' lo hi a bs MU ltac:(rewrite L; exact D) H) as H'.
  replace (wa a) with (wa (a + 0)) by (rewrite Z.add_0_r; reflexivity).
  rewrite (bytes_at_read rsegs m' a bs 0 n H' ltac:(lia)) by (rewrite L; change (Z.to_nat 0) with 0%nat; lia).
  change (Z.to_nat 0) with 0%nat. cbn [skipn]. f_equal. apply firstn_all2. lia.
Qed.

(* ---- run 1: the entry to the first call ---- *)

Lemma cir_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fa len fp : Z) (Bw : list byte),
    length Bw = Z.to_nat TW.W_LEN ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    bytes_at rsegs m (TA_M + 96) (TW.sub Bw 96 4) ->
    bytes_at rsegs m (TA_M + 1640) (TW.sub Bw 1640 8) ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) ->
    bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    TA_M + TW.SZ_M <= bv_unsigned sp - 48 ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.rng RNG (TA_M + 96) 4 -> ExecF.rng RNG (TA_M + 1640) 8 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    TW.s32_at Bw 96 <> 0 -> len = TW.u_at Bw 1640 8 -> 28 <= len < 2 ^ 63 ->
    0 <= fa < 2 ^ 63 -> 0 <= fp < 2 ^ 63 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 CIR_RET1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                    (Z_to_bv 64 fp) (Z_to_bv 64 len) (Z_to_bv 64 fa) (Z_to_bv 64 (TA_M + 120)) (Z_to_bv 64 26)
                    a3 a4 a5 a6 a7 (Z_to_bv 64 fa) (Z_to_bv 64 TA_M) (Z_to_bv 64 ASAN_K)
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CIR_BCMP) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (cir_fr s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 len) (Z_to_bv 64 fp) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIR_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo fa len fp Bw LBW ST LO BON BLEN BGC BCK HSEP RFR GON GLEN GGC GCK HON HLEN HL28 HFA HFP.
  unfold TW.W_LEN in LBW.
  eapply ExecF.evtF_cut.
  { eapply cir_pro_F; [exact ST | exact LO | exact RFR]. }
  intros ms0 (m1 & -> & MU & WM & ST1 & FR).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold TA_M, TW.SZ_M, GOT_CELL_K, CELL_K in HSEP.
  eapply ExecF.evtF_mono.
  { eapply cir_body1_F; [| | | | exact GON | exact GLEN | exact GGC | exact GCK | exact HON | exact HLEN | exact HL28
                        | exact HFA | exact HFP].
    - exact (cir_rd_tp m m1 _ _ (TA_M + 96) (TW.sub Bw 96 4) 4 MU
               (TWorldLemmas.length_sub Bw 96 4 ltac:(lia) ltac:(lia)) ltac:(unfold TA_M; lia) BON).
    - exact (cir_rd_tp m m1 _ _ (TA_M + 1640) (TW.sub Bw 1640 8) 8 MU
               (TWorldLemmas.length_sub Bw 1640 8 ltac:(lia) ltac:(lia)) ltac:(unfold TA_M; lia) BLEN).
    - exact (cir_rd_tp m m1 _ _ GOT_CELL_K (le8 (wa CELL_K)) 8 MU (length_le8 _) ltac:(unfold GOT_CELL_K; lia) BGC).
    - exact (cir_rd_tp m m1 _ _ CELL_K (le8 (wa ASAN_K)) 8 MU (length_le8 _) ltac:(unfold CELL_K; lia) BCK). }
  intros ms' ->. exists m1.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1 | exact FR].
Qed.

(* ---- run 2: the first call's return (it answered 0) to the second call ---- *)

Lemma cir_run2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fa len : Z),
    28 <= len < 2 ^ 63 -> 0 <= fa < 2 ^ 63 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 CIR_RET2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 len) (Z_to_bv 64 (fa + 28))
                              (Z_to_bv 64 (TA_M + 148)) (Z_to_bv 64 (len - 28)) a3 a4 a5 a6 a7
                              (Z_to_bv 64 fa) (Z_to_bv 64 TA_M) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 CIR_BCMP) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 len) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 fa) (Z_to_bv 64 TA_M) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIR_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fa len
    HL28 HFA.
  cir_pc. unfold TA_M.
  (* 0x842cc bnez a0: the first call answered 0 *)
  step. cir_brf ltac:(rewrite bv_eqb_refl; reflexivity).
  (* 0x842d0 addi a0,s2,28; 0x842d4 addi a2,s1,-28; 0x842d8 addi a1,s3,148; 0x842dc the call *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* `srli rd,rs,3` of an address below 2^64. *)
Lemma cir_shr3 : forall x, 0 <= x < 2 ^ 64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* ---- run 3: the second call's return (it answered 0) to the `ret` ---- *)

Lemma cir_run3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (cs0 cs1 cs2 cs3 cs4 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fa len fp : Z) (SB Bw : list byte),
    ov_read_bytes rsegs m (wa ((fp + 30) / 8 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (fp + 30)) 2 = Some (TW.sub SB 30 2) ->
    ov_read_bytes rsegs m (wa (TA_M + 108)) 4 = Some (TW.sub Bw 108 4) ->
    ov_read_bytes rsegs m (wa (TA_g_cfg + 32)) 4 = Some (TW.sub Bw 65056 4) ->
    ov_read_bytes rsegs m (wa (TA_M + 112)) 8 = Some (TW.sub Bw 112 8) ->
    ov_read_bytes rsegs m (wa TA_g_now) 8 = Some (TW.sub Bw 65000 8) ->
    ov_read_bytes rsegs m (wa (TA_g_cfg + 28)) 4 = Some (TW.sub Bw 65052 4) ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.rng RNG ((fp + 30) / 8 + ASAN_K) 1 -> ExecF.rng RNG (fp + 30) 2 ->
    ExecF.rng RNG (TA_M + 108) 4 -> ExecF.rng RNG (TA_M + 112) 8 ->
    ExecF.rng RNG (TA_g_cfg + 28) 8 -> ExecF.rng RNG TA_g_now 8 ->
    stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 ->
    rw_cells rsegs m (bv_unsigned sp + -48) (cir_fr cs4 cs3 cs2 cs1 cs0 cra) ->
    0 <= fp -> fp + 32 <= 2 ^ 63 ->
    TW.u_at SB 30 2 = DgnSpec.u32 (TW.u_at Bw 108 4 + 1) ->
    TW.u_at SB 30 2 <= TW.u_at Bw 65056 4 ->
    TSess0.u64 (TW.u_at Bw 65052 4 * 1000) <= TSess0.u64 (TW.u_at Bw 65000 8 - TW.u_at Bw 112 8) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (r10 r11 r12 spx : word),
         ms' = MS (mkR cra spx gp tp t0 t1 t2 cs0 cs1 r10 r11 r12 a3 a4 a5 a6 a7 cs2 cs3 cs4
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs) /\
         bv_unsigned spx = bv_unsigned sp /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 len)
              (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fa) (Z_to_bv 64 TA_M) (Z_to_bv 64 ASAN_K)
              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIR_RET2) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cs0 cs1 cs2 cs3 cs4 cra
    F fc m lo fa len fp SB Bw RSH RRT RFT RMX RSN RNW RTO GFR GSH GRT GFT GSN GCF GNW ST HLO FR HFP0 HFP1
    HRT HMX HTM.
  cir_pc. unfold ASAN_K, wa in *.
  change (TA_M + 108) with 6156748 in *. change (TA_M + 112) with 6156752 in *.
  change (TA_g_cfg + 32) with 6156448 in *. change (TA_g_cfg + 28) with 6156444 in *.
  change TA_g_now with 6156544 in *. unfold TA_M in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. unfold cir_fr in FR.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as HL0.
  (* 0x842e0 bnez a0: the second call answered 0 *)
  step. cir_brf ltac:(rewrite bv_eqb_refl; reflexivity).
  (* 0x842e4 addi a0,s0,30; 0x842e8 srli a1,a0,3; 0x842ec add a1,a1,s4 *)
  step. step. rewrite (cir_shr3 (fp + 30)) by lia.
  step.
  (* 0x842f0 lb a1,0(a1): the shadow byte of fp + 30, 0; 0x842f4 bnez a1 *)
  step. step.
  cir_brf ltac:(vm_compute; reflexivity).
  pose proof (TWorldLemmas.u_at_range Bw 108 4) as R108. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R108.
  pose proof (TWorldLemmas.u_at_range Bw 65056 4) as R65056. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R65056.
  pose proof (TWorldLemmas.u_at_range Bw 65052 4) as R65052. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R65052.
  pose proof (TWorldLemmas.u_at_range Bw 65000 8) as R65000. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R65000.
  pose proof (TWorldLemmas.u_at_range Bw 112 8) as R112. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R112.
  pose proof (TWorldLemmas.u_at_range SB 30 2) as R30. change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16) in R30.
  (* 0x842f8 lw a2,108(s3): M.fly.retries; 0x842fc lhu a1,0(a0): f->retry *)
  step. rewrite lw_world.
  step. rewrite lhu_world.
  (* 0x84300 addiw a2,a2,1; 0x84304 bne a2,a1: M.fly.retries + 1 = f->retry *)
  step. step.
  cir_brf ltac:(unfold TW.s32_at; rewrite (PWR.cir_addiw (TW.u_at Bw 108 4) (TW.u_at SB 30 2))
                  by (first [exact HRT | lia]); reflexivity).
  (* 0x84308 auipc a0; 0x8430c addi a0 (g_cfg); 0x84310 lw a2,32(a0): max_retries; 0x84314 bltu a2,a1 *)
  step. step. step. rewrite lw_world.
  step. cir_brf ltac:(unfold TW.s32_at; apply PWR.cir_ltu_max; lia).
  (* 0x84318 auipc a1; 0x8431c ld a2,112(s3): M.fly.sent; 0x84320 ld a1 (g_now); 0x84324 lwu a0,28(a0):
     ack_timeout_ms *)
  step. step. rewrite ld_world. step. rewrite ld_world. step. rewrite lwu_world.
  (* 0x84328 sub a1,a1,a2; 0x8432c li a2,1000; 0x84330 mul a0,a0,a2; 0x84334 bltu a1,a0 *)
  step. step. step. step.
  cir_brf ltac:(rewrite (unsigned_lit (TW.u_at Bw 65000 8)), (unsigned_lit (TW.u_at Bw 112 8)),
                  (unsigned_lit (TW.u_at Bw 65052 4)) by lia;
                unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; exact HTM).
  (* the epilogue: 0x84338 .. 0x8434c the six loads, 0x84350 addi sp,sp,48, 0x84354 ret *)
  do 8 step.
  apply evtF_done. do 4 eexists. split; [reflexivity|]. split.
  { rewrite ?unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
