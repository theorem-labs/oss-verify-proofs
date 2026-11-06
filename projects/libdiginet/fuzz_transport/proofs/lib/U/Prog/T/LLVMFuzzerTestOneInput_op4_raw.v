(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the raw arm 0x14488 .. the latch 0x14574
   (fuzz_transport.c:1078-1083: w = fuzz_u16(in), c.len = fuzz_take(in, w % (SPEC_CMD_MAX + 1), &p),
   memcpy(c.bytes, p, c.len), diginet_session_submit(&g_s, &c), check_refusal_submit(&c, rc, before), settle(0)). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_submit_c check_refusal_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs.
Import ListNotations.
Open Scope Z_scope.

(* 0x144d0, the take done: a2 = n = min(w % 25, in.n), s3 the cursor, a0 its n, s0 = (int)before *)
Definition op4_rt (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (c4 : fuzz_in) (nn before : Z) (B1 : list byte) (display key : Z)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s5 s6 s7 t3 t4 t5 t6 : word) (m : word -> option byte)
         (j10 jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 (bv_swrap 32 before)) (Z_to_bv 64 1)
                 (Z_to_bv 64 (fi_n c4)) a1 (Z_to_bv 64 nn) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c4)) (Z_to_bv 64 7) s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x144d0) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor D c4 /\ 0 <= nn <= 24 /\ nn <= fi_n c4 /\
    0 <= before < 2 ^ 32 /\ 0 <= display <= 1 /\ 0 <= key < 2 ^ 32 /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B1 m j10 jio (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi).

(* 0x14488-0x144cc: w = lo8 | hi8 << 8, w % 25, n = min(w % 25, in.n) *)
Lemma op4_raw_head : forall data D regs0 m0 Sp lo ops c4 lo8 hi8 before B1 display key F fc ms
    (Q : machine_state -> Prop),
  op4_r data D regs0 m0 Sp lo ops c4 lo8 hi8 before B1 display key F fc ms ->
  (forall ms', op4_rt data D regs0 m0 Sp lo ops c4
     (if (lo8 + 256 * hi8) mod 25 <? fi_n c4 then (lo8 + 256 * hi8) mod 25 else fi_n c4)
     before B1 display key F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops c4 lo8 hi8 before B1 display key F fc ms Q H HK.
  destruct H as (ra & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s5 & s6 & s7 & t3 & t4 & t5 & t6 & m & j10 & jio & jhi &
                 -> & HOPS & HC & HLO8 & HHI8 & RQ & HDSP & HKEY & LJ & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold llvm_cursor in HC.
  unfold LH_K, LH_FRAME in *.
  assert (HW : 0 <= lo8 + 256 * hi8 < 65536) by lia.
  assert (HM25 : 0 <= (lo8 + 256 * hi8) mod 25 < 25) by (apply Z.mod_pos_bound; lia).
  destruct (llvm_frame_split regs0 m Sp j10 jio (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi) HRW)
    as (F1 & F2 & F3 & F4 & F5 & F6).
  unfold llvm_saved in F6.
  (* 0x14488 slli a2, 8; 0x1448c or a1, a2, a1; 0x14490-0x144bc: w % 25; 0x144c0 ld a2, 0x28(sp);
     0x144c4 and a2, a1, a2 *)
  do 16 zstep.
  rewrite (op4_mod25 (Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8))
    by (rewrite (op4_w16 lo8 hi8 HLO8 HHI8); lia).
  rewrite (op4_w16 lo8 hi8 HLO8 HHI8).
  rewrite (Z.mod_small ((lo8 + 256 * hi8) mod 25) 18446744073709551616) by lia.
  rewrite (op4_land16 ((lo8 + 256 * hi8) mod 25)) by lia.
  (* 0x144c8 bltu a2, a0 *)
  zstep.
  destruct (Z.ltb_spec ((lo8 + 256 * hi8) mod 25) (fi_n c4)) as [LT|LT].
  - brv true.
    replace (if (lo8 + 256 * hi8) mod 25 <? fi_n c4 then (lo8 + 256 * hi8) mod 25 else fi_n c4)
      with ((lo8 + 256 * hi8) mod 25) in HK by (symmetry; apply Z.ltb_lt in LT; rewrite LT; reflexivity).
    apply HK. unfold op4_rt.
    do 17 eexists. exists m, j10, jio, jhi.
    split; [reflexivity|].
    split; [exact HOPS|]. split; [unfold llvm_cursor; lia|]. split; [lia|]. split; [lia|].
    split; [exact RQ|]. split; [exact HDSP|]. split; [exact HKEY|]. split; [exact LJ|]. exact HM0.
  - brv false. zstep.
    replace (if (lo8 + 256 * hi8) mod 25 <? fi_n c4 then (lo8 + 256 * hi8) mod 25 else fi_n c4)
      with (fi_n c4) in HK by (symmetry; apply Z.ltb_ge in LT; rewrite LT; reflexivity).
    apply HK. unfold op4_rt.
    do 17 eexists. exists m, j10, jio, jhi.
    split; [reflexivity|].
    split; [exact HOPS|]. split; [unfold llvm_cursor; lia|]. split; [lia|]. split; [lia|].
    split; [exact RQ|]. split; [exact HDSP|]. split; [exact HKEY|]. split; [exact LJ|]. exact HM0.
Qed.
