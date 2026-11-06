(* DgnBcLoopCut: the two halves of one turn of the msg_next loop of diginet_body_check (fuzz_decode.asan, the loop
   head +0x16c = BC_LOOP of lib/A/Prog/DgnBcCut.v), as STATEMENTS only.
     +0x16c .. +0x174  `mv a0,s5; mv a1,s6; jal diginet_msg_next` and the call, up to its return at +0x178
                       (bl_call_stmt: the state after the call is bl_after);
     +0x178 .. +0x1e4  `beq a0,s10` / `bnez a0` and the sysex test (m.status, m.sysex_len, m.sysex, then the body
                       bytes at m.sysex and m.sysex + 2, each behind a shadow check), to +0x16c (the next turn),
                       +0x1ec (the prefix scan) or, through +0x404 `li a0,-10` and `j +0x298`, the release
                       (bl_test_stmt).
   r = msg_step bb cp st is the step the call makes; bl_after is what the code after the return reads: the walk's
   own journal and the bytes it carries (bc_cur), the loop's registers (bc_regs_loop), a0 = mr_code r, the cursor
   at (mr_pos r, mr_st r), the message bytes of r, and the shadow bytes of c and m. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib DgnTransportCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnBcCut.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of `jal diginet_msg_next` (+0x174), as an offset from the listing's base. *)
Definition BL_RET : Z := AF_diginet_body_check + 0x178.

Section lc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The state at +0x178, after the call of one turn that started with the cursor at (cp, st) and the message bytes
   mj: r = msg_step bb cp st. *)
Definition bl_after (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (regs : bvmap 5 word) (body : Z) (bb : list byte) (pos sp1 F : Z) (cp : nat) (st : Z) (mj : list byte)
    (ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte) (md3 : Model)
    (regs3 : bvmap 5 word) : Prop :=
  bc_cur B MT lyc Sc W memc mdc regs body bb pos sp1 F ly3 S3 W3 mem3 md3 /\
  bc_regs_loop regs regs3 body sp1 F /\
  YK11.getr regs3 10 = w64 (mr_code (msg_step bb cp st)) /\
  garr8 segs (mrestrict (w_H W3) mem3) (F + 32)
    (BMN.trans_mn_cur_bytes body (Z.of_nat (length bb)) (mr_pos (msg_step bb cp st)) (mr_st (msg_step bb cp st))) /\
  garr8 segs (mrestrict (w_H W3) mem3) (F + 96) (BMN.trans_mn_msg_bytes body mj (msg_step bb cp st)) /\
  bc_cm_zero W3 mem3 F.

(* +0x16c .. +0x178: the two argument moves and the call of diginet_msg_next (its contract, a premise), from the
   loop head's facts to bl_after at the return. *)
Definition bl_call_stmt : Prop :=
  bc_laws B MT ->
  (forall fx' : YK11.FPState, @BMN.transport_diginet_msg_next_cg fx' rc B MT (transport_sigma TS_diginet_msg_next)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte)
         (pos sp1 F : Z) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
         (ly2 : alayout) (S2 : astate) (cp : nat) (st : Z) (mj : list byte) (Q : world segs -> config -> Prop),
    bc_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F ->
    bc_cur B MT lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 ->
    bc_regs_loop regs regs2 body sp1 F ->
    (cp <= length bb)%nat -> st_ok st ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 32)
      (BMN.trans_mn_cur_bytes body (Z.of_nat (length bb)) cp st) ->
    length mj = 40%nat ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 96) (map bz mj) ->
    bc_cm_zero W2 mem2 F ->
    (forall (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
            (ly3 : alayout) (S3 : astate),
       bl_after lyc Sc W memc mdc regs body bb pos sp1 F cp st mj ly3 S3 W3 mem3 md3 regs3 ->
       SRr segs W3 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + BL_RET)) mem3 (YK11.seg_rom segs)) md3) Q) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_LOOP)) mem2 (YK11.seg_rom segs)) md2) Q.

(* +0x178 .. : the result test and the sysex test, which write no memory (registers a0, a1, a2 only). A result that
   is not the end and not a refused sysex goes back to the loop head, the end (a0 = 0) to the prefix scan, a refused
   sysex (DgnLib.refused) to the release with a0 = -10. *)
Definition bl_test_stmt : Prop :=
  bc_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte)
         (pos sp1 F : Z) (cp : nat) (st : Z) (mj : list byte)
         (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
         (ly3 : alayout) (S3 : astate) (Q : world segs -> config -> Prop),
    bc_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F ->
    (cp <= length bb)%nat -> st_ok st -> length mj = 40%nat ->
    bl_after lyc Sc W memc mdc regs body bb pos sp1 F cp st mj ly3 S3 W3 mem3 md3 regs3 ->
    (is_end (msg_step bb cp st) = false -> refused bb (msg_step bb cp st) = false ->
       forall (regs4 : bvmap 5 word) mat, bc_regs_loop regs regs4 body sp1 F ->
       SRr segs W3 (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + BC_LOOP)) mem3 (YK11.seg_rom segs))
         (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
    (is_end (msg_step bb cp st) = true ->
       forall (regs4 : bvmap 5 word) mat, bc_regs_scan regs regs4 body sp1 F ->
       SRr segs W3 (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + BC_SCAN)) mem3 (YK11.seg_rom segs))
         (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
    (refused bb (msg_step bb cp st) = true ->
       forall (regs4 : bvmap 5 word) mat, bc_regs_rel regs regs4 sp1 F -> YK11.getr regs4 10 = w64 (-10) ->
       SRr segs W3 (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + BC_REL)) mem3 (YK11.seg_rom segs))
         (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
    SRr segs W3 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + BL_RET)) mem3 (YK11.seg_rom segs)) md3) Q.
End lc.
