(* notice_cgW: Theorem transport_notice_cg_holds : the statement transport_notice_cg_holds_stmt of
   lib/A/Prog/notice_cg.v, the image-A walk (G form: ajournal_gx G_HARNESS 0 []) of notice (fuzz_transport.asan,
   entry 0x83578 = TI.ti_notice timg_A, 600 bytes, a 16-byte frame).

   The walk is split into segments, all symbolic runs of lib/A/Prog/PaShadow.v over the G journal
   (TransportGRunA.v paj_run_x):
   - notice_seg_base.v: the call's facts as a record (nt_ctx), the valuation (registers, the shadow base, the notice's
     four ints, the five GOT fields, the record's address), the entry state with the shadow entry of the notice's 72
     bytes, the model's paths of notice_m (nt_m_desk .. nt_m_foreign), the post at a `ret` (nt_close);
   - notice_seg_lib.v: the region and fact changes between runs, the kept-memory bookkeeping (nt_KA over the walk's
     window and notice_wr), the arm statement nt_path;
   - notice_seg_disp.v: the prologue, the kind load, `bltu 5, kind - 1` (a kind outside 1 .. 6 returns with the world
     unchanged), the jump table at 0x20fcc read as TRANS_RO_RD bytes, and `jr a0` into each arm (nt_holds);
   - one file per arm: notice_seg_desk.v (GOT.desk++, tail jump to check_state_desk through gx_call_cg),
     notice_seg_state.v (+ notice_seg_state_lib.v: the record GOT.t[GOT.n] when GOT.n <= 15, GOT.n++, the tail jump to
     check_state_online when n->state = S_ONLINE), notice_seg_data.v (call of check_state_data through gx_call_cg,
     GOT.ndata++), notice_seg_acked.v (GOT.acked++, tail jump to check_inflight_acked, a leaf),
     notice_seg_lost.v (call of check_inflight_lost, a leaf, then M.fly.on = 0), notice_seg_foreign.v (GOT.foreign++).
   Each arm closes at notice's return (or at the callee's return to notice's caller, for a tail jump) with
   transport_notice_post: the world relation at notice_m's Bw', the bytes outside notice_wr and the window kept. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_lib notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  notice_seg_desk notice_seg_state notice_seg_data notice_seg_acked notice_seg_lost notice_seg_foreign.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.

Section notice_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem transport_notice_cg_holds : @transport_notice_cg_holds_stmt fx rc B MT.
Proof.
  exact (nt_holds B MT (notice_seg_desk.nt_path_desk B MT) (notice_seg_state.nt_path_state B MT)
    (notice_seg_data.nt_path_data B MT) (notice_seg_acked.nt_path_acked B MT) (notice_seg_lost.nt_path_lost B MT)
    (notice_seg_foreign.nt_path_foreign B MT)).
Qed.
End notice_w.

Print Assumptions transport_notice_cg_holds.
