(* notice_cgW: Theorem transport_notice_cg_holds : the statement transport_notice_cg_holds_stmt of
   lib/B/Prog/notice_cg.v, the image-B G-form caller-journal walk of notice (fuzz_transport.asan-ubsan 41113a03c82f,
   entry 0x8341c = TImgB.v ti_notice timg_B, 652 bytes, frame 16).

   The walk is split into segments (lib/B/Prog/notice_seg_*.v), every one over the caller's G journal
   (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []):
   - notice_seg_base.v / notice_seg_lib.v: the symbolic states, regions and atoms, the model's paths of notice_m, the
     call's facts (nt_ctx), the entry state, the post at a return (nt_close), the value and world lemmas, and the
     statement of one arm (nt_path: the walk from `jr a0` at 0x83474 with a0 the arm's code pointer);
   - notice_seg_disp.v: the entry, the UBSan checks of p (decided by p's facts), the kind load, the switch and the
     default arm (nt_holds: the six nt_path give the statement);
   - notice_seg_desk.v, _state.v, _data.v, _acked.v, _lost.v, _foreign.v: the six arms. Each UBSan trap branch
     (0x83610) is refuted by notice_m (an int increment at INT_MAX, GOT.n < 0 on the record path) or by p's facts;
     each callee is applied through its statement: check_state_desk / check_state_data (donor form,
     TransportGCg.v gx_call_cg), check_inflight_acked / check_inflight_lost / check_state_online (leaves,
     TransportGCg.v gx_call_leaf and DgnTransportBLeafb.v decode_leafb_journal). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  notice_seg_desk notice_seg_state notice_seg_data notice_seg_acked notice_seg_lost notice_seg_foreign.

Section notice_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem transport_notice_cg_holds : @transport_notice_cg_holds_stmt fx rc B MT.
Proof.
  exact (nt_holds B MT (nt_desk B MT) (nt_state B MT) (nt_data B MT) (nt_acked B MT) (nt_lost B MT)
    (nt_foreign B MT)).
Qed.
End notice_w.

Print Assumptions transport_notice_cg_holds.
