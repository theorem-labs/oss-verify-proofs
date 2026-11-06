(* fuzz_send on image A: the walk lib/A/Prog/fuzz_send.v `fuzz_send_aproof` with its callee and errno hypotheses
   discharged on the image: ___errno_location by lib/A/Rt/RtErrnoLocClosed.v `link_errno_location_closed`
   (0x90a7c), checked_memcpy by lib/A/AE2q.v `asan_memcpy_realizes` (0x52d78), ERRF by LinkWalkErrnoInst.v
   `link_errno_not_static` from the image's asyms record (lib/A/AF0m.v PcapSyms). What stays is the image instance
   itself: its program tables (PI with its segments the image's), the allocator laws, PALib and LinkVals (as
   fuzz_socket.v `fuzz_socket_aproof_img`).
   Proves fuzz_send (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk LinkWalkErrnoInst fuzz_send_c fuzz_send.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AE2q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtErrnoLocClosed.
Open Scope Z_scope.

Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem fuzz_send_aproof_img : forall B, AR_laws pa_segs B -> PALib B -> LinkVals -> AF0m.PcapSyms B ->
  pa_segs = AB1v.tfibsegs -> forall rlo rhi, fuzz_send_acontract SK pa_segs rlo rhi B.
Proof.
intros B LAWS TL LV TS Hsegs.
apply (fuzz_send_aproof SK B LAWS TL LV (link_errno_not_static B TS)).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtErrnoLocClosed.link_errno_location_closed B).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. rewrite Hsegs in LAWS.
  exact (AE2q.asan_memcpy_realizes B LAWS TS).
Qed.
End img.

Print Assumptions fuzz_send_aproof_img.
