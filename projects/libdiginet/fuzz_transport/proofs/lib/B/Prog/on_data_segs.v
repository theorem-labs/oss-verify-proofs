(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths and module names changed; 291 of its 367 lines of code are new or changed and 367 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_data_seg_cut.v, with its module paths and module names changed; 23 of its 60 lines of code are new or changed and 330 lines of the source are left out. *)
(* on_data_segs: the image-B walk of on_data from its nine pieces. od_holds_of turns the piece Props of
   lib/B/Prog/on_data_seg_cut.v into lib/B/Prog/on_data_cg.v transport_on_data_cg_holds_stmt: od_top_of composes the
   pieces into od_top_at, the contract at TB_on_data with its premises grouped as od_laws (the record facts, with gx_ok
   and gx_noerrno of G from DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno), od_callees, od_pre and
   trans_tf_off_g; od_holds_of_top regroups them as the statement states them. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_frame_is_keepalive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_seg_cut.

Section segs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

(* The statement from the contract at the entry, its premises regrouped. *)
Lemma od_holds_of_top : @od_top_at fx rc B MT -> @transport_on_data_cg_holds_stmt fx rc B MT.
Proof.
intros TOP Hsm Hcl Hodc Hgu Hgne Hrou Hrne HAR Hml Hmfl Hsmp Hasf Hffl CSM CSC CKA CMS CNT.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  HJ Hret Hra Hgp Htp Ha0 Ha1 Ha2 Hal Hlo Hhi Hnow Hdf Htw Hgf Hm Htf Htfg Hrom Hap Hi1 Hi4 Hi3 Hcnt Hev.
refine (TOP _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' _ Htfg).
- exact (conj Hsm (conj Hcl (conj Hodc (conj Hgu (conj Hgne (conj Hrou (conj Hrne (conj HAR (conj Hml (conj Hmfl (conj
    Hsmp (conj Hasf (conj Hffl (conj (G_HARNESS_gx_ok B Hgu) (G_HARNESS_gx_noerrno B Hgne))))))))))))))).
- exact (conj CSM (conj CSC (conj CKA (conj CMS CNT)))).
- exact (conj HJ (conj Hret (conj Hra (conj Hgp (conj Htp (conj Ha0 (conj Ha1 (conj Ha2 (conj Hal (conj Hlo (conj Hhi
    (conj Hnow (conj Hdf (conj Htw (conj Hgf (conj Hm (conj Htf (conj Hrom (conj Hap (conj Hi1 (conj Hi4 (conj Hi3
    (conj Hcnt Hev))))))))))))))))))))))).
Qed.

(* The statement from the nine pieces. *)
Lemma od_holds_of :
  @od_head_stmt fx rc B MT -> @od_sc_stmt fx rc B MT -> @od_acks_stmt fx rc B MT -> @od_dup_stmt fx rc B MT ->
  @od_set_stmt fx rc B MT -> @od_ka_stmt fx rc B MT -> @od_ntc_stmt fx rc B MT -> @od_ncall_stmt fx rc B MT ->
  @od_rel_stmt fx rc B MT -> @transport_on_data_cg_holds_stmt fx rc B MT.
Proof.
intros HEAD SC ACKS DUP SET KA NTC NC REL.
exact (od_holds_of_top (@od_top_of fx rc B MT HEAD SC ACKS DUP SET KA NTC NC REL)).
Qed.

End segs.
