(* The evt-level snprintf chain at fuzz_reply.asan, with every Section hypothesis of its four pieces discharged:
     RT_pf_snf.v snprintf_icpt_ok  <- RT_pf_vsn_body.v vsnprintf_icpt_ok_body  <- RT_pf_vsn.v vsnprintf_icpt_ok
       <- RT_gxa_inst.v fr_vsnprintf_x (GXA's musl vsnprintf at A_img_vsn, memset at RT_gxa_calls_mem.v)
       <- RT_pf_vf.v vf_icpt_ok <- RT_gxa_inst.v fr_vfprintf_guarded (GXA's guarded musl vfprintf at A_img, memcpy /
          memset at RT_gxa_calls_mem.v, strnlen at RT_gxa_calls.v).
   snprintf_chain_closed proves RT_pf_stmt.v snprintf_icpt_stmt (the snprintf interceptor at __wrap_snprintf runs to
   vsnprintf_x_post) at set_ready := RT_gxa_calls_mem.set_ready, in a Theorem Labs lane 3899f140f93's form (its facts are asked
   only when 0 <= n), and at vf_ready := vf_ready_icpt fr_vfb, fr_vfb being the guard of GXA's closed vfprintf body.
   This is RT_pf_vf.v:368-395's commented snprintf_chain_ok with the RT_pf_vsn.v step the comment lacks.  The only
   variable left is GXA's store invariant INV (RT_gxa_inst.v:49), which the evt -> SRr bridge chooses.
   The premise icpt_ready carries GXA's pc_guard through fr_vfb.  RT_pf_chain_sat.v is the non-vacuity witness of
   that premise: it proves pc_guard at fr_vfb's predicates for a concrete store and geometry.  At the earlier
   set_ready, which asked sp < 2 ^ 63 at every n, pc_guard holds at no store, and this theorem would be vacuous. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_inst.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vsn_body.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vsn.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vf.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module GM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Module GI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_inst.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Module PN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_snf.
Module PB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vsn_body.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vsn.
Module PF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_vf.

Section Chain.
Variable INV : (word -> option byte) -> Prop.

Definition fr_VFB := GI.fr_vfprintf_guarded GM.copy_ready GM.memcpy_stack_contract_A GM.set_ready
  GM.memset_stack_contract_A GC.strn_ready GC.strnlen_stack_contract_A INV.
(* the guard GXA's closed vfprintf body carries, read off its type *)
Definition fr_vfb : VFC.vf_guard :=
  ltac:(lazymatch type of fr_VFB with @VFC.vfprintf_guarded_stmt _ ?g => exact g end).

Theorem snprintf_chain_closed : PS.snprintf_icpt_stmt GM.set_ready (PS.vf_ready_icpt fr_vfb).
Proof.
  apply (PN.snprintf_icpt_ok GM.set_ready (PS.vf_ready_icpt fr_vfb)).
  apply (PB.vsnprintf_icpt_ok_body GM.set_ready (PS.vf_ready_icpt fr_vfb)).
  apply (PV.vsnprintf_icpt_ok GM.set_ready (PS.vf_ready_icpt fr_vfb)).
  apply (GI.fr_vsnprintf_x GM.set_ready (PS.vf_ready_icpt fr_vfb) GM.memset_stack_contract_Avsn).
  exact (PF.vf_icpt_ok fr_vfb fr_VFB).
Qed.
End Chain.
