(* F1 priming row R3 (re-hide at a secondary recycle): Quarantine::DoRecycle (0x33cf8) at plugin-hostd/fuzz_reply's
   asan image meets [DMwalkIFRh.dorecycle_spec_rh] (YG0dH.amreal' at YGcfRehidePost.RZ_cf, leaf
   DMwalkIFRh.dr_leaf_rh) over the OPAQUE cut relation ARXr, owned set AOX and recycle invariant DRq, with fuel
   [length P] and the count-0 batch arm, under the six hypotheses of [DMwalkIFRh.dorecycle_ok_rh_t]: those of
   DMwalkIF.dorecycle_ok_t, with Recycle's contract DIfaceRh.de_rchunk_m_rh_t in place of MnRecycle.de_rchunk_m_t
   (CacheDealloc's stays MnRecycle.de_cdealloc_m_t).  Made from lib/A/DMrecF.v.
   The walk: DMrecMRh.dorecycle_arm_rh, with its item step DMrecT5Rh.T_R_rh and its count-0 step DMrecT6Rh.T_O0_rh.
   A new file, so that DMrecF.v stays byte-unchanged.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle
   (frame-generic, count-0 arm, fuel length P, at the re-hide twins). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane): the image-B (asan-ubsan) twin of lib/A/DMrecFRh.v at a working branch 2612386275a5, relocated by a Theorem Labs lane's alreloc a5c53bb2bed4ad03 (every moved numeral a Quarantine::DoRecycle pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIFRh DMrecMRh DMrecT5Rh DMrecT6Rh.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem dorecycle_ok_rh : forall B ARXr AOX DRq RMAXD, DMwalkIFRh.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD.
Proof.
intros B ARXr AOX DRq RMAXD TB HRM FR RV RCH CDH inst ly X P W regs mem md PRE.
pose proof PRE as (_ & Hinst & _). subst inst.
exact (DMrecMRh.dorecycle_arm_rh B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE
  (DMrecT5Rh.T_R_rh B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE)
  (DMrecT6Rh.T_O0_rh B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE) RCH CDH).
Qed.
End c.
Print Assumptions dorecycle_ok_rh.
