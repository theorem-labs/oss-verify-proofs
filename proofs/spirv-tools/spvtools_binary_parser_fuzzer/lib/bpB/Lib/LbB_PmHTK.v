From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HTK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma sr_tleaf : forall {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
      (Wf : X -> list (Z * Z)) (Qf : X -> mem -> word -> word -> mem -> Prop),
    tleaf entry STK PRE Wf Qf ->
    forall (x : X) (s : as_St H) (msF : machine_state) (mo : Model)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - STK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m ->
    PRE x m (bv_unsigned sp) a0 a1 a2 a3 ->
    (forall msF1 mo1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m1 (seg_rom asegs) ->
       munch ((bv_unsigned sp - STK, bv_unsigned sp) :: Wf x) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       stk asegs m1 lo (bv_unsigned sp) -> ACONST m1 ->
       Qf x m a0' a1' m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros X entry STK PRE Wf Qf HL x s msF mo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m lo Q KR VIS ST LO1 LO2 SPA SPH MI AC HP K.
    eapply (ahh_evt_then H HH _ Q s msF _ mo KR VIS
              (HL x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                  ST LO1 LO2 SPA SPH MI AC HP)).
    intros msF1 mo1 KR1 MP1 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                             E1 & MU & WM & MI1 & ST1 & AC1 & HQ).
    exact (K msF1 mo1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 KR1 MP1 E1 MU WM MI1 ST1 AC1 HQ).
  Qed.

  Lemma sr_msteps : forall (s : as_St H) (msF : machine_state) (mo : Model) (R : bvmap 5 word) (F : bvmap 5 word) (pc : word)
      (fc : bv 32) (m : mem) (R1 : bvmap 5 word) (pc1 : word) (M1 : mem) (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m (seg_rom asegs) -> rfull R ->
    CatSim.msteps asegs (MS R F pc fc None m (seg_rom asegs)) (MS R1 F pc1 fc None M1 (seg_rom asegs)) ->
    (forall msF1 mo1, as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F pc1 fc None M1 (seg_rom asegs) -> rfull R1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s msF mo R F pc fc m R1 pc1 M1 Q KR VIS RF Hms K.
    pose proof (msteps_full asegs _ _ Hms RF) as RF1. cbn [ms_regs] in RF1.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    rewrite <- (rfull_eq R1 RF1) in VIS1.
    exact (K msF1 mo1 KR1 MP1 VIS1 RF1).
  Qed.
End HTK.
