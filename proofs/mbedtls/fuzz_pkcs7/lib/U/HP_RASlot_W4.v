(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_entry HP_RF_malloc_small HP_RF_ntf_A HP_RF_ntf_C HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RASlot_W2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W4 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RP_1.T1.rt1_regs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_active"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RP_1.rt1_regs"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.put_meta"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W5.clr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_prev"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_next"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_prev"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W6.full_skip"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : rceil <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L12937216788.55L12937216788.56L18241568998.52L22117270200.58L29784364028.53L34217602743.60L36511751956.55L36511751956.56L39440973590.56L39442877973.54L43059543694.50L59308696166.60L63126885979.54L7441083620.53 00000X01[01_02102202H03004304704;04E04R04V04]S3hRP2lo3CLO3RCB2ra2sp2LO2HB5Ha_st5Hl_stS3hRP2lo3CLO3RCB2sp2s02LO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2spS3hRP2lo3CLO2sp2LOSS3hRP2st1g3RCB4Gpos2GCS3hRP2lo3CLO3RCB2ra2sp2LO2HB5Ha_st5Hl_stS3hRP2lo3CLO3RCB2sp2s02LO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2scS2scS2lo2sp2LOS2st1g1K4GposS2scS2sc2SC". (* [comment removed for export] *)
#[using="MR SC CLO AMS"] Lemma ras_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  a0 = Z_to_bv 64 sc ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' : word) m' junk,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz rp_canary) a1' (pw st (active st sc)) a3 a4 a5 a6 a7
                   a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (match active st sc with None => 0x40ab8 | Some _ => 0x4093c end)) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk rsegs m' lo (bv_unsigned sp + -144)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep st m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof. rceilb.
  intros until fc. intros HA ST LO MI. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR as (_ & _ & (_ & _ & _ & G4 & G5) & _). unfold wz in G4.
  rceilb; unfold ralloc_slot_entry, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step.
  rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; rceilb; lia]) end.
  pose proof (rmrep_active_read st _ sc (wa (512968 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
  step. clear RDA.
  (* [comment removed for export] *)
  step.
  replace (512960 + sc * 8 + 88) with (512968 + 80 + 8 * sc) by lia.
  replace (512960 + sc * 8) with (512960 + 8 * sc) by lia.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K.
  - destruct (active st sc) as [g|] eqn:HA.
    { exfalso. dpose (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _).
      unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
    apply evt_done. deexists 3. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
  - destruct (active st sc) as [g|] eqn:HA.
    2:{ exfalso. apply K. reflexivity. }
    apply evt_done. deexists 3. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ENTRY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

(* [comment removed for export] *)
Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "(0.O1:.O19.O18.O17.O16.O15.O14.(1.&40.Vsc,)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.(1.&40.$2.)(1.&40.(3.(3.$4.+50.)(5.+8.Vsc,)))(1.&40.$6.)(1.&40.(3.$6.(5.+8.Vsc,)))O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L16077671799.48L36032276251.4700000>00MS2st1g1G2mr2RAS2st1g1G2mr3AVR". (* [comment removed for export] *)
#[using="hRP MR MSL AVR"] Lemma rt1_fin_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)P,(9.(:.$;.(<.Vmr,)=))P,(=.$>.Vm,)(?.$>.Lms',$10.(:.$10.R1.(11.(12.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(1.&40.VG,)(13.(14.(<.Vmr,)))(1.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(1.&40.+40:78.)R4.(15.(7.&40.))Vm,(16.$>.)))(11.(12.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.(1.&40.VG,)R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(1.&40.+4093<.)R3.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros AVNZ MI. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
  pose proof (sxv_range (m_avail mr)) as RA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
  { exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
  step. step.
  apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53519272362.47000008S2st1g1G". (* [comment removed for export] *)
#[using="hRP MR MSL"] Lemma rt1_deq_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)P,(:.$;.(<.Vmr,)=)P,(:.$;.(17.Vmr,)=)P,(=.$>.Vm,)(?.$>.Lms',$10.(:.$10.R1.(11.(12.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(18.Vst,(19.Vmr,))(13.=)(1.&40.VG,)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(1.&40.+40960.)R5.(15.(7.&40.))Vm,(16.$>.)))(11.(12.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(1.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(1.&40.+4093<.)R4.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. unfold pw, wz. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11803485471.52L16077671799.51L29759295589.50L36032275870.50L49702840724.52L52163693840.52L53518995108.5000000?00M00[00j01<01N01VS2st1g2sc1G3LENS2st1g1G2mr2RFS2st1g2sc1G2SCS2st1g1G2mr3FRRS2st1g2sc1G2SC3LENS2st1g2sc1G2SC3LENS2st1g1G". (* [comment removed for export] *)
#[using="MR MSL SC FRR"] Lemma rt1_next_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)P,(:.$;.(<.Vmr,)=)P,(9.(:.$;.(17.Vmr,)=))P,(=.$>.Vm,)(?.$>.Lms',$10.(1:.P,(7.&40.)(1;.(7.&8.))Lm',P,(7.&40.)(1;.(7.&8.))(1<.(:.$10.R2.(11.(12.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(18.Vst,(19.Vmr,))(13.(14.(17.Vmr,)))(1.&40.VG,)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(1.&40.+409:0.)R6.(15.(7.&40.))R1.(16.$>.)))(1<.(1=.(1>.(1?.$;.$;.)(20.$;.$;.(3.(3.$4.+50.)(5.+8.Vsc,))(3.(3.(3.$4.+50.)(5.+8.Vsc,))+8.))(21.(1?.$;.$;.)))Vm,R1.)(1<.(22.$>.Vm,R1.)(1<.(=.$>.R1.)(23.VhRP,(24.Vsc,(19.Vmr,)Vst,)R1.))))))(11.(12.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(1.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(1.&40.+4093<.)R4.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
  pose proof (sxv_range (m_freed mr)) as RF.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. step.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
  { exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  dpose MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (512968 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End T1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L13747413779.48L25069450385.50L29759295589.48L49702840724.50L52163693840.5000000E00T00b01401FS3hRP1G3RCB4Gpos2GC1KS2st1g2sc1G3LENS2st1g2sc1G2SCS2st1g2sc1G2SC3LENS2st1g2sc1G2SC3LEN". (* [comment removed for export] *)
#[using="MR MSL SC"] Lemma rdeq_self_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa1,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)P,(:.$25.(19.Vmr,)(26.$27.Vg,))P,(=.$>.Vm,)(?.$>.Lms',$10.(1:.P,(7.&40.)(1;.(7.&8.))Lm',P,(7.&40.)(1;.(7.&8.))(1<.(:.$10.R2.(11.(28.Vsc,R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(13.=)R16.(1.&40.VG,)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(1.&40.+40:;8.)R5.(15.(7.&40.))R1.(16.$>.)))(1<.(1=.(1>.(1?.$;.$;.)(20.$;.$;.(3.(3.$4.+50.)(5.+8.Vsc,))(3.(3.(3.$4.+50.)(5.+8.Vsc,))+8.))(1>.(1?.$;.$;.)(20.$;.$;.VG,(3.VG,+28.))(21.(1?.$;.$;.))))Vm,R1.)(1<.(22.$>.Vm,R1.)(1<.(=.$>.R1.)(23.VhRP,(29.Vg,(2:.Vmr,)(24.Vsc,(15.$27.)Vst,))R1.))))))(11.(28.Vsc,R1<.R1;.R1:.R19.R18.R17.R16.R15.(18.Vst,(19.Vmr,))R14.(1.&40.VG,)R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(1.&40.+40960.)R3.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step.
  (* [comment removed for export] *)
  dpose MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (512968 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
  set (st1 := set_active sc None st) in MR1.
  assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).
  (* [comment removed for export] *)
  rmeta_open G MUg WMg.
  rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
  st1. st1.
  rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read _ _ sc (wa (512968 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L13747413779.66L13747413779.73L29759295589.73L44440941251.66L44440941251.78L49702840724.75L52163693840.75L52564885613.75L59314923118.7800000C00X00f01=01T01f02802M02_S3hRP1G3RCB4Gpos2GCS1G1K3hRP3RCB4Gpos2GCS2st1g2sc1G2SCS3hRP2st3RCB2nx4Npos2NCS3hRP2st3RCB2nx4Npos2NCS2st1g2sc1G2SC3LENS2st1g2sc1G2SC3LENS2st1g2sc1G2nx2pv3LENS2st1g1G2nx4Npos1K". (* [comment removed for export] *)
#[using="MR MSL SC HA"] Lemma rdeq_other_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa1,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)Pnx,$27.Ppv,$27.P,(:.$25.(19.Vmr,)(26.$27.R2.))P,(:.$25.(2;.Vmr,)(26.$27.R2.))P,(9.(:.$27.R4.Vg,))P,(9.(:.$27.R4.Vg,))P,(2<.Vst,R6.)P,(2<.Vst,R6.)P,(=.$>.Vm,)Zst1,$2=.(29.R8.(2>.(26.$27.R9.)(2?.Vst,R8.))Vst,)Zst2,$2=.(29.R:.(30.(26.$27.R9.)(2?.R1.R:.))R1.)Zst3,$2=.(24.Vsc,(26.$27.R;.)R1.)Zst4,$2=.(29.Vg,(2:.Vmr,)R1.)(?.$>.Lms',$10.(1:.(7.&40.)La1',(7.&40.)(1:.P,(7.&40.)(1;.(7.&8.))Lm',P,(7.&40.)(1;.(7.&8.))(1<.(:.$10.R3.(11.(28.Vsc,R2:.R29.R28.R27.R26.R25.R24.R23.(1.&40.(31.Vst,R10.))R2.(1.&40.VG,)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(1.&40.+409:0.)R11.(15.(7.&40.))R1.(16.$>.)))(1<.(1=.(1>.(1?.$;.$;.)(20.$;.$;.(3.(3.$4.+50.)(5.+8.Vsc,))(3.(3.(3.$4.+50.)(5.+8.Vsc,))+8.))(1>.(1?.$;.$;.)(20.$;.$;.VG,(3.VG,+28.))(1>.(1?.$;.$;.)(20.$;.$;.(31.Vst,R?.)(3.(31.Vst,R?.)+28.))(1>.(1?.$;.$;.)(20.$;.$;.(31.Vst,R10.)(3.(31.Vst,R10.)+28.))(21.(1?.$;.$;.))))))Vm,R1.)(1<.(22.$>.Vm,R1.)(1<.(=.$>.R1.)(23.VhRP,R4.R1.)))))))(11.(28.Vsc,R27.R26.R25.R24.R23.R22.R21.R20.(18.Vst,(19.Vmr,))R1?.(1.&40.VG,)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(1.&40.+40960.)R>.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _).
  dpose (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _).
  assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  step. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st pv) MUp WMp.
  rmchunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  (* [comment removed for export] *)
  rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. step. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st nx) MUn WMn.
  rmchunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st2 _ sc (wa (512968 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
  unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. clear CH. step.
  (* [comment removed for export] *)
  dpose MR2 as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (wa (512968 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
  fold st3 in MR3.
  assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).
  (* [comment removed for export] *)
  rmeta_open G MUg WMg.
  rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
  replace (get_meta_rec st3 g) with mr in CH.
  2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1.
  rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read _ _ sc (wa (512968 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
  change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  apply evt_done. deexists 2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L16075584200.57L28223148753.56L34806984771.56L36032274711.55L36034748437.56L36105990701.55L41363641544.57L59314955108.58L59505877513.51L61382946448.57L9206343098.57 00000@00Q00X00i01:01K01\01o02?02P02`S2st1g1G2mr1f2RMS2st1g1G2mr1f3MWRS2mr2FBS2st1g1G2mr1f3MWRS2st1g1G2mr1f3MWRS2st1g1G2mr1f3FRRS2st1g1G2mr1f3MURS2st1g1G2mr1f3NSK1KS2st1g1G2mr1f2LIS2st1g1G2mr1f3FRRS2st1g1G2mr1f2RF". (* [comment removed for export] *)
#[using="hRP MR MSL FRR MW"] Lemma rm_act_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)P,(:.$32.(33.Vst,Vg,)$34.)P,(=.$>.Vm,)(?.$>.Lms',$10.(1:.(7.&40.)La1',(7.&40.)(1:.(7.&40.)La2',(7.&40.)(:.$10.R3.(11.(28.Vsc,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(1.&40.VG,)R2.R1.(13.(14.Vf,))(1.&40.+2.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(1.&40.+409<<.)R6.(15.(7.&40.))Vm,(16.$>.)))))(11.(28.Vsc,R1=.R1<.R1;.R1:.R19.R18.R17.R16.(1.&40.VG,)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(1.&40.+409:0.)R3.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros NSK MI. unfold rt1_regs.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *) apply evt_done. deexists 2. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  { apply evt_done. deexists 2. reflexivity. }
  exfalso. unfold full_skip in NSK. fold mr f in NSK.
  assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
  rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L11803485471.67L16075584200.66L16075706354.68L28225393619.65L29759295589.65L34806984771.66L36032274711.65L36105990701.65L49702840724.67L52163693840.67L59314923118.66L59505877513.60L9206343098.66 00000D00T00h01901L01S01d02502L02c03:03J03ZS2st1g2sc1G2mr1f3LENS2st1g1G2mr1f2RMS2st1g1G2mr1f2mn3FNRS2st1g1G2mr1f3MWRS2st1g2sc1G2mr1f2SCS2mr2FBS2st1g1G2mr1f3MWRS2st1g1G2mr1f3FRRS2st1g2sc1G2mr1f2SC3LENS2st1g2sc1G2mr1f2SC3LENS2st1g1G2mr1f4FBNZ2FB1KS2st1g1G2mr1f2LIS2st1g1G2mr1f2RF". (* [comment removed for export] *)
#[using="f MR MSL SC FRR MW"] Lemma rm_skip_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W4 ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps1,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)Pmn,$27.P,(:.$32.(33.Vst,Vg,)$35.)P,(:.$25.(19.Vmr,)(26.$27.R2.))P,(2<.Vst,R3.)P,(1<.(36.=(17.(2?.Vst,R4.)))(37.(17.(2?.Vst,R4.))(38.+2.+20.)))P,(=.$>.Vm,)(?.$>.Lms',$10.(1:.(7.&40.)La1',(7.&40.)(1:.(7.&40.)La2',(7.&40.)(1:.P,(7.&40.)(1;.(7.&8.))Lm',P,(7.&40.)(1;.(7.&8.))(1<.(:.$10.R4.(11.(28.Vsc,R25.R24.R23.R22.R21.R20.R1?.R1>.(1.&40.(31.Vst,R:.))R3.R2.(13.(14.(17.(2?.Vst,R:.))))(1.&40.+2.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(1.&40.+409<<.)R;.(15.(7.&40.))R1.(16.$>.)))(1<.(1=.(1>.(1?.$;.$;.)(20.$;.$;.(3.(3.$4.+50.)(5.+8.Vsc,))(3.(3.(3.$4.+50.)(5.+8.Vsc,))+8.))(21.(1?.$;.$;.)))Vm,R1.)(1<.(22.$>.Vm,R1.)(1<.(=.$>.R1.)(23.VhRP,(24.Vsc,(26.$27.R:.)Vst,)R1.))))))))(11.(28.Vsc,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(1.&40.VG,)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R8.(1.&40.+409:0.)R7.(15.(7.&40.))Vm,(16.$>.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  dpose (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
  apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.
  (* [comment removed for export] *)
  step. clear CH.
  (* [comment removed for export] *)
  dpose MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (512968 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
  rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
  step. rewrite sx32_wz_sxv by lia.
  apply evt_done. deexists 3. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End M.

End RP_1.
