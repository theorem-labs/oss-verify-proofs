(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ, a section flag at the first start-up step, whose segments run on the states B/StartRegenS.v computes per value of the flag, with the run and check lemmas of B/StartRegen.v; the reserved ledger is the image's entries then the vDSO/vvar pair, and each fixed mmap region of the first step ends below the pair; the launch model's channel reader as a premise, LPS 08b1429). *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia Logic.FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartStates n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.

(* [comment removed for export] *)
Module Start1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "true"; "option"; "Some"; "pair"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "sym_runA"; "mkAX"; "axst"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "SLit"; "rw"; "sprop"; "rm"; "SVar"; "reg_sv"; "SAlu"; "SPUle"; "sstate"; "agree_below"; "eval"; "sprop_below"; "ss_next"; "sv_below"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "leaf"; "RsSymJump"; "mkLeaf"; "sym_run"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "vm_limit"; "vm_noaccess"; "vm_reserved"; "VmMaps"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_mmap_base"; "vm_start_brk"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States"; "L_hm"; "E_b3"; "E_b4"; "E_s2"; "E_b2"; "E_b2_S"; "SPINb2"; "SPINb3"; "SPINb4"; "S_hm"; "E_b3_S"; "E_b4_S"; "S_ctor_x"; "Z1"; "Z2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "agree_vars"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.Seg1"; "m2"; "m3"; "m4"; "Post1"; "vcuts1"; "vexits1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1"; "ECALL_MMAP"; "G1"; "FUEL1"; "cutpcs1"; "F1x"; "S_b4ok"; "cuts1"; "sd_hm"; "HMCUT"; "S_b2fail"; "S_b2ok"; "S_b3fail"; "S_b3ok"; "S_b4fail"; "Xhm"; "ZHEAD"; "exits1"; "rho_hm"; "xf1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates"; "S_ctor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "Kx"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm"; "smear_sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "RMH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init StartStates StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartRegenS StartRegen.
(* LPS 727298f3: this segment's states are those B/StartRegenS.v computes per CONFIG_RSEQ
   (Start1R: [X r] for each state [X]), and its runs, checks and restatement those B/StartRegen.v
   proves of them for both values. *)
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS.Start1R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegen.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Seg1.

Variables (m : Model) (B : Z).
(* LPS 727298f3: the start state [S_ctor] is made per CONFIG_RSEQ (StartStates.v); [rq] is this
   run's value, the launch's [kb_rseq (in_kernel inp)] (StartMain.v). *)
Variable rq : bool.
Hypothesis Hh0 : m_halted m = None.
Hypothesis Hlz : m_vm_lazy m = [].
Hypothesis Hmt : m_vm_materialized m = [].
(* LPS 727298f3: the reserved ledger is the image's entries then the vDSO/vvar pair (Fw/SysSpec.v [vdso_pair_ok]). *)
Hypothesis Hres : exists V, vm_reserved (m_vmmaps m) = segments_reserved segsA ++ V /\ vdso_pair_ok V.
Hypothesis Hmaps : ltac2:(tb__ "0|2|
S12S2S3S26Q40A1M0G0A2M1A1S3aS2eVm;A1A1S0G1A1A3").
Hypothesis Hna : ltac2:(tb__ "0|2|
S12S2S3S26Q40A1M0G0A2M1A1S32S2eVm;A1A1S0G1A1A3").
Hypothesis HusedB : vm_backing_used m <= B.
Hypothesis HBlim : ltac2:(tb__ "0|0|
S4eVB;S31S2eVm;A1A1A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
(* LPS 08b1429: the launch model's channel reader; [MI] carries it from here on. *)
Hypothesis Hrdm : m_channel_reader m = true.

Variable ok : assn.
Hypothesis OK0 : ltac2:(tb__ "0|0|
S7bS9Vok;S7fVm;A1A3").
Hypothesis OKF : ltac2:(tb__ "0|1|
S4cS16S2S26Q40A1A1S2S30A1M0S2fR5R4R3R2R1A4S12G0R3S0S30A1A3F_;Fmd;Ftr;Ftp;Frho;S4dS9Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S4cS16S2S26Q40A1A1S2S30A1M0S2fR5R4R3R2R1A4S12G0R3S0S30A1A3F_;Fmd;Ftr;Ftp;Frho;S82S9Vok;R2A3F_;FJ;").

Definition m2 : Model := lazy_rw_model 0x7fff7000 0x10000000 m.
Definition m3 : Model := lazy_none_model 0x8fff7000 0x20000000000 m2.
Definition m4 : Model := lazy_rw_model 0x2008fff7000 0xdfff0001000 m3.

Lemma OKFx : ltac2:(tb__ "0|0|
S2fS10S4dS9Vok;S28R2R1A2A3FBB;Fmm;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S2fS10S82S9Vok;S28R2R1A2A3FBB;Fmm;").
Proof using OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma m2_vmmaps : ltac2:(tb__ "0|4|
S12S34S2eS5dA1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3S32G0A1S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m2, lazy_rw_model, lazy_rw_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, Hmaps. reflexivity. Qed.
Lemma m3_vmmaps : ltac2:(tb__ "0|5|
S12S34S2eS5eA1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z8fff7000A2S25G1Z20000000000A2A4M4S1G3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3A3S1G3G4S32G0A1A3S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m3, lazy_none_model, none_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, m2_vmmaps. reflexivity. Qed.
Lemma m4_vmmaps : ltac2:(tb__ "0|5|
S12S34S2eS5fA1S35S33S2eVm;A1M0A1S1S3S26Q40M1A1M2G2A2M3S7G2G2S25G1Z2008fff7000A2S25G1Zdfff0001000A2A4S1G3S7G2G2S25G1Z8fff7000A2S25G1Z20000000000A2A4M4S1G3S7G2G2S25G1Z7fff7000A2S25G1Z10000000A2A4S0G3A1A3A3A3S1G3G4S32G0A1A3S39G0A1S36G0A1S31G0A1S38G0A1S37G0A1A8A3").
Proof using Hmaps. unfold m4, lazy_rw_model, lazy_rw_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, m3_vmmaps. reflexivity. Qed.

(* LPS 727298f3: every state of this run is [X rq] (B/StartRegenS.v, Start1R), [if rq then X_1 else
   X_0]; a computation over one destructs [rq] first, never computing over the open flag. *)
Ltac rvmc := destruct rq; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Ltac rrefl := destruct rq; reflexivity.

Lemma clear_b2 : objs_clear_e [] (ax_S (E_b2 rq)) = true. Proof. rvmc. Qed.
Lemma clear_b3 : objs_clear_e [] (ax_S (E_b3 rq)) = true. Proof. rvmc. Qed.
Lemma clear_b4 : objs_clear_e [] (ax_S (E_b4 rq)) = true. Proof. rvmc. Qed.

Lemma seg_b2 : forall rho : valuation,
  triple segsA ok (SPA segsA (KxA m B) (E_b2 rq) rho [])
    (LQA segsA (KxA m2 B) 26%positive (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2147446784) (Z_to_bv 64 268435456))) []
       [mkLeafA (E_b3 rq) RsCut]).
Proof using Hmaps Hres Htop OKF OKP.
  intros rho.
  (* The next variable after the grant, [node_seg]'s bound, read per value of [rq]. *)
  replace 26%positive with (ss_next (ax_S (S_b2ok rq))) by rrefl.
  eapply (node_seg ok (KxA m B) (KxA m2 B) (OKFx _ _) (OKFx _ _) (fun n => stableA_KxA segsA n m B) (fun n => stableA_KxA segsA n m2 B)
            (E_b2 rq) (S_b2ok rq) (SPINb2 rq) (E_b3 rq) rho _ [] [] 400%nat 0x6644c 3000%nat ECALL_MMAP).
  - apply (lazy_noreplace_rw_node ok OKF OKP (E_b2 rq) 0x7fff7000 0x10000000 m B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact Htop | exact clear_b2 | exact Hres | unfold VDSO_FLOOR; lia | rewrite Hmaps; intros b s [] | intros e sz [] ].
  - rrefl.
  - rrefl.
  - rrefl.
  - rvmc.
  - rvmc.
  - exact (runF_b2 rq).
  - exact (spin_b2 rq).
  - rrefl.
  - exact (runO_b2 rq).
Qed.

Lemma init_sp_ok_m2 : init_sp_ok (m_vmmaps m2).
Proof using Hmaps Htop. rewrite m2_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.
Lemma init_sp_ok_m3 : init_sp_ok (m_vmmaps m3).
Proof using Hmaps Htop. rewrite m3_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.
Lemma init_sp_ok_m4 : init_sp_ok (m_vmmaps m4).
Proof using Hmaps Htop. rewrite m4_vmmaps. unfold init_sp_ok in *. cbn [vm_init_sp]. exact Htop. Qed.

Lemma seg_b3 : forall rho : valuation,
  triple segsA ok (SPA segsA (KxA m2 B) (E_b3 rq) rho [])
    (LQA segsA (KxA m3 B) 26%positive (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2415882240) (Z_to_bv 64 2199023255552))) []
       [mkLeafA (E_b4 rq) RsCut]).
Proof using Hmaps Hres Htop OKF OKP.
  intros rho.
  replace 26%positive with (ss_next (ax_S (S_b3ok rq))) by rrefl.
  eapply (node_seg ok (KxA m2 B) (KxA m3 B) (OKFx _ _) (OKFx _ _) (fun n => stableA_KxA segsA n m2 B) (fun n => stableA_KxA segsA n m3 B)
            (E_b3 rq) (S_b3ok rq) (SPINb3 rq) (E_b4 rq) rho _ [] [] 400%nat 0x66460 3000%nat ECALL_MMAP).
  - apply (lazy_noreplace_none_node ok OKF OKP (E_b3 rq) 0x8fff7000 0x20000000000 m2 B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m2 | exact clear_b3 | rewrite m2_vmmaps; exact Hres | unfold VDSO_FLOOR; lia
      | rewrite m2_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ].
  - rrefl.
  - rrefl.
  - rrefl.
  - rvmc.
  - rvmc.
  - exact (runF_b3 rq).
  - exact (spin_b3 rq).
  - rrefl.
  - exact (runO_b3 rq).
Qed.

Lemma seg_b4 : forall rho : valuation,
  triple segsA ok (SPA segsA (KxA m3 B) (E_b4 rq) rho [])
    (LQA segsA (KxA m4 B) G1 (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2201439137792) (Z_to_bv 64 15392894357504))) []
       [mkLeafA (E_s2 rq) RsSymJump]).
Proof using Hmaps Hres Htop OKF OKP.
  intros rho. set (rho' := set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))).
  eapply triple_seq.
  { apply triple1_triple.
    apply (lazy_noreplace_rw_node ok OKF OKP (E_b4 rq) 0x2008fff7000 0xdfff0001000 m3 B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m3 | exact clear_b4 | rewrite m3_vmmaps; exact Hres | unfold VDSO_FLOOR; lia
      | rewrite m3_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[[= <- <-]|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ]. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m3 B) (OKFx _ _) (fun n => stableA_KxA segsA n m3 B) _ (SPINb4 rq) 400%nat 0x66474);
      [ rrefl | rrefl | rrefl | exact (runF_b4 rq) | exact (spin_b4 rq) ].
  - change (lazy_rw_model 0x2008fff7000 0xdfff0001000 m3) with m4.
    change (mkAX (S_ret_lit (ax_S (E_b4 rq)) 0x2008fff7000) [] (SLit SHB)) with (S_b4ok rq).
    change (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))) with rho'.
    assert (HstG : stableA segsA G1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
    { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply stableA_KxA]. }
    assert (HokG : ok_frameA segsA ok (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
    { apply OKF. intros r t tr md [_ HK]. eapply KxA_nil; eassumption. }
    eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segsA (KxA m4 B) G1 (S_b4ok rq) rho' [] w Hw) | intros w Hw; exact Hw |].
    apply (cfg_soundA segsA FUEL1 cutpcs1 G1 (cuts1 rq) (exits1 rq) (withGA (fun r => agree_below G1 rho' r) (KxA m4 B)) ok
             (LQA segsA (KxA m4 B) G1 rho' [] [mkLeafA (E_s2 rq) RsSymJump]) [] HokG HstG (check1 rq)); [|left; reflexivity].
    intros E rhoE [<-|[]]. apply exit_postA. left; reflexivity.
Qed.

Definition Post1 (rho : valuation) : assn :=
  fun w : world => exists rho' : valuation,
    agree_vars 25%positive rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m4 B) (E_s2 rq) rho' [] w.

Lemma agree_vars_set_rw_ge : ltac2:(tb__ "0|0|
S11S16S16S11S26Q40A1S89R5R2A2S52R6R5R4A3S52R7R6S81R5R4R3A3A3F_;F_;Fv;Fi;Frho';Frho;Fn;").
Proof. intros n rho rho' i v Hi [A1 A2]. split; [intros j Hj; rewrite rho_set_rw_other by lia; apply A1; exact Hj | intros l; cbn; apply A2]. Qed.

Theorem start1_sum_A : ltac2:(tb__ "0|0|
S16S4eS27Q40S18R1P1A2A2S27Q40S18R1P4A2A2A2S4eS27Q40S18R2P1A2A2S27Q40S18R2P6A2A2A2S4eZ7fff80000000S27Q40S18R3P1A2A2A2S78S9Vok;S7aS9S7fVm;A1S76Vrq;A1R4A4S60R4A1A4F_;F_;F_;Frho;").
Proof using All.
  intros rho H14 H16 HX1.

  (* LPS 727298f3: [S_ctor_x rq] is the xforms applied to [S_ctor rq] (B/StartRegen.v [xf1_ok]). *)
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    exact (SP_xforms segsA (Kx m) xf1 rho (add_facts F1x (S_ctor rq)) (S_ctor_x rq) w (xf1_ok rq)
             (conj (smatch_add_facts segsA rho F1x (S_ctor rq) w Hsm ltac:(unfold F1x; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; assumption) (F1x_below rq)) Hk)). }

  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_sound; [apply (run_hm rq) | exact OK0 | intros H; rewrite (lenient_S_ctor_x rq) in H; discriminate H]. }
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros HinL. apply triple_pure; intros Hag1.
  rewrite (next_S_ctor_x rq) in Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho1 (L_hm rq) w /\ liftK (Kx m) rho1 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) (L_hm rq) rho1).

  eapply triple_conseq; [intros w Hw; exact (proj2 (restate_hm rq (Kx m) rho1 w Hw)) | intros w Hw; exact Hw |].
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_sound; [apply (run_b2 rq) | exact OK0 | intros H; rewrite (lenient_S_hm rq) in H; discriminate H]. }
  apply triple_ex; intros L2. apply triple_ex; intros rho2. apply triple_pure; intros HinL2. apply triple_pure; intros Hag2.
  rewrite (next_S_hm rq) in Hag2.
  destruct HinL2 as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho2 (E_b2_S rq) w /\ liftK (Kx m) rho2 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) (E_b2_S rq) rho2).

  assert (Hw12 : ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m))) by (rewrite Hmaps, Hna; split; apply ivs_wf_nil).
  eapply triple_conseq; [intros w Hw; exact (SP_SPA m B (E_b2_S rq) rho2 w Hlz Hmt HusedB HBlim (proj1 Hw12) (proj2 Hw12) Hrdm Hw) | intros w Hw; exact Hw |].
  change (axA (E_b2_S rq)) with (E_b2 rq).

  eapply triple_seq; [apply seg_b2|].
  apply triple_ex; intros L3. apply triple_ex; intros rho3. apply triple_pure; intros HinL3. apply triple_pure; intros Hag3.
  destruct HinL3 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho3 [] (E_b3 rq) w /\ KxA m2 B rho3 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m2 B) (E_b3 rq) rho3 []).

  eapply triple_seq; [apply seg_b3|].
  apply triple_ex; intros L4. apply triple_ex; intros rho4. apply triple_pure; intros HinL4. apply triple_pure; intros Hag4.
  destruct HinL4 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho4 [] (E_b4 rq) w /\ KxA m3 B rho4 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m3 B) (E_b4 rq) rho4 []).

  eapply triple_seq; [apply seg_b4|].
  apply triple_ex; intros L5. apply triple_ex; intros rho5. apply triple_pure; intros HinL5. apply triple_pure; intros Hag5.
  destruct HinL5 as [<-|[]]. cbn [la_state].
  eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
  intros w [Hsm Hk]. exists rho5.

  assert (A1 : agree_vars 25 rho rho1) by (eapply agree_vars_below; [apply agree_vars_refl | exact Hag1]).
  assert (A2 : agree_vars 25 rho rho2).
  { eapply agree_vars_below; [| eapply agree_below_le; [|exact Hag2]; cbv; discriminate]. unfold rho_hm. apply agree_vars_set_rw_ge; [lia | exact A1]. }
  assert (A3 : agree_vars 25 rho rho3) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A2 | eapply agree_below_le; [|exact Hag3]; cbv; discriminate]).
  assert (A4 : agree_vars 25 rho rho4) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A3 | eapply agree_below_le; [|exact Hag4]; cbv; discriminate]).
  assert (A5 : agree_vars 25 rho rho5) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A4 | eapply agree_below_le; [|exact Hag5]; cbv; discriminate]).
  split; [exact A5|]. split.
  { eapply RMH_below; [|exact Hag5]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag4]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag3]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag2]. unfold rho_hm. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag1]. apply RMH_refl. }
  split; [exact Hsm | exact Hk].
Qed.

Lemma eseg_b2 : forall rho : valuation,
  etriple segsA (SPA segsA (KxA m B) (E_b2 rq) rho [])
    (LQA segsA (KxA m2 B) 26%positive (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2147446784) (Z_to_bv 64 268435456))) []
       [mkLeafA (E_b3 rq) RsCut]).
Proof using Hmaps Hres Htop.
  intros rho.
  replace 26%positive with (ss_next (ax_S (S_b2ok rq))) by rrefl.
  apply (enode_seg (KxA m B) (KxA m2 B) (E_b2 rq) (S_b2ok rq) (E_b3 rq) rho _ [] [] 3000%nat ECALL_MMAP (fun n => stableA_KxA segsA n m2 B)); [| rrefl | exact (runO_b2 rq)].
  apply (lazy_noreplace_rw_enode (E_b2 rq) 0x7fff7000 0x10000000 m B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact Htop | exact clear_b2 | exact Hres | unfold VDSO_FLOOR; lia | rewrite Hmaps; intros b s [] | intros e sz [] ].
Qed.

Lemma eseg_b3 : forall rho : valuation,
  etriple segsA (SPA segsA (KxA m2 B) (E_b3 rq) rho [])
    (LQA segsA (KxA m3 B) 26%positive (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2415882240) (Z_to_bv 64 2199023255552))) []
       [mkLeafA (E_b4 rq) RsCut]).
Proof using Hmaps Hres Htop.
  intros rho.
  replace 26%positive with (ss_next (ax_S (S_b3ok rq))) by rrefl.
  apply (enode_seg (KxA m2 B) (KxA m3 B) (E_b3 rq) (S_b3ok rq) (E_b4 rq) rho _ [] [] 3000%nat ECALL_MMAP (fun n => stableA_KxA segsA n m3 B)); [| rrefl | exact (runO_b3 rq)].
  apply (lazy_noreplace_none_enode (E_b3 rq) 0x8fff7000 0x20000000000 m2 B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m2 | exact clear_b3 | rewrite m2_vmmaps; exact Hres | unfold VDSO_FLOOR; lia
      | rewrite m2_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ].
Qed.

Lemma eseg_b4 : forall rho : valuation,
  etriple segsA (SPA segsA (KxA m3 B) (E_b4 rq) rho [])
    (LQA segsA (KxA m4 B) G1 (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 2201439137792) (Z_to_bv 64 15392894357504))) []
       [mkLeafA (E_s2 rq) RsSymJump]).
Proof using Hmaps Hres Htop.
  intros rho. set (rho' := set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))).
  eapply etriple_seq.
  { apply (lazy_noreplace_rw_enode (E_b4 rq) 0x2008fff7000 0xdfff0001000 m3 B []);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | reflexivity | lia | unfold alloc_ceiling_lo; lia
      | exact init_sp_ok_m3 | exact clear_b4 | rewrite m3_vmmaps; exact Hres | unfold VDSO_FLOOR; lia
      | rewrite m3_vmmaps; cbn [vm_maps]; intros b s [[= <- <-]|[[= <- <-]|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | intros e sz [] ]. }
  change (lazy_rw_model 0x2008fff7000 0xdfff0001000 m3) with m4.
  change (mkAX (S_ret_lit (ax_S (E_b4 rq)) 0x2008fff7000) [] (SLit SHB)) with (S_b4ok rq).
  change (set_rm rho (unmap_range (rm rho) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000))) with rho'.
  assert (HstG : stableA segsA G1 (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply stableA_KxA]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segsA (KxA m4 B) G1 (S_b4ok rq) rho' [] w Hw) | intros w Hw; exact Hw |].
  change (S_b4ok rq) with (vna_state (mkVNA (S_b4ok rq) 100 (SLit 0))).
  (* The measured cuts and exit of check1 and its completeness check, per value of [rq]
     (B/StartRegen.v [vcuts1], [vexits1], [echeck1]). *)
  apply (cfg_complete_autoA segsA FUEL1 cutpcs1 G1 (vcuts1 rq) (vexits1 rq) (withGA (fun r => agree_below G1 rho' r) (KxA m4 B))
           (LQA segsA (KxA m4 B) G1 rho' [] [mkLeafA (E_s2 rq) RsSymJump]) [] HstG); [ | exact (echeck1 rq) | | left; reflexivity].
  - intros n [<-|[<-|[<-|[]]]]; destruct rq; cbv; discriminate.
  - intros E rhoE [<-|[]]. apply eexit_postA. left; reflexivity.
Qed.

Theorem start1_sum_ex_A : ltac2:(tb__ "0|0|
S16S4eS27Q40S18R1P1A2A2S27Q40S18R1P4A2A2A2S4eS27Q40S18R2P1A2A2S27Q40S18R2P6A2A2A2S4eZ7fff80000000S27Q40S18R3P1A2A2A2S77S9S7aS9S7fVm;A1S76Vrq;A1R4A4S60R4A1A3F_;F_;F_;Frho;").
Proof using Hlz Hmt HusedB HBlim Hmaps Hna Hrdm Hres Htop.
  intros rho H14 H16 HX1.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    exact (SP_xforms segsA (Kx m) xf1 rho (add_facts F1x (S_ctor rq)) (S_ctor_x rq) w (xf1_ok rq)
             (conj (smatch_add_facts segsA rho F1x (S_ctor rq) w Hsm ltac:(unfold F1x; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; assumption) (F1x_below rq)) Hk)). }
  eapply etriple_seq.
  { eapply sym_run_etriple; [exact (lenient_S_ctor_x rq) | apply (run_hm rq)]. }
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag1.
  rewrite (next_S_ctor_x rq) in Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho1 (L_hm rq) w /\ liftK (Kx m) rho1 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) (L_hm rq) rho1).
  eapply etriple_conseq; [intros w Hw; exact (proj2 (restate_hm rq (Kx m) rho1 w Hw)) | intros w Hw; exact Hw |].
  eapply etriple_seq.
  { eapply sym_run_etriple; [exact (lenient_S_hm rq) | apply (run_b2 rq)]. }
  apply etriple_ex; intros L2. apply etriple_ex; intros rho2. apply etriple_pure; intros HinL2. apply etriple_pure; intros Hag2.
  rewrite (next_S_hm rq) in Hag2.
  destruct HinL2 as [<-|[]]. cbn [la_state].
  change (fun w => smatch segsA rho2 (E_b2_S rq) w /\ liftK (Kx m) rho2 (w_tr w) (cfg_model (w_cfg w))) with (SP segsA (Kx m) (E_b2_S rq) rho2).
  assert (Hw12 : ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m))) by (rewrite Hmaps, Hna; split; apply ivs_wf_nil).
  eapply etriple_conseq; [intros w Hw; exact (SP_SPA m B (E_b2_S rq) rho2 w Hlz Hmt HusedB HBlim (proj1 Hw12) (proj2 Hw12) Hrdm Hw) | intros w Hw; exact Hw |].
  change (axA (E_b2_S rq)) with (E_b2 rq).
  eapply etriple_seq; [apply eseg_b2|].
  apply etriple_ex; intros L3. apply etriple_ex; intros rho3. apply etriple_pure; intros HinL3. apply etriple_pure; intros Hag3.
  destruct HinL3 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho3 [] (E_b3 rq) w /\ KxA m2 B rho3 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m2 B) (E_b3 rq) rho3 []).
  eapply etriple_seq; [apply eseg_b3|].
  apply etriple_ex; intros L4. apply etriple_ex; intros rho4. apply etriple_pure; intros HinL4. apply etriple_pure; intros Hag4.
  destruct HinL4 as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho4 [] (E_b4 rq) w /\ KxA m3 B rho4 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m3 B) (E_b4 rq) rho4 []).
  eapply etriple_seq; [apply eseg_b4|].
  apply etriple_ex; intros L5. apply etriple_ex; intros rho5. apply etriple_pure; intros HinL5. apply etriple_pure; intros Hag5.
  destruct HinL5 as [<-|[]]. cbn [la_state].
  eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
  intros w [Hsm Hk]. exists rho5.
  assert (A1 : agree_vars 25 rho rho1) by (eapply agree_vars_below; [apply agree_vars_refl | exact Hag1]).
  assert (A2 : agree_vars 25 rho rho2).
  { eapply agree_vars_below; [| eapply agree_below_le; [|exact Hag2]; cbv; discriminate]. unfold rho_hm. apply agree_vars_set_rw_ge; [lia | exact A1]. }
  assert (A3 : agree_vars 25 rho rho3) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A2 | eapply agree_below_le; [|exact Hag3]; cbv; discriminate]).
  assert (A4 : agree_vars 25 rho rho4) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A3 | eapply agree_below_le; [|exact Hag4]; cbv; discriminate]).
  assert (A5 : agree_vars 25 rho rho5) by (eapply agree_vars_below; [apply agree_vars_set_rm; exact A4 | eapply agree_below_le; [|exact Hag5]; cbv; discriminate]).
  split; [exact A5|]. split.
  { eapply RMH_below; [|exact Hag5]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag4]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag3]. apply RMH_unmap; [| rewrite !u64_of_lit by lia; lia].
    eapply RMH_below; [|exact Hag2]. unfold rho_hm. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag1]. apply RMH_refl. }
  split; [exact Hsm | exact Hk].
Qed.
End Seg1.
End Start1.

(* [comment removed for export] *)
Module Start4FailStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates"; "F0"; "RUN1"; "FUEL1"; "PC_OUT"; "PC_SPIN"; "@Corelib.Init.Datatypes"; "list"; "option"; "cons"; "nil"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition F0 : axst := fail_state E_k8x.
Definition PC_OUT : Z := 0x737a0.
Definition PC_SPIN : Z := 0x6bf18.
Definition FUEL1 : nat := 2500%nat.
Definition RUN1_eq__R : option (list leafA) := ltac2:(tb__ "0|0|
SeSfS2S7SaS3S7SaS4S8SaA1A3A3S0S9A5").
Local Strategy expand [RUN1_eq__R].
Definition RUN1 : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RUN1_eq__R).
Lemma RUN1_eq : ltac2:(tb__ "0|0|
S10S6S5SbA1A1SeSfS2S7SaS3S7SaS4S8SaA1A3A3S0S9A5S1A3").
Proof. exact (@eq_refl (option (list leafA)) RUN1_eq__R <: RUN1_eq__R = RUN1). Qed.
Definition L1a : axst := ltac2:(tb__ "0|1|
S6S5SbA1M0A1ScLx;S1G0G0ScLl0;R1S0SbG0SdR2A1Ll1;Ll;X5x2Ll0;S0X6x2").
Definition L1b : axst := ltac2:(tb__ "0|1|
S6S5SbA1M0A1ScLx;S1G0G0ScLl0;R1S0SbG0G0ScLl2;R1S0SbG0SdR2A1Ll3;Ll;X5x2Ll2;Ll1;X5x2Ll0;S0X6x2").
End Start4FailStates.

(* [comment removed for export] *)
Module RegGlob.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "list"; "true"; "bool"; "nil"; "option"; "None"; "Some"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_regs"; "ss_next"; "valuation"; "DUnknown"; "FcsrFrm0"; "SVar"; "cell"; "mkObj"; "mkSS"; "sobj"; "sprop"; "ss_facts"; "ss_objs"; "ss_pc"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "mkLeafA"; "ax_setS"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob"; "E_G"; "P_G"; "CUTS_G"; "FUEL_G"; "NPG"; "NPOST_G"; "Posts_G"; "junk_regs"; "sub_G"; "O_gstk'"; "leaf1G"; "post_regs_G"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "Pre_G"; "facts_G"; "regglob_ret"; "vS0"; "D_G"; "fregs_G"; "vRA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition leaf1G (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S6S2S20A1M0A1S22Lo;Vo;G0G0S22Ll0;R1VA;S20G0G0S22Ll1;R1S28R2A1S20G0VA;Ll3;Ll2;X2x2Ll1;Ll;X2x2Ll0;VA;X6x2").
Definition run_toG (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S33VA;S23ScVfuel;Vcuts;VA;S3A5A2").

Definition CUTS_G : list Z := [regglob_ret].
Definition FUEL_G : nat := 13500%nat.

Definition run_G__R : option (list leafA) := ltac2:(tb__ "0|0|
S23ScS2cS2bS3aS3A5").
Local Strategy expand [run_G__R].
Definition E_G : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1G Pre_G (ro1__)))) run_G__R).
Lemma run_G : ltac2:(tb__ "0|1|
SdS6S2S20A1M0A1S23ScS2cS2bS3aS3A5S8G0S1S20S24S29S41A2S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_G__R <: run_G__R = Some [mkLeafA E_G RsCut]). Qed.

Lemma E_G_at : ltac2:(tb__ "0|3|
SeSdS39S1eS21S29A1M0A1S3cA3SeSdS38S12G0A1S35A3SeSdS2S1bA1S1cG0A1S3bA3SeSdSfS36SfU1S11G0A1M1S10Z0A1M2A4S40A3SdSfS36SfU2G1G2A4S3dA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition junk_regs : list nat := ltac2:(tb__ "0|0|
S1S0U5S1S0U6S1S0U7S1S0UaS1S0UbS1S0UcS1S0UdS1S0UeS1S0UfS1S0U10S1S0U11S5S0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition NPG : positive := 100.
Definition NPOST_G : positive := 132.
Definition post_reg_G (r : nat) : sv := ltac2:(tb__ "0|0|
S4SfL_;S50S0S4fVr;A1S30A3S16S48S2dS49Vr;A1A2A1S36SfVr;S11S21S29A1A1S10Z0A1A4X4x2").
Definition post_regs_G : list sv := map post_reg_G (seq 0 32).

Definition O_gstk' : sobj := ltac2:(tb__ "0|0|
S18S3dS10S51S3eA1A1S10Z0A1S5S17A1S14A5").
Definition P_G0 : axst := ltac2:(tb__ "0|0|
S25S29S19S3cS34S3fS15S7SfA1S42S1aS1dS21S29A1A1U0S32A4S3bS2eS9A9A2").
Definition P_G : axst := Eval vm_compute in P_G0.
Definition Posts_G : list leafA := ltac2:(tb__ "0|0|
S1S20S24S2aS41A2S5S20A1A3").

Definition sub_G : wsub := ltac2:(tb__ "0|0|
S37S0SbS38SfA2S0SaS38SfS48S2dS49R1A1A2S36SfR1S11S21S29A1A1S10Z0A1A4A4Lr;S30A4").
Lemma ent_G : ltac2:(tb__ "0|0|
SdS4S27S29S2aS31A3S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_G : ltac2:(tb__ "0|0|
SdS4S4eS31S35A2S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma P_G_wf : ltac2:(tb__ "0|1|
SeSdS4S26S2aA1S3A3SeSdS4S1fS21S2aA1M0A1S3A3SdS38S12G0A1S2eA3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Theorem regglob_sum : ltac2:(tb__ "0|0|
S4dOF_;S45S13S2S4aQ40A1A1S47ScR4R3A3S46ScS35R4A3S4cScR6S44ScR5S3aR4R3A5S43ScR5S35R4R3S2fA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact run_G | exact Hok | reflexivity | exact Hst]. }
  apply triple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (triple_entailsA segsA ok J NF E_G P_G sub_G rho1 tp); [exact ent_G | exact wid_G | exact Hst |].
  eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G].
Qed.

Theorem regglob_sum_ex : ltac2:(tb__ "0|0|
S45S13S2S4aQ40A1A1S46ScS35R3A3S4bScS44ScR4S3aR3R2A5S43ScR4S35R3R2S2fA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_seq.
  { eapply sym_run_etripleA; [reflexivity | exact Hst | exact run_G]. }
  apply etriple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (etriple_entailsA segsA J NF E_G P_G sub_G rho1 tp); [exact ent_G | exact wid_G | exact Hst |].
  eapply etriple_conseq; [ | intros w Hw; exact Hw | apply etriple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G].
Qed.
End RegGlob.

