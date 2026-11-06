(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "True"; "iff"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "option"; "prod"; "true"; "Some"; "nat"; "length"; "None"; "false"; "snd"; "fst"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "leafA"; "shadow_ok"; "join_regs"; "axwf"; "join2"; "word_byte"; "shadow_addr"; "stepA_inv"; "step_outA"; "ax_setS"; "la_state"; "run_past_branch"; "run_to_pc"; "sym_runA"; "sym_runA_ref"; "sym_stepA"; "try_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "eval"; "agree_below"; "ss_lenient"; "ss_objs"; "rm"; "sprop"; "sv_below"; "outside_all"; "ss_regs"; "smatch"; "ss_facts"; "ss_pc"; "SVar"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "SLit"; "holds"; "mkVal"; "rl"; "rw"; "sfcsr"; "sobj"; "sprop_below"; "sstate"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "cfg_ms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_halted"; "page_size"; "with_vm_backing"; "m_vmmaps"; "vm_noaccess"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_svc_pending"; "MachineOk"; "machine_result"; "ms_mem"; "ms_pc"; "ms_regs"; "step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA.A"; "smatchA"; "SPA"; "stableA"; "linpath"; "vnext_rel"; "LQA"; "ok_frameA"; "hidz"; "joinval"; "mat_blind"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "div"; "of_nat"; "to_pos"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "triple1"; "tcons"; "w_cfg"; "w_tr"; "wstep"; "ok_src"; "ok_tgt"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "add"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "xword"; "liftKA"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "MI"; "vms"; "virt"; "vmd"; "hid"; "hid_same"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition jpredA : Type := ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S7S52A1S51OF_;F_;F_;F_;").

Definition liftKA (K : list event -> Model -> Prop) : jpredA := fun _ _ tr md => K tr md.
Definition liftJA (J : jpred) : jpredA := fun rho _ tr md => J rho tr md.

Section A.
Variable segs : list Segment.

Definition hidz (md : Model) (tp : list word) (ms : machine_state) : Prop := ltac2:(tb__ "0|5|
S47Q40M0A1S0S8S8bVmd;Vtp;R1A3ScA3S3S0SaS47Q8M1A1M2A1M3S5cVms;R2A2M4SdG2S49G1Z0A2A2A3S1S0G3G4S10G2A1A3S0S8S91S57S56Vmd;A1A1S48G0R2A2A2ScA3A2A2F_;Fa;").

Definition smatchA (rho : valuation) (tp : list word) (A : axst) (w : list event * config) : Prop := ltac2:(tb__ "0|2|
S1S36Vsegs;Vrho;S16VA;A1S89Vtp;Vw;A2A4S1S87Vsegs;S4fS12S7S52A1S4dVw;A3M0A1M1Vtp;A3S1S0S8S1cVA;A1ScA3S1S1aVrho;VA;A2S67G1Vtp;S50G0A1A3A2A2A2A2").

Definition SPA (J : jpredA) (A : axst) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|0|
S73S1S60Vrho;Vtp;VA;R1A4VJ;Vrho;Vtp;S78R1A1S4fS77R1A1A1A4A2Lw;").

Definition LQA (J : jpredA) (n : positive) (rho : valuation) (tp : list word) (leaves : list leafA) : assn := ltac2:(tb__ "0|0|
S73S2S19S19S2S2bS2bS1S7cS19R2Vleaves;A3S1S2eVn;Vrho;R1A3S1S60R1Vtp;S23R2A1R3A4VJ;R1Vtp;S78R3A1S4fS77R3A1A1A4A2A2A2Lrho';A2LL;A2Lw;").

Lemma LQA_weaken : ltac2:(tb__ "0|1|
S81S4bS4bS2bS2bS7S47Q40A1A1S7S19A1M0G0S73S7eR8R7A2S2eR9R7R6A3S19S7cS19R1R6A3S7cS19R2R6A3F_;FL;S65RcRaR8R7R6R4A6S65RdRcRaR8R6R5A6F_;F_;F_;F_;Fw;Fleaves';Fleaves;Ftp;Frho';Frho;Fn';Fn;FJ;").
Proof using .
  intros J n n' rho rho' tp leaves leaves' w Hle Hag Hsub (L & rho'' & Hin & Hag' & Hsm & Hk).
  exists L, rho''. split; [apply Hsub; exact Hin|]. split; [|split; assumption].
  eapply agree_below_trans; [exact Hag|]. eapply agree_below_le; eauto.
Qed.

Lemma smatchA_smatch : ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S15SbS7S52A1S4dA2S60R4R3R2R1A4S36Vsegs;R5S16R3A1S89R4R2A2A4F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w [H _]. exact H. Qed.

Lemma smatchA_MI : ltac2:(tb__ "0|1|
S2bS7S47Q40A1A1S15S7S52A1M0S58S51S60R6R5R4S9G0S4dR3S4eR2R1A2A4A4S87Vsegs;R2R6A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md (_ & H & _). exact H. Qed.

Lemma smatchA_hidz : ltac2:(tb__ "0|1|
S2bS7S47Q40A1A1S15S7S52A1M0S58S51S60R6R5R4S9G0S4dR3S4eR2R1A2A4A4S67R2R6R3A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md (_ & _ & _ & _ & H). exact H. Qed.

Lemma smatchA_axwf : ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S15SbS7S52A1S4dA2S60R4R3R2R1A4S0S8S1cR3A1ScA3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w (_ & _ & H & _). exact H. Qed.

Lemma smatchA_shadow : ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S15SbS7S52A1S4dA2S60R4R3R2R1A4S1aR5R3A2F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w (_ & _ & _ & H & _). exact H. Qed.

Lemma smatchA_swf : ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S15SbS7S52A1S4dA2S60R4R3R2R1A4S0S8S46S16R3A1A1ScA3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w [H _]. exact (proj1 H). Qed.

Lemma smatchA_halted : ltac2:(tb__ "0|2|
S2bS7S47Q40A1M0A1S15S7S52A1M1S58S51S60R6R5R4S9G1S4dR3S4eR2R1A2A4A4S0SaG0A1S53R2A1S10G0A1A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md [Hsm _]. pose proof Hsm as (_ & _ & _ & Hidle & _).
  cbn [fst snd cfg_ms cfg_model virt w_cfg w_tr] in Hidle. apply model_idle_vmd in Hidle. exact Hidle.
Qed.

Lemma smatchA_pending : ltac2:(tb__ "0|2|
S2bS7S47Q40A1M0A1S15S7S52A1M1S58S51S60R6R5R4S9G1S4dR3S4eR2R1A2A4A4S0SaG0A1S59R3A1S10G0A1A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md [Hsm _]. pose proof Hsm as (_ & _ & Hp & _).
  cbn [fst snd cfg_ms cfg_model virt w_cfg w_tr] in Hp. rewrite vms_svc_pending in Hp. exact Hp.
Qed.

Lemma smatchA_pcv : ltac2:(tb__ "0|3|
S2bS7S47Q40M0A1M1A1S15S7S52A1M2S58S51S60R6R5R4S9G2S4dR3S4eR2R1A2A4A4S0G1S5dR3A1S49G0S38S16R5A1A1A2A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md [Hsm _]. pose proof Hsm as (_ & Hpc & _).
  cbn [fst snd cfg_ms cfg_model virt w_cfg w_tr] in Hpc. rewrite vms_pc in Hpc. exact Hpc.
Qed.

Lemma smatchA_facts : ltac2:(tb__ "0|0|
S2bS7S47Q40A1A1S15SbS7S52A1S4dA2S60R4R3R2R1A4S85S32S3eR5A1S37S16R3A1A1A3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w [H _]. eapply smatch_facts; exact H. Qed.

Lemma smatchA_step : ltac2:(tb__ "0|1|
S2bS2bS7S47Q40A1A1S15S15S7S52A1M0S58S51S51S58S60RaR8R7S9G0S4dR5S4eR4R3A2A4A4S20R8R7A2S2eS2cS16R9A1A1RcRbA3S86Vsegs;RbR6R5A4S36Vsegs;RdS16RaA1S9G0S4dR9S4eR5S8aR7A1A2A4A4S58S0S58S88R8ReR1A3R7A3S8cRaRfRbR2A4S60R11R10ReS9G0S4dRdS4eR3RaA2A4A4F_;F_;Fms';F_;F_;F_;F_;F_;Fmsv';Fmd';Fmd;Fms;Ftr;FA';FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A A' tr ms md md' msv' HsmA (Hle & Hlen & HX & Hb & He) Hag Hme Hsm' ms' Hv Hhs.
  pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz).
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    rewrite (mat_equiv_vmd segs tp md md' Hme), Hv. exact Hsm'.
  - cbn. exact (proj2 (proj2 Hme) HMI).
  - eapply axwf_stable; eauto.
  - eapply shadow_ok_stable; eauto. exact (proj1 Hsm).
  - cbn. intros a Ha. rewrite (mat_equiv_hid segs tp md md' Hme) in Ha. rewrite (Hhs a Ha), (mat_equiv_vmmaps segs tp md md' Hme). exact (Hhz a Ha).
Qed.

Definition ok_frameA (ok : world -> Prop) (J : jpredA) : Prop := ltac2:(tb__ "0|4|
S2bS7S47Q40A1M0A1S7S52A1M1S58S51S58VJ;R6R5R4R2A4S87Vsegs;R3R6A3S0SaG0A1M2S53R4A1S10G0A1M3A3S0G2S59R6A1G3A3S0S5bS58A1S5fVsegs;S88R6R9R7A3A2S5aS58R5A2A3Vok;S9G1S4dR9S4eR8R7A2A4A1F_;F_;F_;F_;F_;Fmsv';Fmd;Fms;Ftr;Ftp;Frho;").

Definition stableA (n : positive) (J : jpredA) : Prop := ltac2:(tb__ "0|0|
S2bS2bS7S47Q40A1A1S7S52A1S51S51S2eVn;R6R5A3S86Vsegs;R5R3R2A4VJ;R8R6R5R4A4VJ;R8R7R6R4A4F_;F_;F_;Fmd';Fmd;Ftr;Ftp;Frho';Frho;").

Lemma stableA_mono : ltac2:(tb__ "0|0|
S4bS4bS81S7eR3R2A2S62R4R2A2S62R4R3A2F_;F_;FJ;Fm;Fn;").
Proof using .
  intros n m J Hle H rho rho' tp tr md md' Hag Hme HJ. eapply H; [|exact Hme|exact HJ]. eapply agree_below_le; eauto.
Qed.

Definition mat_blind (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|1|
S7S52A1S51S7SbS47Q40A1M0G0A2A1S7G0A1S6VK;R4S55R2R1R3A3A2VK;R4S55R2S14G0A1R3A3A2A2Fp;Fl;Fmd;Ftr;").

Lemma mat_blind_equiv : ltac2:(tb__ "0|1|
S7S52A1M0S51OF_;F_;S7S47Q40A1A1G0S51S51S69R5A1S86Vsegs;R5R3R2A4R7R5R4A2R8R6R4A2F_;F_;F_;Fmd';Fmd;Ftr;Ftp;FK;").
Proof using .
  intros K tp tr md md' HK ((p & ->) & _) H.
  apply (proj2 (HK tr md (m_vm_lazy md) p)). apply (proj1 (HK tr md (m_vm_lazy md) (m_vm_materialized md))).
  rewrite with_vm_backing_id. exact H.
Qed.

Lemma stableA_liftKA : ltac2:(tb__ "0|0|
S4bS7S52A1S51OF_;F_;S69R1A1S62R3S83R2A1A2F_;FK;Fn;").
Proof using . intros n K HK rho rho' tp tr md md' _ Hme H. unfold liftKA in *. eapply mat_blind_equiv; eauto. Qed.

Lemma stableA_of_proj : forall {B : Type} n (f : Model -> B) (P : valuation -> list word -> list event -> B -> Z -> Prop),
  (forall md l p, f (with_vm_backing l p md) = f (with_vm_backing l [] md)) ->
  (forall rho rho' tp tr b z, agree_below n rho rho' -> P rho tp tr b z -> P rho' tp tr b z) ->
  stableA n (fun rho tp tr md => P rho tp tr (f md) (paid md tp)).
Proof using .
  intros B n f P Hf HP rho rho' tp tr md md' Hag Hme H.
  destruct Hme as ((p & ->) & Hpaid & _). rewrite Hpaid.
  rewrite Hf. rewrite <- (with_vm_backing_id md) in H. rewrite Hf in H. eapply HP; eauto.
Qed.

Lemma ok_frameA_tgt : ltac2:(tb__ "0|1|
S7S52A1M0OF_;S81S2bS7S47Q40A1A1G0S51R5R4R3R2R1A4S76R7R3A2F_;Fmd;Ftr;Ftp;Frho;S66S7bVsegs;R3A2R2A2F_;FJ;FSpec;").
Proof using .
  intros Spec J HJ rho tp tr ms md msv' Hj HMI Hh Hp Hs. split; [exact (HJ _ _ _ _ Hj)|].
  cbn. intros evs. eapply sstepA_no_error; eauto.
Qed.

Lemma ok_frameA_src : ltac2:(tb__ "0|1|
S7S52A1M0OF_;S81S2bS7S47Q40A1A1G0S51R5R4R3R2R1A4S76R7R3A2F_;Fmd;Ftr;Ftp;Frho;S66S7aVsegs;R3A2R2A2F_;FJ;FSpec;").
Proof using .
  intros Spec J HJ rho tp tr ms md msv' Hj HMI Hh Hp Hs. split; [exact (HJ _ _ _ _ Hj)|].
  cbn. eapply unmodeledA_not; eauto.
Qed.

Definition vnext_rel (A A' : axst) (rho : valuation) (tp : list word) (tr : list event) (ms : machine_state) (md : Model) : Prop := ltac2:(tb__ "0|0|
S1S8fVsegs;S16VA;A1S16VA';A1Vrho;Vtr;S88Vmd;Vtp;Vms;A3S8aVmd;A1A7S20VA;VA';A2A2").

Theorem sym_step_soundA : ltac2:(tb__ "0|2|
S15S2bS7S47Q40A1A1S7S52A1M0S58S51S0S8S2fS16R6A1A1S11A3S60R6R5R7S9G0S4dR4S4eR3R2A2A4A4S21OLx;S28Vsegs;R8A2S15S64R9R1R8R7R6R5R4A7LA';S15S15S3S64RaR2R9R8R7R6R5A7S64RaR1R9R8R7R6R5A7A2LA2;LA1;M1G1S90S5Lr;X21x4F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA;").
Proof using .
  intros A rho tp tr ms md Hlen HsmA. pose proof HsmA as (Hsm & _ & Hwf & Hsh & _).
  pose proof (sym_stepA_sound segs A rho tr (vms md tp ms) (vmd md) Hlen Hsm Hsh Hwf) as X.
  pose proof (sym_stepA_kept segs A) as K.
  destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r]; [split; assumption | | | exact I];
    destruct K as [K1 K2]; destruct X as [X|X]; [left|right|left|right]; split; assumption.
Qed.

Lemma vnext_rel_wstep : ltac2:(tb__ "0|3|
S15S15S2bS7S47Q40A1A1S7S52A1M0S58S51S60R5R4R7S9G0S4dR3S4eR2R1A2A4A4S64R8R7R6R5R4R3R2A7S2S58S58S2S51S51S2S2bS2bS1S79Vsegs;S9G0S4dR8S4eR7R6A2A4S9G0S4dR8S4eR3R2A2A4M1A3S1S73S79Vsegs;S9G0S4dR9S4eR8R7A2A4R1A3S0S73R2S9G0S4dRaS4eR5R4A2A4A3F_;Fw';S1S2eS2cS16RcA1A1M2RaR1A3S1S7eG2S2cS16RbA1A1A2S1S60R1R9RbG1A4S86Vsegs;R9R6R2A4A2A2A2A2A2Lrho';A2Lmd';A2Lms';A2F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA';FA;").
Proof using .
  intros A A' rho tp tr ms md HsmA [(msv' & rho' & Hstep & Hag & Hle & Hsm') Hinv].
  pose proof (smatchA_MI _ _ _ _ _ _ HsmA) as HMI.
  pose proof (smatchA_halted _ _ _ _ _ _ HsmA) as Hh.
  pose proof (smatchA_pending _ _ _ _ _ _ HsmA) as Hp.
  destruct (wstepA_of_step segs tr ms md tp msv' HMI Hh Hp Hstep) as (ms' & md' & Hacc & Hw & Hv & Hme & Hhs).
  exists ms', md', rho'. split; [exact Hw|]. split.
  { intros w' Hw'. exact (wstepA_step_inv segs tr ms md ms' md' w' Hh Hp Hacc Hw'). }
  split; [exact Hag|]. split; [exact Hle|]. split; [|exact Hme].
  eapply smatchA_step; eauto.
Qed.

Lemma triple1_branchA : ltac2:(tb__ "0|1|
S73OF_;S81S15S15S15S2bS7S47Q40A1A1S66R7R6A2S0S8S2fS16R6A1A1S11A3S62S2cS16R7A1A1R8A2S7S52A1M0S58S51S60R8R7RbS9G0S4dR3S4eR2R1A2A4A4S3S64RcRbR9R8R4R3R2A7S64RcRaR9R8R4R3R2A7A2F_;Fmd;Fms;Ftr;S75Vsegs;RbS61RaR9R6R5A4S73S2S2bS2bS1S2eS2cS16RbA1A1R8R1A3S3S61RcRaR1R7R2A5S61RcR9R1R7R2A5A2A2Lrho';A2Lw;A4F_;F_;F_;F_;Ftp;Frho;FA2;FA1;FA;FJ;Fok;").
Proof using .
  intros ok J A A1 A2 rho tp Hok Hlen Hst Hnext. apply triple1_step.
  intros [tr [ms md]] [HsmA Hk]. cbn in Hk.
  pose proof (smatchA_MI _ _ _ _ _ _ HsmA) as HMI.
  pose proof (smatchA_halted _ _ _ _ _ _ HsmA) as Hh.
  pose proof (smatchA_pending _ _ _ _ _ _ HsmA) as Hp.
  assert (Hok' : forall Ax, vnext_rel A Ax rho tp tr ms md -> ok (tr, mkCfg ms md)).
  { intros Ax [(msv' & rho' & Hstep & _) _]. exact (Hok rho tp tr ms md msv' Hk HMI Hh Hp Hstep). }
  destruct (Hnext tr ms md HsmA) as [N|N].
  - split; [exact (Hok' _ N)|].
    destruct (vnext_rel_wstep A A1 rho tp tr ms md HsmA N) as (ms' & md' & rho' & _ & Huniq & Hag & Hle & HsmA' & Hme).
    intros w' Hw. rewrite (Huniq w' Hw).
    exists rho'. split; [exact Hag|]. left. split; [exact HsmA' | eapply Hst; eauto].
  - split; [exact (Hok' _ N)|].
    destruct (vnext_rel_wstep A A2 rho tp tr ms md HsmA N) as (ms' & md' & rho' & _ & Huniq & Hag & Hle & HsmA' & Hme).
    intros w' Hw. rewrite (Huniq w' Hw).
    exists rho'. split; [exact Hag|]. right. split; [exact HsmA' | eapply Hst; eauto].
Qed.

Inductive linpath : axst -> axst -> Prop :=
| lp_refl : forall A, linpath A A
| lp_step : forall A A' B, sym_stepA segs A = StNextA A' -> linpath A' B -> linpath A B.

Lemma run_past_branch_lin : ltac2:(tb__ "0|0|
SeS15S15S0SaS15A1S24Vsegs;R3R2A3SdS15R1A2A3S63R3R2A2F_;FB;FA;Fn;").
Proof using .
  induction n as [|n IH]; intros A B H; cbn [run_past_branch] in H; [discriminate|].
  destruct (sym_stepA segs A) as [A'| | |] eqn:Hs; try discriminate.
  destruct (is_branch_at segs (ss_pc (ax_S A))).
  - injection H as <-. eapply lp_step; [exact Hs | apply lp_refl].
  - eapply lp_step; [exact Hs | apply IH; exact H].
Qed.

Lemma run_to_pc_lin : ltac2:(tb__ "0|0|
SeS4aS15S15S0SaS15A1S25Vsegs;R4R3R2A4SdS15R1A2A3S63R3R2A2F_;FB;FA;Fpc;Fn;").
Proof using .
  induction n as [|n IH]; intros pc A B H; cbn [run_to_pc] in H.
  - destruct (ss_pc (ax_S A) =? pc); [injection H as <-; apply lp_refl | discriminate].
  - destruct (ss_pc (ax_S A) =? pc); [injection H as <-; apply lp_refl |].
    destruct (sym_stepA segs A) as [A'| | |] eqn:Hs; try discriminate.
    eapply lp_step; [exact Hs | eapply IH; exact H].
Qed.

Lemma linpath_inv : ltac2:(tb__ "0|2|
S15S15S63R2R1A2S1S7eS2cS16R3A1M0A1S2cS16R2A1M1A1A2S1S0S8S2fG1A1S2fG0A1A3S1S0S7SbS2aS2aA2A1S17R2A1S17R3A1A3S0S2aS18R2A1S18R3A1A3A2A2A2F_;FB;FA;").
Proof using .
  intros A B H. induction H as [A | A A' B Hs Hl IH].
  - repeat split; reflexivity || lia.
  - pose proof (sym_stepA_kept segs A) as K. rewrite Hs in K. destruct K as (K1 & K2 & K3 & K4 & _).
    destruct IH as (I1 & I2 & I3 & I4). repeat split; try lia; congruence.
Qed.

Lemma linpath_sound : ltac2:(tb__ "0|0|
S73OF_;S81S15S15S2bS7S47Q40A1A1S66R6R5A2S63R5R4A2S0S8S2fS16R6A1A1S11A3S62S2cS16R7A1A1R8A2S74Vsegs;RaS61R9R8R6R5A4S73S2S2bS2bS1S2eS2cS16RaA1A1R8R1A3S61RbR9R1R7R2A5A2Lrho';A2Lw;A4F_;F_;F_;F_;Ftp;Frho;FB;FA;FJ;Fok;").
Proof using .
  intros ok J A B rho tp Hok Hl. revert rho. induction Hl as [A | A A' B Hs Hl IH]; intros rho Hlen Hst.
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
    intros w Hw. exists rho. split; [apply agree_below_refl | exact Hw].
  - pose proof (sym_stepA_kept segs A) as K. rewrite Hs in K. destruct K as (K1 & K2 & _).
    apply triple1_triple. eapply triple1_seq_l.
    { apply (triple1_branchA ok J A A' A' rho tp Hok Hlen Hst).
      intros tr ms md Hsm. pose proof (sym_step_soundA A rho tp tr ms md Hlen Hsm) as X. rewrite Hs in X. left. exact X. }
    apply triple_ex. intros rho'. apply triple_pure. intros Hag.
    assert (T' : triple segs ok (SPA J A' rho' tp) (fun w => exists rho'', agree_below (ss_next (ax_S A')) rho' rho'' /\ SPA J B rho'' tp w)).
    { apply IH; [rewrite K2; exact Hlen | eapply stableA_mono; [exact K1 | exact Hst]]. }
    assert (POST : forall w, (exists rho'', agree_below (ss_next (ax_S A')) rho' rho'' /\ SPA J B rho'' tp w) ->
                   exists rho'', agree_below (ss_next (ax_S A)) rho rho'' /\ SPA J B rho'' tp w).
    { intros w (rho'' & Hag' & Hsp). exists rho''. split; [|exact Hsp].
      eapply agree_below_trans; [exact Hag | eapply agree_below_le; [exact K1 | exact Hag']]. }
    apply triple_disj; (eapply triple_conseq; [intros w Hw; exact Hw | exact POST | exact T']).
Qed.

Definition joinval (rho : valuation) (base : positive) (ms : machine_state) : valuation := ltac2:(tb__ "0|0|
S3fS4bS8S47Q40A1L_;S80R1Vbase;A2S41Vrho;R1A2S8eS5eVms;A1S49Q5S72S4cR1A1S4cVbase;A1A2A2A2X8x2Lv;S40Vrho;A1S31Vrho;A1A3").

Lemma joinval_agree : ltac2:(tb__ "0|0|
S2bS4bS58S2eR2R3S68R3R2R1A3A3Fms;Fbase;Frho;").
Proof using .
  intros rho base ms. split; [|split; reflexivity]. intros i Hi. cbn.
  destruct (i <? base)%positive eqn:E; [reflexivity|]. apply Pos.ltb_ge in E. lia.
Qed.

Lemma join_regs_length : ltac2:(tb__ "0|1|
S4bS7S2aA1M0G0S4aS0SeSfS2aR3A2SfS2aR2A2A3S0SeSfS2aS1bR5R2R4R3A4A2SfS2aR4A2A3F_;Fr;Fl2;Fl1;Fbase;").
Proof using .
  intros base l1. induction l1 as [|a t IH]; intros [|b t2] r H; cbn in H |- *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma join_regs_nth : ltac2:(tb__ "0|4|
S4bS7S2aA1M0G0S4aSeS2aS8dR2SfS2aR5A2M1A2S8dR3G1A2S3S1S0S2aS84S2aR4S1bR8R5R7R6A4R3A4M2S84S2aR4R7R3A4M3A3S0S2aG3S84S2aR4R6R3A4A3A2S0S2aG2S39S70S6aS6aS4cR8A1R5A2S6fR4A1A2A1A1A3A2F_;F_;Fd;Fk;Fr;Fl2;Fl1;Fbase;").
Proof using .
  intros base l1. induction l1 as [|a t IH]; intros [|b t2] r k d H1 H2; cbn in H1, H2; try lia.
  destruct k as [|k]; cbn [join_regs nth].
  - destruct (sv_eqb a b) eqn:E.
    + left. split; [reflexivity|]. apply sv_eqb_sound. exact E.
    + right. f_equal. f_equal. lia.
  - destruct (IH t2 (r + 1) k d ltac:(lia) ltac:(lia)) as [X|X]; [left; exact X | right].
    rewrite X. f_equal. f_equal. lia.
Qed.

Lemma join_regs_below : ltac2:(tb__ "0|1|
S4bS7S2aA1M0G0S4aS4bS4bS6bZ0R3A2S0S8S7dS2aS33R3A1R6A3ScA3S7eR4R3A2S6bS6aS6aS4cR9A1R6A2S6fSfS2aR8A2A1A2S4cR4A1A2S0S8S7dS2aS33R5A1S1bRaR7R9R8A4A3ScA3F_;F_;F_;F_;Fbnd;Fm;Fr;Fl2;Fl1;Fbase;").
Proof using .
  intros base l1. induction l1 as [|a t IH]; intros [|b t2] r m bnd Hr Hb Hm Hlen; cbn in Hb |- *; try reflexivity.
  apply andb_prop in Hb as [Ha Ht]. apply andb_true_intro. split.
  - destruct (sv_eqb a b); [eapply sv_below_mono; eauto|]. cbn. apply Pos.ltb_lt.
    enough (Z.pos (Z.to_pos (Z.pos base + r)) < Z.pos bnd) by lia. cbn [length] in Hlen. rewrite Z2Pos.id by lia. lia.
  - eapply IH; [lia | exact Ht | exact Hm | cbn in Hlen; lia].
Qed.

Lemma join_regs_below2 : ltac2:(tb__ "0|1|
S4bS7S2aA1M0G0S4aS4bS4bS6bZ0R3A2S0S8S7dS2aS33R3A1R5A3ScA3S7eR4R3A2S6bS6aS6aS4cR9A1R6A2S6fSfS2aR7A2A1A2S4cR4A1A2S0S8S7dS2aS33R5A1S1bRaR7R9R8A4A3ScA3F_;F_;F_;F_;Fbnd;Fm;Fr;Fl2;Fl1;Fbase;").
Proof using .
  intros base l1. induction l1 as [|a t IH]; intros [|b t2] r m bnd Hr Hb Hm Hlen; cbn in Hb |- *; try reflexivity.
  apply andb_prop in Hb as [Ha Ht]. apply andb_true_intro. split.
  - destruct (sv_eqb a b) eqn:E; [apply sv_eqb_sound in E; subst a; eapply sv_below_mono; eauto|]. cbn. apply Pos.ltb_lt.
    enough (Z.pos (Z.to_pos (Z.pos base + r)) < Z.pos bnd) by lia. cbn [length] in Hlen. rewrite Z2Pos.id by lia. lia.
  - eapply IH; [lia | exact Ht | exact Hm | cbn in Hlen; lia].
Qed.

Lemma smatchA_join : ltac2:(tb__ "0|c|
S2bS7S47Q40A1A1S15S15S4bS7S52A1M0S58S51S60R8R7R6S9G0S4dR3S4eR2R1A2A4A4S7eS2cS16R7A1M1A1R5A2S0S4aS38G1A1S38S16R8A1M2A1A3S0S7S2aA1S3bG2A1S3bS16R9A1M3A1A3S0S42S3aG3A1S3aS16RaA1M4A1A3S0SaS2aA1S3cG4A1S3cS16RbA1M5A1A3S0S7S43A1S30G5A1S30S16RcA1A1A3S0S7SbS2aS2aA2A1S17RcA1S17RdA1A3S0S2aS18RdA1S18ReA1A3S0S4bS2cS16ReA1A1S7fRdP20M6A2A3S0SeSfS2aS35S16RfA1A1A2U20M7A3SeS8dR1G7A2S3S0S2aS84S2aR2S35S16R12A1A1S3dZ0A1M8A4M9S84S2aR2S35S16R13A1MaA1G8A4A3S0S2aG9S39S70S6aS4cR11A1S6fR2A1A2A1A1A3A2F_;Fk;S0S8S7dS2aS33S7fR10G6A2A1S35S16R11A1A1A3ScA3S32S7cS32R1S37GaA1MbA3S7cS32R2S37S16R15A1A1A3F_;Ff;S0S8S7dS32S44S7fR12G6A2A1GbA3ScA3S60S68R17R13R11A3R16R14S9G0S4dR12S4eR11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Fbase;FM;FBi;Ftp;Frho;").
Proof using .
  intros rho tp Bi M base tr ms md HsmA Hle Hpc Hfr Hfc Hrv Hob HX Hb Hnx Hlen Hregs Hrb Hfacts Hfb.
  set (rho' := joinval rho base ms).
  pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz).
  assert (Hag : agree_below (ss_next (ax_S Bi)) rho rho').
  { eapply agree_below_le; [exact Hle | apply joinval_agree]. }
  pose proof (smatch_agree segs rho rho' (ax_S Bi) _ Hag Hsm) as Hsm'.
  pose proof (proj1 Hsm) as Hswf.
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm' |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm' |- *.
    destruct Hsm' as (Hwf' & Hpc' & Hpend & Hhalt & Hrom & Hroc & Hregs' & Hfregs & Hfcsr & Hresv & Hmem & Hfacts').
    cbn [fst snd cfg_ms cfg_model] in Hpc', Hpend, Hhalt, Hrom, Hroc, Hregs', Hfregs, Hfcsr, Hresv, Hmem, Hfacts'.
    unfold smatch. cbn [fst snd cfg_ms cfg_model].
    split.
    {   unfold swf. unfold swf in Hwf'. repeat (apply andb_prop in Hwf'; destruct Hwf' as [Hwf' ?]).
      rewrite Hlen, Hfr, Hfc, Hrv, Hob, Hnx, Hrb. rewrite H5. cbn [andb Nat.eqb].
      repeat (apply andb_true_intro; split).
      - eapply forallb_mono_below; [|exact H3]. lia.
      - destruct (ss_fcsr (ax_S Bi)); [reflexivity|]. eapply sv_below_mono; [|exact H2]. lia.
      - destruct (ss_resv (ax_S Bi)); [|reflexivity]. eapply sv_below_mono; [|exact H1]. lia.
      - apply forallb_forall. intros o Ho. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) H0 o Ho)]. lia.
      - exact Hfb. }
    split; [rewrite Hpc; exact Hpc'|]. split; [exact Hpend|]. split; [exact Hhalt|].
    split; [exact Hrom|]. split; [exact Hroc|].
    split.
    {   intros r Hr0. unfold reg_sv. pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr.
      destruct (bv_unsigned r =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
      destruct (Hregs (Z.to_nat (bv_unsigned r)) ltac:(lia)) as [E|E]; rewrite E.
      - pose proof (Hregs' r Hr0) as X. unfold reg_sv in X. rewrite E0 in X. exact X.
      - cbn [eval rw rho' joinval]. rewrite Z2Pos.id by lia.
        destruct (Z.to_pos (Z.pos base + Z.of_nat (Z.to_nat (bv_unsigned r))) <? base)%positive eqn:El.
        + apply Pos.ltb_lt in El. rewrite <- (Pos2Z.id base) in El at 2.
          assert (Z.pos (Z.to_pos (Z.pos base + Z.of_nat (Z.to_nat (bv_unsigned r)))) < Z.pos base) by lia.
          rewrite Z2Pos.id in H by lia. lia.
        + replace (Z.pos base + Z.of_nat (Z.to_nat (bv_unsigned r)) - Z.pos base) with (bv_unsigned r) by lia.
          rewrite Z_to_bv_bv_unsigned. unfold vms, restrict. cbn [ms_regs]. reflexivity. }
    split; [unfold fregs_match, freg_sv; rewrite Hfr; exact Hfregs|]. split; [rewrite Hfc; exact Hfcsr|]. split; [rewrite Hrv; exact Hresv|].
    split; [rewrite Hob; exact Hmem|].
    apply Forall_forall. intros f Hf. exact (proj1 (Forall_forall _ _) Hfacts' f (Hfacts f Hf)).
  -   unfold axwf in Hwf |- *. rewrite HX, Hb, Hnx. apply andb_prop in Hwf as [H1 H2].
    apply andb_true_intro. split.
    + apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H1 r Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; [eapply sv_below_mono; [|exact Y1]; lia | eapply sv_below_mono; [|exact Y2]; lia].
    + eapply sv_below_mono; [|exact H2]. lia.
  -   eapply (shadow_ok_stable Bi M rho rho'); [exact Hag | exact Hwf | exact Hswf | exact HX | exact Hb | | exact Hsh].
    unfold exts. rewrite Hob. reflexivity.
Qed.

Lemma join2_spec : ltac2:(tb__ "0|1|
S4bS15S15S15S15S0SaS15A1S1dR5R4R3R2A4SdS15R1A2A3S1S0S7SbS2aS2aA2A1S17R2A1S17R5A1A3S1S0S2aS18R2A1S18R5A1A3S1S0S8S2fS16R2A1M0A1S11A3S7eR6S2cG0A1A2A2A2A2F_;FM;FB2;FB1;FA;Fg;").
Proof using .
  intros g A B1 B2 M H. unfold join2 in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection H as <-. cbn. repeat split; try reflexivity. lia.
Qed.

Lemma try_join_spec : ltac2:(tb__ "0|1|
S15S15S15S15S0SaS15A1M0S29Vsegs;R4R3R2A4SdS15R1A2A3S2S15S15S2S15S15S1S63R6R2A2S1S63R5R1A2S0G0S1dS2cS16R7A1A1R7R2R1A4SdS15R4A2A3A2A2LB2;A2LB1;A2F_;FM;FA2;FA1;FA;").
Proof using .
  intros A A1 A2 M H. unfold try_join in H.
  destruct (run_past_branch segs JOIN_FUEL A1) as [B1|] eqn:H1; [|discriminate].
  destruct (run_to_pc segs JOIN_FUEL (ss_pc (ax_S B1)) A2) as [B2|] eqn:H2; [|discriminate].
  exists B1, B2. split; [eapply run_past_branch_lin; exact H1|]. split; [eapply run_to_pc_lin; exact H2 | exact H].
Qed.

Lemma join2_sound : ltac2:(tb__ "0|0|
S81S4bS15S15S15S15S2bS7S47Q40A1A1S73S0SaS15A1S1dR8R7R6R5A4SdS15R4A2A3S62R9RaA2S3S61RbR8R5R4R3A5S61RbR7R5R4R3A5A2S2S2bS2bS1S2eRcR7R1A3S61RdR8R1R6R5A5A2Lrho';A2F_;F_;F_;Fw;Ftp;Frho;FM;FB2;FB1;FA;Fg;FJ;").
Proof using .
  intros J g A B1 B2 M rho tp [tr [ms md]] H Hst Hsp. unfold join2 in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection H as EM.
  apply andb_prop in E as [E Cb2]. apply andb_prop in E as [E Cb1]. apply andb_prop in E as [E CX2]. apply andb_prop in E as [E CX1].
  apply andb_prop in E as [E CL2]. apply andb_prop in E as [E CL1]. apply andb_prop in E as [E CFb].
  apply andb_prop in E as [E CF2]. apply andb_prop in E as [E CF1]. apply andb_prop in E as [E COb].
  apply andb_prop in E as [E CRv]. apply andb_prop in E as [E CFc]. apply andb_prop in E as [E CFr].
  apply andb_prop in E as [E CN2]. apply andb_prop in E as [Cpc CN1].
  apply Z.eqb_eq in Cpc. apply Nat.eqb_eq in CN1. apply Nat.eqb_eq in CN2.
  apply (list_eqb_sound sv_eqb sv_eqb_sound) in CFr. apply sfcsr_eqb_sound in CFc. apply osv_eqb_sound in CRv.
  apply (list_eqb_sound sobj_eqb sobj_eqb_sound) in COb.
  apply negb_true_iff in CL1. apply negb_true_iff in CL2.
  apply (list_eqb_sound xr_eqb xr_eqb_sound) in CX1. apply (list_eqb_sound xr_eqb xr_eqb_sound) in CX2.
  apply sv_eqb_sound in Cb1. apply sv_eqb_sound in Cb2.
  set (base := Pos.max (Pos.max (ss_next (ax_S B1)) (ss_next (ax_S B2))) g) in EM.
  exists (joinval rho base ms). split.
  { eapply agree_below_le; [|apply joinval_agree]. lia. }
  assert (FACTS : forall Si, forallb (fun f => existsb (sprop_eqb f) (ss_facts Si)) (ss_facts (ax_S A)) = true ->
                  forall f, In f (ss_facts (ax_S A)) -> In f (ss_facts Si)).
  { intros Si HF f Hf. pose proof (proj1 (forallb_forall _ _) HF f Hf) as X. apply existsb_exists in X as (f' & Hin & Heq).
    apply sprop_eqb_sound in Heq. subst f'. exact Hin. }
  assert (HJ : forall rho0, J rho0 tp tr md -> J (joinval rho0 base ms) tp tr md).
  { intros rho0 HJ0. eapply Hst; [| apply mat_equiv_refl | exact HJ0]. eapply agree_below_le; [|apply joinval_agree]. lia. }
  destruct Hsp as [[HsmA Hk]|[HsmA Hk]]; (split; [|apply HJ; exact Hk]); subst M.
  - eapply (smatchA_join rho tp B1); try exact HsmA; cbn; try reflexivity; try lia.
    + symmetry. exact CX1.
    + symmetry. exact Cb1.
    + rewrite join_regs_length; congruence.
    + intros k Hk'. destruct (join_regs_nth base (ss_regs (ax_S B1)) (ss_regs (ax_S B2)) 0 k (SLit 0) ltac:(lia) ltac:(lia)) as [[X _]|X];
        [left; exact X | right; rewrite X; f_equal; f_equal; lia].
    + eapply (join_regs_below base _ _ 0 (ss_next (ax_S B1))); [lia | | lia | rewrite CN1; lia].
      pose proof (smatchA_swf _ _ _ _ HsmA) as W. unfold swf in W. repeat (apply andb_prop in W; destruct W as [W ?]). assumption.
    + apply FACTS. assumption.
    + apply forallb_forall. intros f Hf. eapply sprop_below_mono; [|exact (proj1 (forallb_forall _ _) CFb f Hf)]. lia.
  - eapply (smatchA_join rho tp B2); try exact HsmA; cbn; try reflexivity; try lia; try congruence.
    + rewrite join_regs_length; congruence.
    + intros k Hk'. destruct (join_regs_nth base (ss_regs (ax_S B1)) (ss_regs (ax_S B2)) 0 k (SLit 0) ltac:(lia) ltac:(lia)) as [[X Y]|X];
        [left; rewrite X; exact Y | right; rewrite X; f_equal; f_equal; lia].
    + eapply (join_regs_below2 base _ _ 0 (ss_next (ax_S B2))); [lia | | lia | rewrite CN2; lia].
      pose proof (smatchA_swf _ _ _ _ HsmA) as W. unfold swf in W. repeat (apply andb_prop in W; destruct W as [W ?]). assumption.
    + apply FACTS. assumption.
    + apply forallb_forall. intros f Hf. eapply sprop_below_mono; [|exact (proj1 (forallb_forall _ _) CFb f Hf)]. lia.
Qed.

Section Driver.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Hok : ok_frameA ok J.

Lemma sym_run_sound_genA0_ref : ltac2:(tb__ "0|3|
SeS7S4aA1S15S8S7S19A1M0S2bS7S47Q40A1A1S0S8S2fS16R5A1A1S11A3S62S2cS16R6A1A1VJ;A2S0SaG0A1S27Vsegs;R9R8R7R6A5SdG0R5A2A3S8OLfirst;R7S75Vsegs;Vok;S61VJ;R8R5R4A4M1S65VJ;S2cS16R8A1A1R5R4R6A5M2A4S74Vsegs;Vok;G1G2A4X8x2F_;F_;F_;Ftp;Frho;Fleaves;Ffirst;FA;Fcuts;Ffuel;").
Proof using Hok.
  induction fuel as [|fuel IH]; intros cuts A first leaves rho tp Hlen Hst Hrun.
  - cbn in Hrun. destruct first; [discriminate|]. inversion Hrun; subst.
    intros n Hg w [Hsm Hk]. apply Hg. exists (mkLeafA A RsFuel), rho.
    split; [left; reflexivity|]. split; [apply agree_below_refl|]. split; assumption.
  - cbn [sym_runA_ref] in Hrun.
    assert (Hleaf : forall r, triple segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp [mkLeafA A r])).
    { intros r n Hg w [Hsm Hk]. apply Hg. exists (mkLeafA A r), rho.
      split; [left; reflexivity|]. split; [apply agree_below_refl|]. split; assumption. }
    destruct (negb first && memZ (ss_pc (ax_S A)) cuts)%bool eqn:Hcut.
    + destruct first; [discriminate|]. inversion Hrun; subst. apply Hleaf.
    + pose proof (sym_stepA_kept segs A) as Hkept.
      assert (Hgo : forall A1 A2 l1 l2,
                stepA_inv A A1 -> stepA_inv A A2 ->
                (forall tr ms md, smatchA rho tp A (tr, mkCfg ms md) ->
                   vnext_rel A A1 rho tp tr ms md \/ vnext_rel A A2 rho tp tr ms md) ->
                sym_runA_ref segs fuel cuts A1 false = Some l1 ->
                sym_runA_ref segs fuel cuts A2 false = Some l2 ->
                (forall L, In L l1 -> In L leaves) -> (forall L, In L l2 -> In L leaves) ->
                triple1 segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp leaves)).
      { intros A1 A2 l1 l2 (Hle1 & Hl1 & _) (Hle2 & Hl2 & _) Hnext Hr1 Hr2 Hs1 Hs2.
        eapply triple1_seq_l; [apply triple1_branchA; [exact Hok | exact Hlen | exact Hst | exact Hnext]|].
        apply triple_ex. intros rho'. apply triple_pure. intros Hag.
        apply triple_disj.
        - eapply triple_conseq; [intros w Hw; exact Hw | | exact (IH cuts A1 false l1 rho' tp ltac:(rewrite Hl1; exact Hlen) (stableA_mono _ _ _ Hle1 Hst) Hr1)].
          intros w HQ. exact (LQA_weaken J _ _ rho rho' tp l1 leaves w Hle1 Hag Hs1 HQ).
        - eapply triple_conseq; [intros w Hw; exact Hw | | exact (IH cuts A2 false l2 rho' tp ltac:(rewrite Hl2; exact Hlen) (stableA_mono _ _ _ Hle2 Hst) Hr2)].
          intros w HQ. exact (LQA_weaken J _ _ rho rho' tp l2 leaves w Hle2 Hag Hs2 HQ). }
      assert (FORK : forall A1 A2,
                stepA_inv A A1 /\ stepA_inv A A2 ->
                (forall tr ms md, smatchA rho tp A (tr, mkCfg ms md) ->
                   vnext_rel A A1 rho tp tr ms md \/ vnext_rel A A2 rho tp tr ms md) ->
                match sym_runA_ref segs fuel cuts A1 false, sym_runA_ref segs fuel cuts A2 false with
                | Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end = Some leaves ->
                if first then triple1 segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp leaves)
                else triple segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp leaves)).
      { intros A1 A2 [K1 K2] Hnext Hr.
        destruct (sym_runA_ref segs fuel cuts A1 false) as [l1|] eqn:H1; [|discriminate].
        destruct (sym_runA_ref segs fuel cuts A2 false) as [l2|] eqn:H2; [|discriminate].
        injection Hr as <-.
        assert (TT : triple1 segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp (l1 ++ l2))).
        { apply (Hgo A1 A2 l1 l2); auto.
          - intros L HL. apply in_or_app. left. exact HL.
          - intros L HL. apply in_or_app. right. exact HL. }
        destruct first; [exact TT | apply triple1_triple; exact TT]. }
      destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r] eqn:Hss.
      * assert (TT : triple1 segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp leaves)).
        { apply (Hgo A' A' leaves leaves); auto.
          intros tr ms md Hsm. pose proof (sym_step_soundA A rho tp tr ms md Hlen Hsm) as X. rewrite Hss in X.
          left; exact X. }
        destruct first; [exact TT | apply triple1_triple; exact TT].
      * apply (FORK A1 A2 Hkept); [|exact Hrun].
        intros tr ms md Hsm. pose proof (sym_step_soundA A rho tp tr ms md Hlen Hsm) as X. rewrite Hss in X. exact X.
      *
        assert (Hnext : forall tr ms md, smatchA rho tp A (tr, mkCfg ms md) ->
                   vnext_rel A A1 rho tp tr ms md \/ vnext_rel A A2 rho tp tr ms md).
        { intros tr ms md Hsm. pose proof (sym_step_soundA A rho tp tr ms md Hlen Hsm) as X. rewrite Hss in X. exact X. }
        destruct (try_join segs A A1 A2) as [M|] eqn:Htj; [|apply (FORK A1 A2 Hkept Hnext Hrun)].
        destruct Hkept as [(Hle1 & Hl1 & _) (Hle2 & Hl2 & _)].
        destruct (try_join_spec A A1 A2 M Htj) as (B1 & B2 & HL1 & HL2 & HJ2).
        destruct (join2_spec _ _ _ _ _ HJ2) as (HXM & HbM & HlenM & HleM).
        assert (TT : triple1 segs ok (SPA J A rho tp) (LQA J (ss_next (ax_S A)) rho tp leaves)).
        { eapply triple1_seq_l; [apply triple1_branchA; [exact Hok | exact Hlen | exact Hst | exact Hnext]|].
          apply triple_ex. intros rho'. apply triple_pure. intros Hag.
          assert (ARM : forall Ai Bi, stableA (ss_next (ax_S Ai)) J -> ss_lenient (ax_S Ai) = false ->
                    (ss_next (ax_S A) <= ss_next (ax_S Ai))%positive ->
                    linpath Ai Bi ->
                    (forall r w, SPA J Bi r tp w -> exists r', agree_below (ss_next (ax_S A)) r r' /\ SPA J M r' tp w) ->
                    triple segs ok (SPA J Ai rho' tp) (LQA J (ss_next (ax_S A)) rho tp leaves)).
          { intros Ai Bi HstI HlenI HleI HLI HBi.
            eapply triple_seq; [apply (linpath_sound ok J Ai Bi rho' tp Hok HLI HlenI HstI)|].
            apply triple_ex. intros rho''. apply triple_pure. intros Hag'.
            eapply triple_seq.
            { eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
              intros w Hsp. exact (HBi rho'' w Hsp). }
            apply triple_ex. intros rho3. apply triple_pure. intros Hag3.
            eapply triple_conseq; [intros w Hw; exact Hw | |
              exact (IH cuts M false leaves rho3 tp HlenM (stableA_mono _ _ _ HleM Hst) Hrun)].
            intros w HQ. eapply (LQA_weaken J _ _ rho rho3 tp leaves leaves w HleM); [|intros L HL; exact HL|exact HQ].
            eapply agree_below_trans; [exact Hag|]. eapply agree_below_trans; [eapply agree_below_le; [exact HleI | exact Hag']|].
            exact Hag3. }
          apply triple_disj.
          - apply (ARM A1 B1); [eapply stableA_mono; [exact Hle1|exact Hst] | rewrite Hl1; exact Hlen | exact Hle1 | exact HL1 |].
            intros r w Hsp. exact (join2_sound J _ A B1 B2 M r tp w HJ2 Hst (or_introl Hsp)).
          - apply (ARM A2 B2); [eapply stableA_mono; [exact Hle2|exact Hst] | rewrite Hl2; exact Hlen | exact Hle2 | exact HL2 |].
            intros r w Hsp. exact (join2_sound J _ A B1 B2 M r tp w HJ2 Hst (or_intror Hsp)). }
        destruct first; [exact TT | apply triple1_triple; exact TT].
      * destruct first; [discriminate|]. inversion Hrun; subst. apply Hleaf.
Qed.

Lemma sym_run_sound_genA0 : ltac2:(tb__ "0|3|
SeS7S4aA1S15S8S7S19A1M0S2bS7S47Q40A1A1S0S8S2fS16R5A1A1S11A3S62S2cS16R6A1A1VJ;A2S0SaG0A1S26Vsegs;R9R8R7R6A5SdG0R5A2A3S8OLfirst;R7S75Vsegs;Vok;S61VJ;R8R5R4A4M1S65VJ;S2cS16R8A1A1R5R4R6A5M2A4S74Vsegs;Vok;G1G2A4X8x2F_;F_;F_;Ftp;Frho;Fleaves;Ffirst;FA;Fcuts;Ffuel;").
Proof using Hok.
  intros fuel cuts A first leaves rho tp HL HS Hrun. rewrite sym_runA_ref_eq in Hrun.
  exact (sym_run_sound_genA0_ref fuel cuts A first leaves rho tp HL HS Hrun).
Qed.

End Driver.

End A.

Definition xword (rho : valuation) (A : axst) (x : word) : Prop := ltac2:(tb__ "0|6|
S2SbS2aS2aA2M0G0S2S4aS4aS2S4aS4aS1S7cG0R3S17VA;A1A3S1S1S6bS48Q40M1S2dVrho;S13S2aS2aR3A3A2A2M2R2A2S6cR2S6aG2S48G1S2dVrho;S12S2aS2aR3A3A2A2A2A2A2S1S1S6bZ0M3R1A2S6cR1Z8M4A2A2S1S1S6bG3S6aS48G1S2dVrho;S18VA;A1A2A2S6eR2G4A2A2M5A2S6cG5S71Z2Z40A2A2A2S0S47G1A1Vx;S1eG5R1A2A3A2A2A2A2Lj;A2Ly;A2Lr;A2").

Lemma shadow_addr_word_byte : ltac2:(tb__ "0|2|
S4aS4aS6bZ0S6aR2S6eR1Z8M0A2A2A2S0S47Q40A1S1fR3R2A2S1eS6aR3S6eR2G0A2A2M1S6dG1G0A2A2A3F_;Fy;Foff;").
Proof. intros off y H. unfold shadow_addr. rewrite word_byte_self; [reflexivity | exact H]. Qed.

Lemma shadow_ok_transport : ltac2:(tb__ "0|7|
S2bS2bS15S15S0S7SbS2aS2aA2M0A1S17R1A1S17R2A1A3S0S47Q40A1M1S2dR4S18R2A1A2S2dR5S18R3A1A2A3G0S7cG0R1S17R5A1A3S1S0G1S2dR7S13S2aS2aR2A3M2A2S2dR8G2A2A3S0G1S2dR7S12S2aS2aR2A3M3A2S2dR8G3A2A3A2F_;Fr;G1S82R8R6R1A3S34R9S30S16R7A1A1R2A3S4S0SaS47Q8A1M4A1M5S31RaR3A2S10G4A1A3A1S1S34RaS30S16R8A1A1R4A3S0G5S31RaR4A2S31RbR4A2A3A2F_;F_;F_;Fx;S1aR8R6A2M6G6F_;F_;F_;F_;F_;FA';FA;Frho';Frho;").
Proof.
  intros rho rho' A A' HX Hb Hev HT H. unfold shadow_ok in H |- *. rewrite HX, Hb.
  apply Forall_forall. intros [b l] Hr. destruct (Hev _ Hr) as [E1 E2]. cbn [fst snd] in E1, E2.
  pose proof (proj1 (Forall_forall _ _) H _ Hr) as X. unfold xr_ok in X |- *. cbn [fst snd] in X |- *. rewrite E1, E2.
  destruct X as (H8 & Hnw & X). split; [exact H8|]. split; [exact Hnw|].
  intros a Ha. destruct (X a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
  assert (XW : forall j, 0 <= j < 8 -> xword rho A (word_byte (bv_unsigned (eval rho (ax_base A)) + a / 8) j)).
  { intros j Hj. exists (b, l), a, j. cbn [fst snd]. split; [exact Hr|]. split; [exact Ha|]. split; [exact Hj|]. split; [exact Hoff | reflexivity]. }
  assert (Hj0 : 0 <= (bv_unsigned (eval rho (ax_base A)) + a / 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  pose proof (shadow_addr_word_byte (bv_unsigned (eval rho (ax_base A))) a (proj1 Hoff)) as Eba.
  destruct (HT (shadow_addr (bv_unsigned (eval rho (ax_base A))) a) ltac:(rewrite Eba; apply XW; exact Hj0) Hout ltac:(rewrite Hv; discriminate)) as [Hout' Hrm'].
  split; [exact Hoff|]. split; [exact Hout'|]. split.
  - intros j Hj. destruct (Hwd j Hj) as [Ho Hrj]. destruct (HT _ (XW j Hj) Ho Hrj) as [Ho' Hr']. split; [exact Ho' | rewrite Hr'; exact Hrj].
  - exists v. rewrite Hrm'. split; [exact Hv | exact Henc].
Qed.

Lemma shadow_ok_transport_objs : ltac2:(tb__ "0|1|
S2bS15S45S47Q40A1S82R4R3R1A3S34R5S30S16R4A1A1R2A3S4S0SaS47Q8A1M0A1S31R6R3A2S10G0A1A3A1S34R7S30R5A1R4A3F_;F_;F_;Fx;S1aR4R3A2S1aR5S22R4R3A2A2F_;F_;FS';FA;Frho;").
Proof.
  intros rho A S' HT H. eapply (shadow_ok_transport rho rho A); [reflexivity | reflexivity | intros; split; reflexivity | | exact H].
  cbn [ax_S ax_setS]. intros x Hx Ho Hd. split; [exact (HT x Hx Ho Hd) | reflexivity].
Qed.

Lemma mod8_of_page : ltac2:(tb__ "0|1|
S4aS0S4aS6dR1S54A2Z0M0A3S0S4aS6dR2Z8A2G0A3F_;Fx;").
Proof.
  intros x H. pose proof (Z.div_mod x page_size ltac:(unfold page_size; lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D. unfold page_size. replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma xword_avoid_aligned : ltac2:(tb__ "0|6|
S2bS15S4aS4aS47Q40M0A1S0S4aS6dR3Z8A2Z0A3M1G1SbS2aS2aA2M2S4aS7cG2R2S17R8A1A3S1S6bS48G0S2dRaS13S2aS2aR3A3A2A2M3R2A2S6cR2S6aG3S48G0S2dRaS12S2aS2aR3A3A2A2A2A2A2S4S1S6bR9S48G0S1fS48G0S2dRbS18RaA1A2A2R3A2A2M4A2S6cG4R8A2A2A1F_;F_;Fy;Frr;S82R8R7R4A3S4S1S6bR7S48G0R5A2M5A2S6cG5R6A2A2A1F_;F_;F_;F_;Fx;Fhi;Flo;FA;Frho;").
Proof.
  intros rho A lo hi x Hlo Hhi Hxs (rr & y & j & Hr & Hy & Hj & Hz & ->).
  pose proof (Hxs rr y Hr Hy) as X. unfold shadow_addr in X. rewrite Z_to_bv_unsigned, bv_wrap_small in X by (change (bv_modulus 64) with (2 ^ 64); lia).
  destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2.
  apply word_outside_aligned_range; [lia | exact Hj | exact Hlo | exact Hhi | exact X].
Qed.

Lemma mod8_of_pages : ltac2:(tb__ "0|2|
S4aS4aS0S4aS6dR2S54A2Z0M0A3M1G1S0S4aS6dS6aR4R3A2Z8A2G0A3F_;F_;Fn;Fa;").
Proof.
  intros a n Ha Hn. rewrite Z.add_mod, (mod8_of_page a Ha), (mod8_of_page n Hn) by lia. reflexivity.
Qed.

Lemma xword_agree : ltac2:(tb__ "0|0|
S2bS2bS15S47Q40A1S2eS2cS16R2A1A1R4R3A3S0S8S1cR3A1ScA3S82R5R4R3A3S82R7R5R4A3F_;F_;F_;Fx;FA;Frho';Frho;").
Proof.
  intros rho rho' A x Hag Hwf (rr & y & j & Hr & Hy & Hj & Hz & ->).
  unfold axwf in Hwf. apply andb_prop in Hwf as [HX Hb].
  pose proof (proj1 (forallb_forall _ _) HX _ Hr) as Y. unfold xr_below in Y. apply andb_prop in Y as [Y1 Y2].
  rewrite <- (eval_agree _ _ _ _ Hag Y1), <- (eval_agree _ _ _ _ Hag Y2) in Hy. rewrite <- (eval_agree _ _ _ _ Hag Hb) in Hz |- *.
  exists rr, y, j. split; [exact Hr|]. split; [exact Hy|]. split; [exact Hj|]. split; [exact Hz | reflexivity].
Qed.

Lemma xword_avoid : ltac2:(tb__ "0|6|
S2bS15S4aS4aS47Q40M0A1SbS2aS2aA2M1S4aS4aS7cG1R3S17R7A1A3S1S6bS48G0S2dR9S13S2aS2aR4A3A2A2M2R3A2S6cR3S6aG2S48G0S2dR9S12S2aS2aR4A3A2A2A2A2A2S1S6bZ0R3A2S6cR3Z8M3A2A2S4S1S6bR9S48G0S1eS6aS48G0S2dRbS18RaA1A2A2S6eR5G3A2A2R4A2A2M4A2S6cG4R8A2A2A1F_;F_;F_;Fj;Fy;Frr;S82R6R5R2A3S4S1S6bR5S48G0R3A2M5A2S6cG5R4A2A2A1F_;F_;Fx;Fhi;Flo;FA;Frho;").
Proof.
  intros rho A lo hi x Hxs (rr & y & j & Hr & Hy & Hj & Hz & ->). exact (Hxs rr y j Hr Hy Hj).
Qed.
