(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "list"; "prod"; "true"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sstate"; "ss_facts"; "ss_next"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "JGA"; "am_below"; "am_eqb"; "am_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs.XA"; "entAs_check"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "eqb"; "leb"; "ltb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tv_sub_eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundW SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section XA.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2S25A1S24OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S15Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;Vam;A9").

Definition entAs_check (s0 : wsub) (n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|3|
S5S3S12S6A2M0Vs0;S26VNP;VX;VA;A3A3S2G0A1S0S0L_;M1S27VX;VA;R1A3G1S1cR1VNP;A2G1S2bVNP;SaVX;A1M2A2G1S29G2Vtvi;A2G1S2aR1Vtvi;Vtvj;A3G1S16G2Vami;A2G1S17S18R1Vamj;A2Vami;A2G1SbVn;VvE;A2G1S22Z0VrA;A2G1S23VrA;VrE;A2S4G1S21VrA;VrE;A2S28S9VX;A1S1bR1VvA;A2Z1VvE;A4S1X0x2X0x2S1X0x2S1X0x2S1X0x2S1X0x2S1X0x2S1X0x2S1X0x2S1X0x2S1X0x2Ts;").

Lemma entAs_sound : ltac2:(tb__ "0|2|
S1aS12S8S8S2S3S6S6A2A1M0G0S14S14S6S11S11S6SfS0S1eRcRbRaR9R8R7R6R5R4R3R2R1AcS4A3S7S7SdS13Vsegs;VJGv;RcRaA2ReR2R1A5S1dR10R4R3A3S10S7S7SeS13Vsegs;VJGv;ReRcA2R10R1R4A5SeS1fZ0S19RaRbR1A3M1A2S20G1S19R9R8R6A3A2A2A2Lrho';A2F_;F_;Fw;Frho;FrhoX;F_;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj;Ftvi;FA;FX;Fn;Fs0;").
Proof using FB Kc ML P0f rho0.
  intros s0 n X A tvi tvj ami amj vA rA rE vE H rhoX rho w Hw Hag. unfold entAs_check in H. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [Hb H].
  apply lazy_andb_prop in H as [H0 H].
  exists (rho_sub rho (s0 ++ infer_sub NP X A)). split.
  - eapply (SPJ_entails_JGA segs C NP Kc rho0 P0f FB ML); [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact Hw].
  - unfold emeasZ. rewrite <- eval_subst.
    rewrite (eval_agree_vals n rhoX rho vE Hag Hb).
    apply Z.leb_le in H0.
    pose proof (urange (eval rho (sv_subst (s0 ++ infer_sub NP X A) vA))) as R1. pose proof (urange (eval rho vE)) as R2.
    apply lazy_orb_prop in H as [Hlt|H].
    + apply Z.ltb_lt in Hlt. nia.
    + apply lazy_andb_prop in H as [Heq Hu]. apply Z.eqb_eq in Heq. subst rE.
      destruct Hw as [Hsm _]. destruct w as [tr [ms md]].
      pose proof (uleq_sound rho _ _ 1 _ (smatch_facts_hold segs _ _ _ Hsm) Hu) as U1. unfold U in U1. lia.
Qed.

Section TRXA.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
ScScScSdR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OScScR3VTR;R3R2A2F_;VTR;SdSeR5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Lemma entAs_TR : ltac2:(tb__ "0|3|
S1aS12S8S8S2S3S6S6A2M0A1M1G1G1S14S14S6S11S11S6S7S7ScSfS0S1eR10RfReRdRcRbR9R8R7R6R5R4AcS4A3S2cG0RcRbA3S1dR11R5R4A3S7SeS1fZ0S19RaRbR1A3M2A2S20G2S19R9R8R7A3A2A2VTR;S13Vsegs;VJGv;RfRdA2R12R2A4R6A2F_;Frho';VTR;S13Vsegs;VJGv;R10RdA2R12R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FX;Fn;Fs0;").
Proof using FB Kc ML P0f TR_exw TR_pre TR_pureh rho0.
  intros s0 n X A tvi tvj tvj' ami amj vA rA rE vE rhoX rho FAMb H HP Hag HA.
  eapply TR_pre; [ | apply (TR_exw valuation (fun rho' w => (0 <= emeasZ rA vA rho' < emeasZ rE vE rhoX) /\ SPJ segs (JGv tvj' amj) A rho' w))].
  - intros w Hw. destruct (entAs_sound s0 n X A tvi tvj ami amj vA rA rE vE H rhoX rho w Hw Hag) as (rho' & H' & Hm).
    exists rho'. split; [exact Hm|]. destruct H' as [Hs HJ]. split; [exact Hs|]. eapply JGA_tv_perm; [exact HP | exact HJ].
  - intros rho'. apply TR_pureh. intros Hm. exact (HA rho' Hm).
Qed.
End TRXA.
End XA.
