(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "PG_P"; "pcuts"; "FUEL_pg"; "pexits"; "pg_cutpcs2"; "K318"; "K34c"; "K3dc"; "K29c"; "K4a"; "K4b"; "Kbbp"; "Kcm"; "Kfin"; "Knw"; "Kproj"; "O_pp2d"; "P_inv"; "P_ok"; "Pre_pg"; "pN"; "E_r2"; "E_sc3"; "E_sc4"; "Kext"; "Klat"; "pSCR"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nat"; "list"; "prod"; "Some"; "app"; "nil"; "option"; "pair"; "false"; "S"; "fst"; "negb"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sprop"; "sv"; "valuation"; "SLit"; "sobj"; "agree_below"; "SVar"; "holds"; "ss_facts"; "ss_next"; "ss_objs"; "SPBranch"; "rw"; "smatch"; "DUnknown"; "SAlu"; "SPNot"; "cell"; "mkObj"; "sprop_below"; "sprop_eqb"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "lnode"; "mkLN"; "check_cut"; "vdir"; "SPfam"; "forallb_lazy"; "Vdown"; "Vup"; "check_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "skipn"; "@Corelib.Numbers.BinNums"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d"; "R2_P"; "Pre_r2"; "P_ret"; "Posts_r2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d"; "Pre_sc"; "P_sc"; "Posts_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_glue"; "E3r"; "E4r"; "E5c"; "E3"; "E4"; "E5"; "E5b"; "R3"; "R4"; "R5"; "T3"; "T4"; "T5a"; "T5d"; "s3"; "s4"; "s5"; "E5a"; "T3r"; "T4r"; "T5"; "T5b"; "T5c"; "T5e"; "s318"; "s3dc"; "s418"; "set_obj"; "d3"; "d3r"; "d4"; "d4r"; "nf3r"; "nf4r"; "nf5"; "sel5"; "sel5b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "set_objs"; "RsSymJump"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "BC_EQ"; "BC_NE"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_tess_polygon_glue.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.

Import ListNotations.
Close Scope bv_scope.

Definition set_obj (S : sstate) (i : nat) (o : sobj) : sstate := ltac2:(tb__ "0|1|
S8cVS;S22S31S53S31Vi;S37VS;A1M0A3S1bS31Vo;S54S31S27Vi;A1G0A3A3A3A2").
Definition O_pp2d_lit (k : Z) : sobj := ltac2:(tb__ "0|0|
S3fS1aS30Z0A1S3cS99S30Vk;A1S30Z4A1A3S23S3eA1S3bA5").

Definition E3 : sstate := E_sc3 PG_P.
Definition E3r : sstate := set_obj E3 6 (O_pp2d_lit 3).
Definition d3 := Eval vm_compute in match state_diff E3 E3r with Some (d, _) => d | None => [] end.
Lemma sd3 : ltac2:(tb__ "0|3|
S2aS24S20S1fS20S2eS2eA2A1M0S1fS2dA1M1A2M2A1S4eS62S5fA2S21G2S25G0G1S7bS23S2dA1A4A2A3").
Proof. vm_compute. reflexivity. Qed.
Definition s3 : wsub := Eval vm_compute in infer_sub 10 E3r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc.
Definition R3 : list sobj := Eval vm_compute in match entails_fr E3r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s3 with Some R => R | None => [] end.
Lemma efr3 : ltac2:(tb__ "0|1|
S2aS24S1fS31A1M0A1S87S5fS5cS6dA3S21G0S66A2A3").
Proof. vm_compute. reflexivity. Qed.
Lemma chk3 : ltac2:(tb__ "0|0|
S2aS1cS8fS5fS5cS6dS66S5eA5S1dA3").
Proof. vm_compute. reflexivity. Qed.
Definition T3 : sstate := Eval vm_compute in import_post s3 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E3r) R3.
Lemma imp3 : ltac2:(tb__ "0|0|
S2aS2cS90S6dS44S5dS36S5fA1S66A5S69A3").
Proof. vm_compute. reflexivity. Qed.

Definition T3r : sstate := ltac2:(tb__ "0|0|
S4fS7aS69U0S10A3S35S62A1A2").
Definition d3r := Eval vm_compute in match state_diff T3 T3r with Some (d, _) => d | None => [] end.
Definition nf3r := Eval vm_compute in match state_diff T3 T3r with Some (_, nf) => nf | None => [] end.
Lemma sd3r : ltac2:(tb__ "0|3|
S2aS24S20S1fS20S2eS2eA2A1M0S1fS2dA1M1A2M2A1S4eS69S71A2S21G2S25G0G1S7cS7fA4A2A3").
Proof. vm_compute. reflexivity. Qed.
Definition s318 : wsub := Eval vm_compute in infer_sub NF T3r (K318 PG_P).
Lemma ent318 : ltac2:(tb__ "0|0|
S2aS1cS86S71S5S0A1S77A3S1dA3").
Proof. vm_compute. reflexivity. Qed.
Lemma id318 : ltac2:(tb__ "0|0|
S2aS1cS89S77S44A2S1dA3").
Proof. vm_compute. reflexivity. Qed.

Lemma n_is3 : ltac2:(tb__ "0|2|
S2fS34R1S3dS38S9bS14S30Z3M0A1A3A1A2S2aS97Q40M1A1S39R2PeA2S96G1G0A2A3F_;Frho;").
Proof.
  intros rho H. cbn [holds branch_taken eval] in H. unfold bv_eqb in H.
  apply Bool.not_true_iff_false in H. apply Bool.negb_false_iff in H. apply Z.eqb_eq in H.
  apply bv_eq. exact H.
Qed.

Lemma Forall_by_eqb : ltac2:(tb__ "0|1|
S2dOF_;S1fS2dA1M0G0S2aS1cS92S2dS2dS91S2dS41R1A1R3A3Lp;R1A3S1dA3S52S2dR4R3A3S52S2dR5R3A3F_;F_;FG;FF;FP;").
Proof.
  intros P F G Hb HF. apply Forall_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) Hb p Hp) as X. apply existsb_exists in X as (q & Hq & E).
  apply sprop_eqb_sound in E. subst q. exact (proj1 (Forall_forall _ _) HF p Hq).
Qed.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S55S2fS2fS1fS2dA1S32R4R3R2A3S2aS1cS92S2dS40R5A1R2A3S1dA3S52S2dS34R5A1M0R3A3S52S2dG0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))).
  exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Section ExitSc3.
  Variable ok : world -> Prop. Variable K : ltac2:(tb__ "0|0|
S1fS57A1S56OF_;F_;").
  Hypothesis Hok : ltac2:(tb__ "0|0|
S51S43Vok;VK;A3").
  Variable rho0 : valuation.
  Let G : ltac2:(tb__ "0|0|
S2fOFr;") := ltac2:(tb__ "0|0|
S2fS32S44Vrho0;R1A3Lr;").
  Variable Q : assn.

  Lemma exit_sc3 : ltac2:(tb__ "0|0|
S2fVG;R1A1S84S43Vok;S50S43VK;S62R2A4S85S2bS49S43VK;VG;S1S0A1R1A5VQ;R1A1A2Lw;A4F_;Frho;").
  Proof using Hok rho0.
    intros rho Hg.
    apply (triple_factsJ segs ok (liftK K) E3 rho). intros HF.
    assert (Hn3 : holds rho (SPNot (SPBranch BC_NE pN (SLit 3)))).
    { exact (proj1 (Forall_forall _ _) HF _ ltac:(left; reflexivity)). }
    eapply triple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. eapply (SP_restate segs K rho E3 E3r); [reflexivity | exact sd3 | | constructor | exact Hw].
      unfold d3. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is3 rho Hn3). vm_compute. reflexivity. }
    apply (call_sound segs ok K K E3r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s3 R3 P.Lib_tess__G1.Lib_tess_scale2d.Posts_sc _ rho efr3 chk3).
    - intros rho1. apply P.Lib_tess__G1.Lib_tess_scale2d.scale2d_sum. exact Hok.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s3 (ss_next P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc) P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E3r) R3) with (import_post s3 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E3r) R3). rewrite imp3.
      assert (HF' : Forall (holds rho') (ss_facts E3)).
      { eapply (Forall_holds_agree (ss_next E3r)); [exact Hag' | reflexivity | exact HF]. }
      assert (Hn3' : holds rho' (SPNot (SPBranch BC_NE pN (SLit 3)))).
      { exact (proj1 (Forall_forall _ _) HF' _ ltac:(left; reflexivity)). }
      eapply triple_conseq; [| intros w Hw; exact Hw |].
      { intros w Hw. eapply (SP_restate segs K rho' T3 T3r); [reflexivity | exact sd3r | | | exact Hw].
        - unfold d3r. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is3 rho' Hn3'). vm_compute. reflexivity.
        - eapply Forall_by_eqb; [|exact HF']. vm_compute. reflexivity. }
      apply (exit_reenter segs ok K G NF (pcuts PG_P) Q T3r (K318 PG_P) [] s318);
        [cbn; tauto | exact ent318 | exact id318 | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | reflexivity | intros; constructor |].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_le; [|exact Hag']. vm_compute; congruence.
  Qed.
End ExitSc3.

Definition E4 : sstate := E_sc4 PG_P.
Definition E4r : sstate := set_obj E4 6 (O_pp2d_lit 4).
Definition d4 := Eval vm_compute in match state_diff E4 E4r with Some (d, _) => d | None => [] end.
Lemma sd4 : ltac2:(tb__ "0|3|
S2aS24S20S1fS20S2eS2eA2A1M0S1fS2dA1M1A2M2A1S4eS63S60A2S21G2S25G0G1S7dS23S2dA1A4A2A3").
Proof. vm_compute. reflexivity. Qed.
Definition s4 : wsub := Eval vm_compute in infer_sub 10 E4r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc.
Definition R4 : list sobj := Eval vm_compute in match entails_fr E4r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s4 with Some R => R | None => [] end.
Lemma efr4 : ltac2:(tb__ "0|1|
S2aS24S1fS31A1M0A1S87S60S5cS6eA3S21G0S67A2A3").
Proof. vm_compute. reflexivity. Qed.
Lemma chk4 : ltac2:(tb__ "0|0|
S2aS1cS8fS60S5cS6eS67S5eA5S1dA3").
Proof. vm_compute. reflexivity. Qed.
Definition T4 : sstate := Eval vm_compute in import_post s4 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E4r) R4.
Lemma imp4 : ltac2:(tb__ "0|0|
S2aS2cS90S6eS44S5dS36S60A1S67A5S6aA3").
Proof. vm_compute. reflexivity. Qed.

Definition T4r : sstate := ltac2:(tb__ "0|0|
S4fS7aS6aU0S10A3S35S63A1A2").
Definition d4r := Eval vm_compute in match state_diff T4 T4r with Some (d, _) => d | None => [] end.
Definition nf4r := Eval vm_compute in match state_diff T4 T4r with Some (_, nf) => nf | None => [] end.
Lemma sd4r : ltac2:(tb__ "0|3|
S2aS24S20S1fS20S2eS2eA2A1M0S1fS2dA1M1A2M2A1S4eS6aS72A2S21G2S25G0G1S7eS80A4A2A3").
Proof. vm_compute. reflexivity. Qed.
Definition s418 : wsub := Eval vm_compute in infer_sub NF T4r (K34c PG_P).
Lemma ent34c : ltac2:(tb__ "0|0|
S2aS1cS86S72S6S0A1S79A3S1dA3").
Proof. vm_compute. reflexivity. Qed.
Lemma id418 : ltac2:(tb__ "0|0|
S2aS1cS89S79S44A2S1dA3").
Proof. vm_compute. reflexivity. Qed.

Lemma n_is4 : ltac2:(tb__ "0|2|
S2fS34R1S38S9aS14S30Z4M0A1A3A2S2aS97Q40M1A1S39R2PeA2S96G1G0A2A3F_;Frho;").
Proof.
  intros rho H. cbn [holds branch_taken eval] in H. unfold bv_eqb in H. apply Z.eqb_eq in H.
  apply bv_eq. exact H.
Qed.

Section ExitSc4.
  Variable ok : world -> Prop. Variable K : ltac2:(tb__ "0|0|
S1fS57A1S56OF_;F_;").
  Hypothesis Hok : ltac2:(tb__ "0|0|
S51S43Vok;VK;A3").
  Variable rho0 : valuation.
  Let G : ltac2:(tb__ "0|0|
S2fOFr;") := ltac2:(tb__ "0|0|
S2fS32S44Vrho0;R1A3Lr;").
  Variable Q : assn.

  Lemma exit_sc4 : ltac2:(tb__ "0|0|
S2fVG;R1A1S84S43Vok;S50S43VK;S63R2A4S85S2bS49S43VK;VG;S1S0A1R1A5VQ;R1A1A2Lw;A4F_;Frho;").
  Proof using Hok rho0.
    intros rho Hg.
    apply (triple_factsJ segs ok (liftK K) E4 rho). intros HF.
    assert (Hn4 : holds rho (SPBranch BC_EQ pN (SLit 4))).
    { exact (proj1 (Forall_forall _ _) HF _ ltac:(left; reflexivity)). }
    eapply triple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. eapply (SP_restate segs K rho E4 E4r); [reflexivity | exact sd4 | | constructor | exact Hw].
      unfold d4. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is4 rho Hn4). vm_compute. reflexivity. }
    apply (call_sound segs ok K K E4r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s4 R4 P.Lib_tess__G1.Lib_tess_scale2d.Posts_sc _ rho efr4 chk4).
    - intros rho1. apply P.Lib_tess__G1.Lib_tess_scale2d.scale2d_sum. exact Hok.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s4 (ss_next P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc) P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E4r) R4) with (import_post s4 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E4r) R4). rewrite imp4.
      assert (HF' : Forall (holds rho') (ss_facts E4)).
      { eapply (Forall_holds_agree (ss_next E4r)); [exact Hag' | reflexivity | exact HF]. }
      assert (Hn4' : holds rho' (SPBranch BC_EQ pN (SLit 4))).
      { exact (proj1 (Forall_forall _ _) HF' _ ltac:(left; reflexivity)). }
      eapply triple_conseq; [| intros w Hw; exact Hw |].
      { intros w Hw. eapply (SP_restate segs K rho' T4 T4r); [reflexivity | exact sd4r | | | exact Hw].
        - unfold d4r. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is4 rho' Hn4'). vm_compute. reflexivity.
        - eapply Forall_by_eqb; [|exact HF']. vm_compute. reflexivity. }
      apply (exit_reenter segs ok K G NF (pcuts PG_P) Q T4r (K34c PG_P) [] s418);
        [cbn; tauto | exact ent34c | exact id418 | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | reflexivity | intros; constructor |].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_le; [|exact Hag']. vm_compute; congruence.
  Qed.
End ExitSc4.

Definition E5 : sstate := E_r2 PG_P.
Definition E5a : sstate := Eval vm_compute in match split_obj_at E5 0 (SLit (-2232)) with Some X => X | None => E5 end.
Lemma sp5a : ltac2:(tb__ "0|0|
S2aS24S2cA1S94S64U0S30N8b8A1A3S21S2cS70A2A3"). Proof. vm_compute. reflexivity. Qed.
Definition E5b : sstate := Eval vm_compute in match split_obj_at E5a 1 (SLit (-2200)) with Some X => X | None => E5 end.
Lemma sp5b : ltac2:(tb__ "0|0|
S2aS24S2cA1S94S70U1S30N898A1A3S21S2cS65A2A3"). Proof. vm_compute. reflexivity. Qed.
Definition sel5 : list nat := ltac2:(tb__ "0|0|
S1bS1eU3S1bS1eU1S1bS1eU8S1bS1eU9S1bS1eUaS1bS1eUbS1bS1eU7S1bS1eU0S1bS1eU2S1bS1eU4S1bS1eU5S1bS1eU6S23S1eA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition E5c : sstate := Eval vm_compute in set_objs E5b (select (ss_objs E5b) sel5).
Lemma e5c : ltac2:(tb__ "0|0|
S2aS2cS8cS65S88S37S65A1S82A2A2S61A3"). Proof. vm_compute. reflexivity. Qed.
Definition wsub_del (ks : list positive) (s : wsub) : wsub := ltac2:(tb__ "0|2|
S9eS20S55S2eA2M0S8aSa0G0A1G0S9cS29S91S55S9dS28S55S2eR1A3A1Vks;A3A1M1A1Lp;G0S9fG1A1Lx;Vs;A6").
Definition s5 : wsub := Eval vm_compute in
  ([(15%positive, pSCR); (16%positive, pNXT); (17%positive, pPRV); (18%positive, pRFX); (19%positive, SVar 19)]
   ++ wsub_del [15;16;17;18;19]%positive (infer_sub 10 E5c (Pre_r2 R2_P))).
Definition R5 : list sobj := Eval vm_compute in match entails_fr E5c (Pre_r2 R2_P) s5 with Some R => R | None => [] end.
Lemma efr5 : ltac2:(tb__ "0|1|
S2aS24S1fS31A1M0A1S87S61S59S58A1S6fA3S21G0S68A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma chk5 : ltac2:(tb__ "0|0|
S2aS1cS8fS61S59S58A1S6fS68S5bS58A1A5S1dA3"). Proof. vm_compute. reflexivity. Qed.
Definition T5 : sstate := Eval vm_compute in import_post s5 NF (P_ret R2_P) (ss_next E5c) R5.
Lemma imp5 : ltac2:(tb__ "0|0|
S2aS2cS90S6fS44S5aS58A1S36S61A1S68A5S73A3"). Proof. vm_compute. reflexivity. Qed.
Definition T5a : sstate := Eval vm_compute in match rebase_obj_at T5 1 with Some X => X | None => T5 end.
Lemma rb5 : ltac2:(tb__ "0|0|
S2aS24S2cA1S95S73U1A2S21S2cS6bA2A3"). Proof. vm_compute. reflexivity. Qed.
Definition sel5b : list nat := ltac2:(tb__ "0|0|
S1bS1eU7S1bS1eU1S1bS1eU8S1bS1eU0S1bS1eU9S1bS1eUaS1bS1eUbS1bS1eU6S1bS1eU2S1bS1eU3S1bS1eU4S1bS1eU5S23S1eA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T5b : sstate := Eval vm_compute in set_objs T5a (select (ss_objs T5a) sel5b).
Lemma t5b : ltac2:(tb__ "0|0|
S2aS2cS8cS6bS88S37S6bA1S83A2A2S74A3"). Proof. vm_compute. reflexivity. Qed.
Definition T5c : sstate := Eval vm_compute in match merge_objs_at T5b 0 with Some X => X | None => T5b end.
Lemma mg5c : ltac2:(tb__ "0|0|
S2aS24S2cA1S93S74U0A2S21S2cS75A2A3"). Proof. vm_compute. reflexivity. Qed.
Definition T5d : sstate := Eval vm_compute in match merge_objs_at T5c 0 with Some X => X | None => T5c end.
Lemma mg5d : ltac2:(tb__ "0|0|
S2aS24S2cA1S93S75U0A2S21S2cS6cA2A3"). Proof. vm_compute. reflexivity. Qed.
Definition T5e : sstate := ltac2:(tb__ "0|0|
S4fS6cS35S64A1A2").
Definition nf5 := Eval vm_compute in match state_diff T5d T5e with Some (_, nf) => nf | None => [] end.
Lemma sd5 : ltac2:(tb__ "0|4|
S2aS24S20S1fS20S2eS2eA2M0A1M1S1fS2dA1M2A2M3A1S4eS6cS76A2S21G3S25G1G2S23G0A1S81A4A2A3"). Proof. vm_compute. reflexivity. Qed.
Definition s3dc : wsub := Eval vm_compute in infer_sub NF T5e (K3dc PG_P).
Lemma ent3dc : ltac2:(tb__ "0|0|
S2aS1cS86S76S7S0A1S78A3S1dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma id3dc : ltac2:(tb__ "0|0|
S2aS1cS89S78S44A2S1dA3"). Proof. vm_compute. reflexivity. Qed.

Lemma SP_smatch_step : ltac2:(tb__ "0|1|
S1fS57A1M0S56OF_;F_;S2fS2cS2cS20G0S98A2S3aS43R4R3R1A4S3aS43R5R3R2A4F_;S50S43R6R4R5R2A5S50S43R7R4R6R3A5F_;F_;Fw;FS';FS;Frho;FK;").
Proof. intros K rho S S' w H [Hsm Hk]. split; [apply H; exact Hsm | exact Hk]. Qed.

Ltac select_ok :=
  first [ vm_compute; reflexivity
        | intros i Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [cbn; lia|]); contradiction
        | intros i Hi; cbn in Hi; do 12 (destruct i as [|i]; [cbn; tauto|]); lia ].

Section ExitR2.
  Variable ok : world -> Prop. Variable K : ltac2:(tb__ "0|0|
S1fS57A1S56OF_;F_;").
  Hypothesis Hok : ltac2:(tb__ "0|0|
S51S43Vok;VK;A3").
  Variable rho0 : valuation.
  Let G : ltac2:(tb__ "0|0|
S2fOFr;") := ltac2:(tb__ "0|0|
S2fS32S44Vrho0;R1A3Lr;").
  Variable Q : assn.

  Lemma exit_r2 : ltac2:(tb__ "0|0|
S2fVG;R1A1S84S43Vok;S50S43VK;S64R2A4S85S2bS49S43VK;VG;S1S0A1R1A5VQ;R1A1A2Lw;A4F_;Frho;").
  Proof using Hok rho0.
    intros rho Hg.
    apply (triple_factsJ segs ok (liftK K) E5 rho). intros HF.
    eapply triple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. apply (SP_smatch_step K rho E5b E5c); [intros X; rewrite <- e5c; apply smatch_select; [exact X | select_ok | select_ok | select_ok] |].
      apply (SP_smatch_step K rho E5a E5b); [eapply smatch_split; exact sp5b |].
      apply (SP_smatch_step K rho E5 E5a); [eapply smatch_split; exact sp5a |]. exact Hw. }
    apply (call_sound segs ok K K E5c (Pre_r2 R2_P) s5 R5 (Posts_r2 R2_P) _ rho efr5 chk5).
    - intros rho1. apply run2d_sum. exact Hok.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s5 (ss_next (Pre_r2 R2_P)) (P_ret R2_P) (ss_next E5c) R5) with (import_post s5 NF (P_ret R2_P) (ss_next E5c) R5). rewrite imp5.
      assert (HF' : Forall (holds rho') (ss_facts E5)).
      { eapply (Forall_holds_agree (ss_next E5c)); [exact Hag' | reflexivity | exact HF]. }
      eapply triple_conseq; [| intros w Hw; exact Hw |].
      { intros w Hw.
        eapply (SP_restate segs K rho' T5d T5e); [reflexivity | exact sd5 | constructor | eapply Forall_by_eqb; [|exact HF']; vm_compute; reflexivity |].
        apply (SP_smatch_step K rho' T5c T5d); [eapply smatch_merge; exact mg5d |].
        apply (SP_smatch_step K rho' T5b T5c); [eapply smatch_merge; exact mg5c |].
        apply (SP_smatch_step K rho' T5a T5b); [intros X; rewrite <- t5b; apply smatch_select; [exact X | select_ok | select_ok | select_ok] |].
        apply (SP_smatch_step K rho' T5 T5a); [eapply smatch_rebase; exact rb5 |]. exact Hw. }
      apply (exit_reenter segs ok K G NF (pcuts PG_P) Q T5e (K3dc PG_P) [] s3dc);
        [cbn; tauto | exact ent3dc | exact id3dc | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | reflexivity | intros; constructor |].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_le; [|exact Hag']. vm_compute; congruence.
  Qed.
End ExitR2.
End Lib_tess_polygon_glue.

Module Lib_tess_polygon_chk2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.

Import ListNotations.
Close Scope bv_scope.

Lemma chk_pg_K34c : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S6S0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk2.

Module Lib_tess_polygon_ex_nodes.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.

Import ListNotations. Open Scope Z_scope.

Section N. Variable c : pg_consts.
Definition lcuts_pg : list lnode := ltac2:(tb__ "0|8|
S1bS45S46S13Vc;S23S2dA1A2Z14S23S20S48S2eA2M0A1M1A3S1bS45S46SdVc;A1Z13S1bG0S25S48S2eS4bS26A1M2S33P79A1A4G1A3A3S1bS45S46ScVc;A1Z12S1bG0S25S48S2eS4cS26A1S33P78A1A4G1A3A3S1bS45S46SeVc;A1Z11S1bG0S25S48S2eG2S33P7bA1A4M3G1A3M4A3S1bS45S46S18Vc;A1Z10M5S1bG0G3S1bG0S25S48S2eG2S30Z1A1A4G1A3A3A3S1bS45S46SfVc;A1ZfM6G4A3S1bS45S46SbVc;A1G6G4A3S1bS45S46S8Vc;A1ZeG1A3S1bS45S46S5Vc;A1ZcM7G1A3S1bS45S46S6Vc;A1G7G1A3S1bS45S46S7Vc;A1G7G1A3S1bS45S46S9Vc;A1ZbG1A3S1bS45S46SaVc;A1ZaG1A3S1bS45S46S19Vc;A1G5S1bG0G3S1bG0S25S48S2eG2S30Z0A1A4G1A3A3A3S23S45A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition lexits_pg : list lnode := ltac2:(tb__ "0|3|
S1bS45S46S11Vc;A1Z0M0S23S20S48S2eA2A1M1A3S1bS45S46S12Vc;A1G0G1A3S1bS45S46S16Vc;A1ZdM2G1A3S1bS45S46S17Vc;A1G2G1A3S1bS45S46S15Vc;A1G2G1A3S23S45A1A3A3A3A3A3").
Definition lnodes_pg : list lnode := lcuts_pg ++ lexits_pg.
End N.
End Lib_tess_polygon_ex_nodes.

Module Lib_tess_polygon_chk.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.

Import ListNotations.
Close Scope bv_scope.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk2.

Definition Posts_pg : list leaf := ltac2:(tb__ "0|0|
S1bS8bS8eS11S0A1S8dA2S1bS8bS8eS12S0A1S8dA2S23S8bA1A3A3").

Lemma pcuts_strict : ltac2:(tb__ "0|0|
S2aS1cS91S2cS42S1S0A1A3S26A3").
Proof. reflexivity. Qed.

Lemma chk_pg_Pre : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S13S0S23S2dA1A2A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_Kfin : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3SdS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_Kcm : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3ScS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_Knw : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3SeS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_Kproj : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3SfS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_Kbbp : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3SbS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_K29c : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S8S0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_K318 : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S5S0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_K3dc : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S7S0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_K4a : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3S9S0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_pg_K4b : ltac2:(tb__ "0|0|
S2aS1cS47S43S2S4S0A1S44S22S2cS1S0A1S3S0A1A3SaS0A1A6S1dA3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma forallb_lazy_cons_true {A} (f : A -> bool) (x : A) (l : list A) : ltac2:(tb__ "0|0|
S2aS1cVf;Vx;A1S1dA3S2aS1cS4aVA;Vf;Vl;A3S1dA3S2aS1cS4aVA;Vf;S1bVA;Vx;Vl;A3A3S1dA3F_;F_;").
Proof. intros H1 H2. cbn [forallb_lazy]. rewrite H1. exact H2. Qed.

Lemma check_pg : ltac2:(tb__ "0|0|
S2aS1cS4dS43S2S4S0A1S44S1S0A1S3S0A1A6S1dA3").
Proof.
  change (forallb_lazy (check_cut segs FUEL_pg (pg_cutpcs2 PG_P) NF (pcuts PG_P ++ pexits PG_P))
            [Pre_pg PG_P []; Kfin PG_P; Kcm PG_P; Knw PG_P; Kext PG_P; Kproj PG_P; Kbbp PG_P; K29c PG_P;
             K318 PG_P; K34c PG_P; K3dc PG_P; K4a PG_P; K4b PG_P; Klat PG_P] = true).
  apply forallb_lazy_cons_true; [exact chk_pg_Pre|].
  apply forallb_lazy_cons_true; [exact chk_pg_Kfin|].
  apply forallb_lazy_cons_true; [exact chk_pg_Kcm|].
  apply forallb_lazy_cons_true; [exact chk_pg_Knw|].
  apply forallb_lazy_cons_true; [exact chk_pg_Kext|].
  apply forallb_lazy_cons_true; [exact chk_pg_Kproj|].
  apply forallb_lazy_cons_true; [exact chk_pg_Kbbp|].
  apply forallb_lazy_cons_true; [exact chk_pg_K29c|].
  apply forallb_lazy_cons_true; [exact chk_pg_K318|].
  apply forallb_lazy_cons_true; [exact chk_pg_K34c|].
  apply forallb_lazy_cons_true; [exact chk_pg_K3dc|].
  apply forallb_lazy_cons_true; [exact chk_pg_K4a|].
  apply forallb_lazy_cons_true; [exact chk_pg_K4b|].
  apply forallb_lazy_cons_true; [exact chk_pg_Klat|].
  reflexivity.
Qed.
End Lib_tess_polygon_chk.
