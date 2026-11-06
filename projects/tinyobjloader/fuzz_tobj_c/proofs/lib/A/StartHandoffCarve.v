(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "pow"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rl"; "sv"; "smatch"; "soff"; "ss_objs"; "sstate"; "DList"; "cell"; "eval"; "mkObj"; "mkSS"; "obj_range"; "ranges_disjoint"; "rm"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "valuation"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "length"; "list"; "nil"; "Some"; "app"; "bool"; "cons"; "nat"; "option"; "pair"; "prod"; "true"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffCarve"; "list_objS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymFrame SymEntail SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition list_objS (base elo ehi : sv) (l : positive) : sobj := ltac2:(tb__ "0|0|
S12Vbase;Velo;Vehi;S23S10A1SfVl;A1A5").

Lemma smatch_carve_listS : ltac2:(tb__ "0|5|
S22S33A1S1fSeS2bS22S35A1S34A2SaSaSaS1S1SbR9R8R7R6A4S13S1bR8A1S1cR8A1S19R8A1S18R8A1S1dR8A1S25S8SdR8A1S27S8S36R6R5R4R3A4S23S8A1A3A3S17R8A1R2S1aR8A1A9SeS20S26S1eR1A1S2cA3S2fQ40M0S11RbR8A2A2S0ScRcR8A2S0ScRdR8A2S0S3R2R1A2S7S6R2R3A2S5Z2M1Z3fA2A2S3Z0M2S2R5R4A2A2S3S2R6R4A2S5G1Z40A2A2S20S0S4S21S2eQ8M3A1M4S9R12RcA2A2A1S6R5R6A2A3S31S8S8S15S14R14R1A2S2aS0S0S2R9R8A2S2R9R7A2A4A2Lo';SdR12A1A3S28S30R1S21G4S9R15RfA2A2A2S20S29G4A1S16R16S2dG0S2S2RbRaA2S4R2A1A2A2A2S24G4S32G4R2S9R16R10A2S2dG3G2A2A4A2A3F_;Fj;SbR16R15RcR13A4F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;TS';F_;Fnx;Fl;Fehi;Felo;Fbase;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S [tr [ms md]] base elo ehi l nx Hsm S' Hwf b lo hi Hs2 Hs3 Hlo Hhi Hlen Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  assert (Hmem : forall j, (j < length (rl rho l))%nat ->
            ms_mem ms (Z_to_bv 64 (b + lo + Z.of_nat j)) = Some (nth j (rl rho l) (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (Hbytes j Hj). apply Hfr.
    eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  assert (Hrange : obj_range rho (list_objS base elo ehi l) = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, list_objS. cbn [ob_base ob_lo ob_hi]. reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, list_objS. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b. fold lo. fold hi.
    split; [lia|]. split.
    { intros o Ho. unfold wview.
      replace (b + o) with (b + lo + Z.of_nat (Z.to_nat (o - lo))) by lia.
      rewrite (Hmem (Z.to_nat (o - lo))) by lia. discriminate. }
    split; [constructor|].
    split.
    { intros o Ho _. cbn [dflt_holds]. unfold rd, ms_read_byte.
      replace (b + o) with (b + lo + Z.of_nat (Z.to_nat (o - lo))) by lia.
      rewrite (Hmem (Z.to_nat (o - lo))) by lia. reflexivity. }
    cbn [dflt_inv]. exact Hlen.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite Hrange. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.
