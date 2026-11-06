(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia Logic.FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8 Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAM.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.

(* [comment removed for export] *)
Module StartNodes3E.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "ss_next"; "eval"; "rw"; "agree_below"; "rm"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "Some"; "app"; "bool"; "option"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "Model"; "vm_init_sp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_place_ok"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "LB_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3"; "null_rw_model"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section LazyNullRwE.

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Local Notation null_rw_model := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.null_rw_model lenZ) (only parsing).
Local Notation null_rw_h := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.null_rw_h lenZ) (only parsing).
Local Notation null_rw_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.null_rw_facts E lenZ) (only parsing).
Local Notation null_rw_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.null_rw_ok E lenZ nxt) (only parsing).

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S6S5VE;A1S7S2fA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1aS26A1S38S13SfS4VE;A1A1A2S17S26S27A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1Z11A2S7ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZaA2S7Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZbA2S7VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZcA2S7Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZdA2S7Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZeA2S7ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZfA2S7Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S39SaS4VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S19S30VGl;S4VE;A1A2S1bA3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S15S14S10Q40A1M0G0A2A1S1fS1dVm;A1A1S2bS13A1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S2eS18S14S10Q40A1M0G0A2S1fS1dVm;A1M1A1S1eG1A1A3S2dS2cA3").

Variable rho_of : ltac2:(tb__ "0|0|
S9S10Q40A1S9F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S9S10Q40A1SdSaS4VE;A1A1S37R2S36SeR2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S9S10Q40A1M0S0G0ScVrho_of;R2R1A2SaS4VE;A1A1A2R1A3Fa;Frho;").

Lemma n_valW : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Lemma place_ok_none_of : ltac2:(tb__ "0|3|
S10Q40M0A1M1S20G1G1S23S12G0Z0A2M2R4R3R2R1A5S22G2R4R3R2A4F_;Fa;Flen;Fmd;Fflags;").
Proof. intros flags md len a (P1 & P2 & P3 & P4 & _). unfold mmap_place_ok_none. repeat split; assumption. Qed.

Hypothesis Hwit : ltac2:(tb__ "0|2|
S1S10Q40M0A1M1G1S22S12G0Z0A2Vm;Vn;R1A4La;A2").

Theorem lazy_null_rw_enode : ltac2:(tb__ "0|5|
S9S15S10Q40M0A1M1A1S6S1cS2aS14S6S1cA2S16S6S1cR2R1A4VGl;A3S3S1G1G1S1G1G1S2S2aS14G1G1A2S16G1G1R2R1A4S1eS1dVm;A1M2A1A3S2S25S11G0R2A2M3S11G0SbR7R5A2A2M4A2S25S24G4R4A2S24G3S11G0R1A2A2A2A2A2Ls;A2Lb;A2S25S24S11G0SbR5R3A2A2R2A2S31VlenZ;A1A2A2F_;Fsz;Fe;S0S1cS11G0ScR3P1A2A2S11G0S21G2A1A2A3S34S13S29S13S28Vm;VB;A2VE;R4R3A5S35S1G1G1S2S22S12G0Z0A2Vm;Vn;R1A4S29S13S28S32VlenZ;Vm;R1A3VB;A2S33VE;VlenZ;Vnxt;A3Vrho_of;R6R1A2R5R2A6A2La;A2Lw;A3F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof n_valW as Nv. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  assert (Hshape : mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true).
  { apply mmap_modeled_b_intro_core; [rewrite G2; reflexivity | rewrite G3; apply mmap_flags_core_16418; reflexivity | rewrite G5; reflexivity]. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  destruct Hwit as [a Hwa].
  assert (Hpl : mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
  { rewrite G0, G1. destruct Hwa as (W1 & W2 & W3 & W4). unfold mmap_place_ok. rewrite Evm.
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
    unfold mmap_noreserve_backed_ok. rewrite G3, (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl). reflexivity. }
  exists ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a (mmap_n (ms_gpr ms 1)))) (mmap_rw_model (ms_gpr ms 3) md (ms_gpr ms 1) a)).
  split; [exact (wstep_mmap_intro_okA segsA ms md _ Hh H222 Hlen Hshape [] a Hp Hpl)|].
  exists a.
  rewrite G0, G1 in Hpl.
  assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
  assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
  assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
  { apply (place_ok_none_of (ms_gpr ms 3) m n a). unfold mmap_place_ok in Hpl |- *. rewrite Evm in Hpl.
    destruct Hpl as (P1 & P2 & P3 & P4 & P5). repeat split; try assumption.
    unfold mmap_noreserve_backed_ok in P5 |- *. rewrite G3 in P5 |- *. rewrite (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl) in P5 |- *. exact P5. }
  split; [exact Hplm|].
  pose proof Hplm as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree.
  pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Pfree)).
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
  unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ.
  set (rho' := rho_of rho a).
  split.
  * unfold null_rw_ok.
    assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                   ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a n)) (vm_add_lazy a n (with_vmmaps (null_rw_h md a) md)))).
    { eapply (smatchA_after_grant_lazy segsA rho rho' tp E [] ms md [] (null_rw_h md a)); try exact Hsp.
      -- reflexivity.
      -- reflexivity.
      -- reflexivity.
      -- exact Pal.
      -- rewrite Nv. exact Hnl.
      -- rewrite Nv. exact Hpos.
      -- rewrite Nv. unfold two_pow_64 in CL. lia.
      -- exact Hfree_m.
      -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
      -- intros o Ho. rewrite Nv.
         apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
         ++ lia.
         ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
         ++ intros x Hx. lia.
         ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
            pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
            unfold iv_overlap in R. rewrite Nv in R.
            apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
         ++ exact Ho.
      -- rewrite HX. intros rr y [] _.
      -- subst rho'. apply Hrho_ag.
      -- lia.
      -- cbn. apply Pos.ltb_lt. exact Hnxt.
      -- subst rho'. cbn [eval]. apply Hrho_at. }

    replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
    split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
    -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
       ++ unfold null_rw_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
          repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
          ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
          ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
          ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
       ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
    -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
    -- unfold shadow_ok. cbn. constructor.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (null_rw_model md a) tp <= B).
    { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3.null_rw_model. change (Z_to_bv 64 lenZ) with n. rewrite (paid_add_lazy (with_vmmaps (null_rw_h md a) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_rw_noreserve_le md (null_rw_h md a) a n (MI_ivs_wf segsA _ _ HMI)
                    Pal ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                    ltac:(rewrite Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
      lia. }
    assert (Hem' : erase_mat (null_rw_model md a) = erase_mat (null_rw_model m a)).
    { unfold null_rw_model, null_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNullRwE.
End StartNodes3E.

(* [comment removed for export] *)
Module Start4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "ss_facts"; "eval"; "rm"; "sprop_eqb"; "ss_objs"; "DZero"; "cell"; "mkObj"; "holds"; "sv_eqb"; "SPUle"; "SAlu"; "SPEq"; "ss_lenient"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "agree_below"; "sprop_below"; "sstate"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "pow"; "sub"; "land"; "eqb"; "testbit"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "pair"; "list"; "prod"; "true"; "app"; "option"; "false"; "andb"; "Some"; "fst"; "orb"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_init_sp"; "vm_maps"; "vm_reserved"; "alloc_top"; "Model"; "m_vm_lazy"; "vm_noaccess"; "vm_limit"; "event"; "lazy_interior"; "page_in_ranges"; "region_free"; "VmMaps"; "page_size"; "vm_backing_used"; "maps_subtract"; "vm_forget_range"; "with_vmmaps"; "mkVmMapsFull"; "vm_brk"; "vm_mmap_base"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "alloc_ceiling_hi"; "alloc_ceiling_lo"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.Seg4.WithP"; "m8"; "pRI"; "m9"; "n9"; "TP11"; "RI"; "Z11"; "B11"; "ZD11"; "priZ"; "G9"; "sbZ"; "pg"; "G8"; "Post4b"; "Post8a"; "m10"; "rho9"; "B12"; "clsZ"; "h8"; "m11"; "m8dead"; "q1Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "spacebeg"; "G4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.Seg4.WithP.S10.S11.S11m"; "C11"; "G11"; "G11c"; "tail11"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkLeafA"; "ax_setS"; "ax_X"; "ax_base"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.Seg4"; "n7"; "m7"; "m8"; "n9"; "sd8"; "Post4"; "m9"; "rho7"; "Post4b"; "m10"; "pair8_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "SHADOW_RW_LO_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.Seg4.WithP.S10"; "m10"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "E_k8x"; "L11m"; "L8m"; "E_k10"; "E_k11"; "M11"; "shRI_base"; "E_k12c"; "E_k12d"; "E_k8"; "E_k9"; "T2_11"; "ri30"; "shB6_base"; "F11m"; "M8"; "S_k11ok"; "S_k8ok"; "e_ri"; "e_rid"; "e_sb"; "fail_state"; "CLS11"; "F8m"; "F8x"; "T1_11"; "objShB6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.Seg4.WithP.S10.S11"; "m11"; "G10"; "bandav"; "clsZ"; "shpg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "agree_vars"; "objs_clear_e"; "RMH"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut";
"set_objs"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "NoDup"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States"; "E_k7"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "same_but_objs"; "state_diff"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "withX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "LB_of"; "eager_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"].
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
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition spacebeg (P : word) : word := ltac2:(tb__ "0|3|
S27Q40M0S30S2bS25G0VP;A2M1Z10000M2A2S2dG1G2A2A2A2").

Lemma testbit_high64 : ltac2:(tb__ "0|1|
S28S28S1S2aZ0R2A2S2cR2S2fZ2Z40M0A2A2A2S2aG0R2A2S0S36S33R4R3A2S3dA3F_;F_;Fk;Fx;").
Proof.
  intros x k Hx Hk. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
  apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_himask : ltac2:(tb__ "0|0|
S28S1S2aZ0R1A2S2cR1S2fZ2Z40A2A2A2S0S28S31R2Zfffffffffffff000A2S30R2S2dR2Z1000A2A2A3F_;Fx;").
Proof.
  intros x Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  rewrite E. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.ldiff_spec.
  replace (x - x mod 4096) with (x / 2 ^ 12 * 2 ^ 12) by (rewrite (Z.div_mod x (2^12)) at 2 by lia; change (2^12) with 4096; lia).
  rewrite Z.mul_pow2_bits by lia.
  destruct (Z.ltb_spec k 12) as [Hk12|Hk12].
  - rewrite (Z.ones_spec_low 12 k) by lia. rewrite (Z.testbit_neg_r _ (k - 12)) by lia. cbn. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.ones_spec_high 12 k) by lia. rewrite Z.div_pow2_bits by lia. replace (k - 12 + 12) with k by lia.
    destruct (Z.ltb_spec k 64) as [Hk64|Hk64].
    + rewrite (Z.ones_spec_low 64 k) by lia. cbn. rewrite andb_true_r. reflexivity.
    + rewrite (Z.ones_spec_high 64 k) by lia. rewrite (testbit_high64 x k) by lia. reflexivity.
Qed.
Lemma land_lomask16 : ltac2:(tb__ "0|0|
S28S2aZ0R1A2S0S28S31R2ZffffA2S2dR2Z10000A2A3F_;Fx;").
Proof. intros x Hx. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma restate8_evals : ltac2:(tb__ "0|5|
S6S0S26Q40M0A1M1S5R1P1eM2A2S7fS5R1P1dM3A2A1A3S0S28S2dS25G0S5R2G3A2A2Z1000A2Z0A3S2aS2bS25G0S5R3G3A2A2Z2000011000A2Z7fffff800000A2S1S0G1SdR4Sb5A2SdR4SbG2A1A2A3S1S0G1SdR4Sb3A2SdR4SadA2M4A3S0G1SdR4Sb4A2G4A3A2A2F_;F_;F_;Frho;").
Proof.
  intros rho H30 Hal Hceil. pose proof (bv_unsigned_in_range _ (rw rho 29%positive)) as R. change (bv_modulus 64) with (2^64) in R.
  set (P := bv_unsigned (rw rho 29%positive)) in *.
  pose proof (Z.mod_pos_bound P 65536 ltac:(lia)) as MB.
  assert (U30 : bv_unsigned (rw rho 30%positive) = P + 65536 - P mod 65536).
  { rewrite H30. unfold spacebeg. fold P. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  assert (E1 : eval rho e_sb = eval rho (SVar 30%positive)).
  { unfold e_sb. cbn [eval]. unfold alu64, alu. apply bv_eq.
    rewrite bv_sub_unsigned, bv_add_unsigned, bv_and_unsigned, !Z_to_bv_unsigned. fold P. rewrite U30.
    change (bv_wrap 64 65536) with 65536. change (bv_wrap 64 65535) with 65535.
    rewrite land_lomask16 by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small (P + 65536)) by lia. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : eval rho e_ri = eval rho ri30).
  { unfold e_ri, ri30. cbn [eval]. cbn [eval] in E1. rewrite E1. reflexivity. }
  split; [exact E1|]. split; [exact E2|].
  unfold e_rid. change (eval rho (SAlu ALU_AND e_ri (SLit 18446744073709547520))) with (alu64 ALU_AND (eval rho e_ri) (Z_to_bv 64 18446744073709547520)).
  rewrite E2. unfold ri30. cbn [eval]. unfold alu64, alu. apply bv_eq.
  rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned, U30.
  change (bv_wrap 64 18446744073709547520) with 18446744073709547520. change (bv_wrap 64 137438953472) with 137438953472.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (P + 65536 - P mod 65536 + 137438953472)) by lia.
  rewrite land_himask by lia.
  assert (Hm : (P + 65536 - P mod 65536 + 137438953472) mod 4096 = 0).
  { apply Z.mod_divide in Hal as [q Hq]; [|lia].
    assert (D : exists r, P mod 65536 = 4096 * r).
    { exists ((P mod 65536) / 4096). rewrite Hq. rewrite Z.mul_comm.
      replace 65536 with (4096 * 16) by reflexivity. rewrite Z.mul_mod_distr_l by lia.
      rewrite (Z.mul_comm 4096 (q mod 16)), Z.div_mul by lia. lia. }
    destruct D as [r Hr]. rewrite Hr, Hq.
    replace (q * 4096 + 65536 - 4096 * r + 137438953472) with ((q + 16 - r + 33554432) * 4096) by lia. apply Z_mod_mult. }
  lia.
Qed.

Lemma fact_of_state : ltac2:(tb__ "0|0|
S24SaS6S0S36Sc8SaSfR2A1ScR3A1A3S3aA3Sd0SaS14R2A1ScR4A1A3S14R3R4A2F_;F_;Frho;Ff;FS;").
Proof.
  intros S f rho Hb HF. apply existsb_exists in Hb as (g & Hin & He). apply sprop_eqb_sound in He. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

Lemma page_in_ranges_of_In : ltac2:(tb__ "0|5|
S26Q40M0A1M1G1G1S38S39G1G1A2M2A1Sc9G2S37G1G1R3R2A4R1A3S2aS25G0R4A2M3S25G0R5A2M4A2S2aS2bS25G0R6A2S55A2S2bG4G3A2A2S0S36S52R7R4A2S3aA3F_;F_;F_;Fl;Fs;Fb;Fp;").
Proof.
  intros p b s l Hin H1 H2. unfold page_in_ranges. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma paid_forget_le : ltac2:(tb__ "0|2|
S4cS54S28S28S38S26Q40A1M0A1SdcS4dR5A1A1ScbG0R2A2S2aSceS58R5R4S59R6R7A2A3M1R3A2S2bSceR7R3A2S30S56G1A1S56R7A1A2A2A2F_;F_;Ftp;Fhi;Flo;Fh;Fmd;").
Proof.
  intros md h lo hi tp Hwf Hnd. unfold paid.
  pose proof (unpaid_forget_le (with_vmmaps h md) lo hi tp ltac:(rewrite m_vm_lazy_with_vmmaps; exact Hwf) Hnd) as L.
  rewrite (unpaid_ext md (with_vmmaps h md) tp) in L by reflexivity.
  pose proof page_size_pos. nia.
Qed.

Lemma paid_cons_ge : ltac2:(tb__ "0|1|
S4cS26Q40A1M0S38G0A1S2aSceR3R1A2SceR3S34G0R2R1A3A2A2Ftp;Fp;Fmd;").
Proof.
  intros md p tp. unfold paid, unpaid. cbn [List.filter].
  destruct (page_in_ranges p (m_vm_lazy md) && negb (page_mem p (m_vm_materialized md))); cbn [length]; unfold page_size; lia.
Qed.
Lemma paid_app_ge : ltac2:(tb__ "0|2|
S4cS38S26Q40A1M0A1M1G1S2aSceR3R1A2SceR3S3bG0R2R1A3A2A2Ftp;Fl;Fmd;").
Proof.
  intros md l tp. induction l as [|p l IH]; cbn [app]; [lia|].
  etransitivity; [exact IH | apply paid_cons_ge].
Qed.

Lemma rw_of_agree_below : ltac2:(tb__ "0|0|
S29S6S6S29S22R4R3R2A3Se0R2R5A2S0S26Q40A1S5R4R3A2S5R5R3A2A3F_;F_;Fi;Frho';Frho;Fn;").
Proof. intros n rho rho' i (V & _ & _) Hi. symmetry. apply V. exact Hi. Qed.
Lemma agree_vars_trans : ltac2:(tb__ "0|1|
S29S29S29S6S6S6SdfR4R6A2SdfR5R6A2Sc1R8R5R4A3M0G0Sc1R8R7R5A3F_;F_;F_;F_;Frho3;Frho2;Frho1;Fk;Fm;Fn;").
Proof.
  intros n m k rho1 rho2 rho3 Hn Hm [A1 A2] [B1 B2]. split.
  - intros i Hi. rewrite (B1 i) by lia. apply A1. lia.
  - intros l. rewrite (B2 l). apply A2.
Qed.

Lemma lazy_interior_lit : ltac2:(tb__ "0|5|
S26Q40M0A1M1G1S0S28S2dS25G0R2A2Z1000A2Z0M2A3M3G3S2cG2S25G0R3A2A2S2aS2bS25G0R5A2S25G0R4A2A2S2fZ2Z40A2A2S0S38S39G1G1A2M4A1S51R6R5A2S34G4S37G1G1R6R5A4S35G4A1A3A3F_;F_;F_;F_;Fn;Fa;").
Proof.
  intros a n Ha Hn Hp He. pose proof (urange a) as Ua. pose proof (urange n) as Un. unfold lazy_interior, page_size.
  apply Z.mod_divide in Ha as [qa Hqa]; [|lia]. apply Z.mod_divide in Hn as [qn Hqn]; [|lia].
  rewrite Hqa, Hqn in *. replace (qa * 4096 + 4096 - 1) with (4095 + qa * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0.
  replace (qa * 4096 + qn * 4096) with ((qa + qn) * 4096) by lia. rewrite Z.div_mul by lia.
  destruct (Z.ltb_spec ((0 + qa) * 4096) ((qa + qn) * 4096)); [|exfalso; nia].
  f_equal. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned, Hqa. rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2^64). lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned, Hqn. rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2^64). lia.
Qed.

Definition G4 : list (sv * Z) := ltac2:(tb__ "0|1|
S34S39S7S28A2M0S37S7S28SbP1bA1Z10000A4S34G0S37S7S28SbP1cA1Z38e000A4S35G0A1A3A3").

Section Seg4.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S38S39S26Q40A1M0G0A2A1S4aS47Vm;A1A1Sd9S46A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S0S38S39S26Q40M0A1M1G1A2M2A1S49S47Vm;A1A1S34G2S37G1G1Va2;S27G0Z38e000A2A4S34G2S37G1G1Va1;S27G0Z10000A2A4S34G2S37G1G1S27G0Z2008fff7000A2S27G0Zdfff0001000A2A4S34G2S37G1G1S27G0Z8fff7000A2S27G0Z20000000000A2A4S34G2S37G1G1S27G0Z7fff7000A2S27G0Z10000000A2A4S35G2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S0S38S39S26Q40M0A1M1G1A2M2A1S4eS47Vm;A1A1S34G2S37G1G1S27G0Z8fff7000A2S27G0Z20000000000A2A4S35G2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S0S38S39S26Q40M0A1M1G1A2M2A1S4dVm;A1S3bG2S51S27G0Z2008fff7000A2S27G0Zdfff0001000A2A2S3bG2S51S27G0Z8fff7000A2S27G0Z20000000000A2A2S51S27G0Z7fff7000A2S27G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).

Hypothesis Ha1 : ltac2:(tb__ "0|2|
S1S2aZ646000S25Q40Va1;A2M0A2S1S3S2aS2bG0Z10000A2M1S9dA2S2aS9cG0A2A2S2aG1S4bS47Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S1S2aZ646000S25Q40Va2;A2M0A2S1S3S2aS2bG0Z38e000A2M1S9dA2S2aS9cG0A2A2S2aG1S4bS47Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S2aS2bVB;Z1000000A2S4fS47Vm;A1A1A2").

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S65S6S38S26Q40A1A1S38S50A1M0S4cR5R4R3R2R1A4S0G0R3S35S50A1A3F_;Fmd;Ftr;Ftp;Frho;S66S46Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S65S6S38S26Q40A1A1S38S50A1M0S4cR5R4R3R2R1A4S0G0R3S35S50A1A3F_;Fmd;Ftr;Ftp;Frho;SdeS46Vok;R2A3F_;FJ;").

Lemma OKFx : ltac2:(tb__ "0|0|
S4cS28S66S46Vok;S5eR2R1A2A3FBB;Fmm;").
Proof using OKF. clear Ha1 Ha2 HBlim Htop. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S4cS28SdeS46Vok;S5eR2R1A2A3FBB;Fmm;").
Proof using OKP. clear Ha1 Ha2 HBlim Htop. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma top_range : ltac2:(tb__ "0|1|
S1S2aS61S4bS47Vm;A1A1M0A2S2aG0S60A2A2").
Proof using Htop. clear Ha1 Ha2 HBlim. exact (alloc_top_bounds _ Htop). Qed.

Lemma Hband : ltac2:(tb__ "0|2|
S9eS3bS39S26Q40A1M0G0A2S4aS47Vm;A1M1A1S49G1A1A3S9dS9cA3").
Proof using Hmaps. clear Ha1 Ha2 HBlim Htop.
  apply (shadow_band_covered _ (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000)
           (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000)); try (vm_compute; reflexivity);
    apply in_app_iff; right; rewrite Hmaps; cbn [In]; tauto.
Qed.

Definition n7 : word := Z_to_bv 64 0x2000011000.
Definition m7 (P : word) : Model := null_none_model 0x2000011000 m P.
Definition rho7 (rho : valuation) (P : word) : valuation := ltac2:(tb__ "0|0|
ScdScdSd4Vrho;Sd3SeVrho;A1VP;S91A3A2P1dVP;A3P1eS7fVP;A1A3").

Lemma clear7 : ltac2:(tb__ "0|0|
S0S36Sc2S80S85ScfA1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma HG4 : ltac2:(tb__ "0|4|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S7S28Sc9S39S7S28A2S37S7S28R2R1A4S80A3S3S2G1G1S2G1G1S1Sc9S39G1G1A2S37G1G1R2R1A4S49S47Vm;A1A1A3S1S2aS25G0R2A2M2S25G0SdR8R5A2A2M3A2S2aS2bG3R4A2S2bG2S25G0R1A2A2A2A2A2Ls;A2Lb;A2S2aS2bS25G0SdR6R3A2A2R2A2Se3Z2000011000A1A2A2F_;Fsz;Fe;F_;F_;Frho;").
Proof using Hmaps. clear Ha1 Ha2 HBlim Htop.
  intros rho H27 H28 e sz [[= <- <-]|[[= <- <-]|[]]]; cbn [eval]; [rewrite H27|rewrite H28]; left; rewrite Hmaps.
  - exists a1, (Z_to_bv 64 0x10000). split; [cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - exists a2, (Z_to_bv 64 0x38e000). split; [cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma seg7 : ltac2:(tb__ "0|3|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0S28S25G0S5R3P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eVm;VB;A2ScfR4S35G1A1M2A5S8cS2G1G1S1S5fS27G0Z0A2Vm;S91R1A4S64S46S5eS92R1A1VB;A2P1fS98R6R1A2G2S34S86S87SaaSc6A2S35S86A1A3R2A7A2LP;A2Lw;A4F_;F_;F_;Frho;").
Proof using Hmaps Hres Htop OKF OKP. clear Ha1 Ha2 HBlim.
  intros rho H27 H28 Hv1.
  eapply triple_seq.
  { apply triple1_triple.
    apply (lazy_null_none_node ok OKF OKP E_k7 0x2000011000 m B G4 31%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear7.
    + exact Hres.
    + exact Htop.
    + exact Hband.
    + intros rho0 a. unfold rho7.
      assert (N : ss_next (ax_S E_k7) = 29%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      eapply agree_below_trans; [apply (agree_below_set_rw _ 29%positive a 29%positive); lia | apply (agree_below_set_rw _ 30%positive (spacebeg a) 29%positive); lia].
    + intros rho0 a. unfold rho7.
      assert (N : ss_next (ax_S E_k7) = 29%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      rewrite rho_set_rw_other by discriminate. apply rho_set_rw_at.
    + exact (HG4 rho H27 H28).
    + exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m B) (OKFx _ _) (fun n => stableA_KxA segsA n m B) _ SPIN7 200%nat SPIN_RAR);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run7_fail | exact spin7].
  - apply triple_ex; intros P. apply triple_pure; intros HPL.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists P; split; [exact HPL|exact Hw] |].
    apply triple1_triple.
    change (null_none_ok E_k7 0x2000011000 31) with S_k7ok.
    eapply sym_run_soundA; [exact run7_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Definition sd8 := Eval vm_compute in (match state_diff (ax_S E_k8) (ax_S E_k8x) with Some p => p | None => ([], []) end).
Lemma sd8_eq : ltac2:(tb__ "0|1|
S0S3cS39S38S39S7S7A2A1S38SaA1A2M0A1Sd6S85SaaA1S85Sa1A1A2S3fG0S95A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pair8_ok (p : sv * sv) : bool := ltac2:(tb__ "0|3|
S41S41S3eS15S40S7S7Vp;A3M0Sb4A2S15S42S7S7Vp;A3M1SadA2M2A2S3eS15G0Sb3A2G2A2A2S3eS15G0Sb5A2S15G1SbP1eA1A2A2A2").
Lemma sd8_shape : ltac2:(tb__ "0|3|
S1S0S36ScaS39S7S7A2M0S9bS40S38G0A1M1S38SaA1M2S95A3A3S3aA3S0G2S42G1G2S95A3Sb9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma swf8x : ltac2:(tb__ "0|0|
S0S36S21S85Sa1A1A1S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma restate8 : ltac2:(tb__ "0|3|
S26Q40M0A1M1S6S8cS0G1S5R2P1dA2R3A3S0G1S5R3P1eA2S7fR4A1A3S0S28S2dS25G0R5A2Z1000A2Z0A3S2aS9cS25G0R6A2A2S2aS2bS25G0R7A2Z2000011000A2Z7fffff800000A2S63S46S5eS92R8A1VB;A2SaaR7S35G1A1M2R6A6S63S46S5eS92R9A1VB;A2Sa1R8G2R7A6F_;F_;F_;F_;F_;F_;Fw;Frho;FP;").
Proof.
  clear. intros P rho w H29 H30 Hal HK Hceil Hsp.
  change E_k8x with (ax_setS E_k8 (ax_S E_k8x)).
  destruct sd8_shape as [Hd Hnf].
  eapply (SPA_restate segsA (KxA (m7 P) B) rho E_k8 (ax_S E_k8x) [] w (fst sd8) (snd sd8)).
  - exact swf8x.
  - rewrite sd8_eq. destruct sd8; reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - subst P. destruct (restate8_evals rho H30 Hal Hceil) as (E1 & E2 & E3).
    unfold diffs_ok. apply Forall_forall. intros pr Hin. pose proof (proj1 (forallb_forall _ _) Hd pr Hin) as Hp.
    unfold pair8_ok in Hp. apply Bool.orb_prop in Hp as [Hp|Hp]; [apply Bool.orb_prop in Hp as [Hp|Hp]|];
      apply andb_prop in Hp as [H1 H2]; apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; rewrite H1, H2; assumption.
  - rewrite Hnf. unfold F8x. unfold SHADOW_BAND_HI in HK.
    pose proof (bv_unsigned_in_range _ P) as R. change (bv_modulus 64) with (2^64) in R.
    pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
    assert (U30 : bv_unsigned (rw rho 30%positive) = bv_unsigned P + 65536 - bv_unsigned P mod 65536).
    { rewrite H30. unfold spacebeg. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?H29.
    + change (2 ^ 16) with 65536. split; [lia|]. rewrite U30.
      set (q := bv_unsigned P) in *. rewrite (Z.div_mod q 65536) at 1 by lia.
      replace (65536 * (q / 65536) + q mod 65536 + 65536 - q mod 65536) with ((q / 65536 + 1) * 65536) by lia.
      apply Z_mod_mult.
    + rewrite U30. lia.
    + unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned, U30. change (bv_wrap 64 65536) with 65536.
      unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small (bv_unsigned P + 65536) (2^64)) by lia. lia.
  - exact Hsp.
Qed.

Hypothesis Hfail8 : ltac2:(tb__ "0|0|
S4cS28S6S38S26Q40A1A1S8fS8eS46Vok;S63S46S5eR5R4A2Sb6Sa1A1R3R2A5R1A4FQ;Ftp;Frho;FBB;Fmm;").

Section WithP.
Variable P : word.
Hypothesis HPL : ltac2:(tb__ "0|0|
S5fS27Q40Z0A2Vm;S91VP;A4").
Let mP : Model := m7 P.

Definition RI : word := ltac2:(tb__ "0|1|
S27Q40M0S2bS25G0S7fVP;A1A2S2fZ2Z25A2A2A2").
Definition pg : word := Z_to_bv 64 4096.
Definition h8 : VmMaps := ltac2:(tb__ "0|0|
Se2S47VmP;A1S6cS73A3").
Definition m8 : Model := ltac2:(tb__ "0|1|
S58S25Q40S6cA2M0S2bG0Z1000A2S59S7bVmP;A2A3").
Definition m8dead : Model := mmap_fixed_dead_model mP RI pg.

Lemma mP_vmmaps : ltac2:(tb__ "0|4|
S0S54S47VmP;A1S5aS4aS47Vm;A1M0A1S34S39S26Q40A1M1G1A2M2S37G1G1VP;S91A4M3S49G0A1A3S34G2G3S4eG0A1A3S5dG0A1S5bG0A1S4fG0A1S5cG0A1S48G0A1A8A3").
Proof. unfold mP, m7, null_none_model, null_none_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps. reflexivity. Qed.
Lemma top_mP : ltac2:(tb__ "0|0|
S0S28S4bS47VmP;A1A1S4bS47Vm;A1A1A3").
Proof. unfold alloc_top. rewrite mP_vmmaps. reflexivity. Qed.

Lemma P_facts : ltac2:(tb__ "0|5|
S1S0S28S2dS25Q40M0VP;A2M1Z1000A2Z0A3S1S2aS2bG1Z2000011000A2S4bS47Vm;A1M2A1M3A2S1S0S36S53S3bS39S26G0A1M4G4A2S4aG2A1S49G2A1A3VP;S91A3S3aA3S1S2aS9cG1A2S2aG3S60A2A2A2A2A2").
Proof using HPL Hres Htop Hmaps. clear Ha1 Ha2 HBlim.
  pose proof HPL as (Pal & Ppos & Pceil & Pfree).
  assert (HnZ : mmap_nZ n7 = 0x2000011000) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite HnZ in Pceil.
  assert (Hn : mmap_n n7 = n7) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Pfree.
  pose proof (place_LB_A m 0x2000011000 P Htop Hres Hband ltac:(lia) ltac:(reflexivity) HPL) as (PLB & _ & _ & _ & Phi).
  split; [exact Pal|]. split; [exact Pceil|]. split; [exact Pfree|]. split; [exact PLB | exact Phi].
Qed.

Lemma SB_val : ltac2:(tb__ "0|3|
S0S28S25Q40M0S7fVP;A1A2S30S2bS25G0VP;A2M1Z10000M2A2S2dG1G2A2A2A3").
Proof using HPL Hres Htop Hmaps. clear Ha1 Ha2 HBlim.
  pose proof P_facts as (Pal & Pceil & _ & _ & Phi). unfold alloc_ceiling_hi in Phi. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
  unfold spacebeg. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange P). lia.
Qed.

Lemma RI_val : ltac2:(tb__ "0|1|
S0S28S25Q40M0S6cA2S2bS25G0S7fVP;A1A2S2fZ2Z25A2A2A3").
Proof using HPL Hres Htop Hmaps. clear Ha1 Ha2 HBlim.
  pose proof P_facts as (Pal & Pceil & _ & _ & Phi). unfold alloc_ceiling_hi in Phi. pose proof SB_val.
  pose proof (urange P). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
  unfold RI. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia.
Qed.

Lemma RI_range : ltac2:(tb__ "0|4|
S1S2aS2bS2bS25Q40M0VP;A2M1S2fZ2Z25A2A2Z1000M2A2S25G0S6cA2M3A2S1S2aS2bG3G2A2S2bG1Z2000011000A2A2S0S28S2dG3G2A2Z0A3A2A2").
Proof using HPL Hres Htop Hmaps. clear Ha1 Ha2 HBlim.
  pose proof P_facts as (Pal & Pceil & _). pose proof SB_val as SB. pose proof RI_val as RV. pose proof (urange P).
  pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
  assert (D : exists r, bv_unsigned P mod 65536 = 4096 * r /\ 0 <= r < 16).
  { pose proof Pal as Pal'. apply Z.mod_divide in Pal' as [q Hq]; [|lia]. exists ((bv_unsigned P mod 65536) / 4096). rewrite Hq.
    replace 65536 with (4096 * 16) by reflexivity. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia.
    rewrite (Z.mul_comm 4096 (q mod 16)), Z.div_mul by lia. pose proof (Z.mod_pos_bound q 16 ltac:(lia)). lia. }
  destruct D as (r & Hr & Hr16).
  split; [lia|]. split; [lia|].
  rewrite RV, SB, Hr. apply Z.mod_divide in Pal as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 4096 + 65536 - 4096 * r + 2 ^ 37) with ((q + 16 - r + 33554432) * 4096) by lia. apply Z_mod_mult.
Qed.

Lemma clear8 : ltac2:(tb__ "0|0|
S0S36Sc2S80S85Sa1A1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma a12_off_P : ltac2:(tb__ "0|5|
S1S3S2aS2bS25Q40M0Va1;A2M1Z10000A2S25G0VP;A2M2A2S2aS2bG2Z2000011000A2M3G1A2A2S3S2aS2bS25G0Va2;A2M4Z38e000A2G2A2S2aG3G4A2A2A2").
Proof using HPL Hres Htop Hmaps. clear Ha1 Ha2 HBlim.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  pose proof (region_free_In _ _ _ a2 (Z_to_bv 64 0x38e000) (region_free_app_r _ _ _ _ Pfree) ltac:(rewrite Hmaps; cbn [In]; tauto)) as Q2.
  pose proof (region_free_In _ _ _ a1 (Z_to_bv 64 0x10000) (region_free_app_r _ _ _ _ Pfree) ltac:(rewrite Hmaps; cbn [In]; tauto)) as Q1.
  unfold iv_overlap, n7 in Q1, Q2. rewrite !u64_of_lit in Q1, Q2 by lia.
  apply andb_false_iff in Q1; apply andb_false_iff in Q2.
  split; [destruct Q1 as [Q|Q]; apply Z.ltb_ge in Q; lia | destruct Q2 as [Q|Q]; apply Z.ltb_ge in Q; lia].
Qed.

Lemma node_s8 : ltac2:(tb__ "0|6|
S6S38S26Q40M0A1M1A1S0G1S5R2P1bA2Va1;A3S0G1S5R3P1cA2Va2;A3S0G1S5R4P1dA2VP;A3S0G1S5R5P1eA2S7fVP;A1A3S0S28S25G0S5R6P1A2A2S25G0S48S47Vm;A1A1A2A3S90S46Vok;S63S46S5eVmP;VB;A2M2Sa1R7R6A5S8cS3S63S46G2Sb6Sa1A1M3R8R7R1A6S3S63S46S5eS67S2bVB;Z1000M4A2A2Sb2R8R7R1A6S63S46S5eS7dVB;A2G3Sd4R8Sd3SeR8A1S6cS73A3A2Se5S25G0S6cA2M5S2bG5G4A2R7A3R1A6A2A2Lw;A4F_;F_;F_;F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp H27 H28 H29 H30 Hv1.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (alloc_top_lt (m_vmmaps m)) as CL. unfold two_pow_64 in CL.
  pose proof a12_off_P as [Q1 Q2].
  assert (Ptop : bv_unsigned P + 0x2000011000 <= bv_unsigned (rw rho 1%positive) - 0x800000).
  { revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil. }
  assert (Upg : bv_unsigned pg = 4096) by reflexivity.
  assert (Eri : eval rho ri30 = RI).
  { unfold ri30. cbn [eval]. rewrite H30. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. pose proof (urange P). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
    apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mP Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  assert (R17 : reg_sv (ax_S E_k8x) 17 = SLit 222) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R10 : reg_sv (ax_S E_k8x) 10 = ri30) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R11 : reg_sv (ax_S E_k8x) 11 = SLit 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R12 : reg_sv (ax_S E_k8x) 12 = SLit 3) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R13 : reg_sv (ax_S E_k8x) 13 = SLit 50) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R14 : reg_sv (ax_S E_k8x) 14 = SLit 18446744073709551615) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R15 : reg_sv (ax_S E_k8x) 15 = SLit 0) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E_k8x [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4r & G5).
  rewrite R10, Eri in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4r. rewrite R15 in G5.
  cbn [eval] in G1, G2, G3, G4r, G5. change (Z_to_bv 64 4096) with pg in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_50. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pg) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, top_mP; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact R3).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, mP_vmmaps. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear RI pg b s Hin). lia. }

  assert (Hothers : region_free (vm_maps (m_vmmaps m)) RI pg = true).
  { rewrite Hmaps. apply region_free_of_forall. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha1, Ha2.
    intros b s [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]; unfold iv_overlap; rewrite Upg; rewrite ?u64_of_lit by lia.
    - destruct Q2 as [Q|Q]; apply andb_false_iff; [left|right]; apply Z.ltb_ge; lia.
    - destruct Q1 as [Q|Q]; apply andb_false_iff; [left|right]; apply Z.ltb_ge; lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, mP_vmmaps. cbn [vm_maps].
    unfold map_contains. cbn [existsb fst snd]. unfold n7. rewrite (u64_of_lit 0x2000011000) by lia. rewrite Upg.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hobjs : forall o, In o (ss_objs (ax_S E_k8x)) -> ranges_disjoint (obj_range rho o) (bv_unsigned RI, bv_unsigned RI + 4096)).
  { intros o Ho.
    apply (objs_clear_e_sound rho G4 (ax_S E_k8x) RI 4096 (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) clear8);
      [lia| right; lia | intros x Hx; lia | |exact Ho].
    intros e sz [[= <- <-]|[[= <- <-]|[]]] x Hx; cbn [eval]; [rewrite H27|rewrite H28]; intros Hc; lia. }
  assert (OV : overlap_sum (vm_maps (m_vmmaps md)) (bv_unsigned RI) (bv_unsigned RI + 4096) <= 4096).
  { rewrite Evm, mP_vmmaps. cbn [vm_maps].
    match goal with |- overlap_sum (?r :: ?rest) _ _ <= _ => change (r :: rest) with ([] ++ r :: rest) end.
    replace (bv_unsigned RI + 4096) with (bv_unsigned RI + bv_unsigned pg) by (rewrite Upg; reflexivity).
    replace 4096 with (bv_unsigned pg) at 2 by exact Upg.
    apply overlap_sum_split_le. cbn [app]. exact Hothers. }
  split.
  - apply (OKP (KxA mP B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (fixed_rw_commit_only_okA segsA ms md _ H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont).
  - intros w' Hw.
    destruct (wstep_fixed_rw_commit_invA segsA ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] w' Hp Hw)
      as [-> | [[Hb ->] | ->]].
    +   left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (fail_state E_k8x) with (A_after E_k8x (SLit (bv_unsigned (errno_ret ENOMEM)))).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    +   right; left.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
      unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Enr, HnZ, G0, Upg.
      split.
      * change S_k8ok with (ax_setS E_k8x (S_after (ax_S E_k8x) ri30 (ss_objs (ax_S E_k8x) ++ [mkObj ri30 (SLit 0) (SLit (bv_unsigned pg)) [] DZero]) 31%positive)).
        eapply (smatchA_after_commit_obj segsA rho rho tp E_k8x [] ms md [] (mmap_fixed_rw_next (m_vmmaps md) RI pg) RI pg RI ri30 ri30 31%positive Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact R3.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. lia.
        -- rewrite Upg. lia.
        -- rewrite Upg. exact OV.
        -- unfold headroom. rewrite Evm, Upg, mP_vmmaps. cbn [vm_limit]. lia.
        -- intros x Hx. apply (grant_no_ro_A RI 4096); [intros z Hz; lia|]. rewrite Upg in Hx. exact Hx.
        -- rewrite Upg. exact Hobjs.
        -- intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- exact Eri.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- exact Eri.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold m8, h8. rewrite <- Evm. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3).
           pose proof (paid_forget_le md (mmap_fixed_rw_next (m_vmmaps md) RI pg) (bv_unsigned RI) (bv_unsigned RI + 4096) tp W3 (MI_nodupT segsA _ _ HMI)) as PF.
           pose proof (used_commit_le md (mmap_fixed_rw_next (m_vmmaps md) RI pg) RI pg (MI_ivs_wf segsA _ _ HMI) eq_refl eq_refl) as UC.
           rewrite Upg in UC. lia.
    +   right; right.
      unfold mmap_fixed_dead_model, with_mmap_destroyed. rewrite HnZ, G0, Upg.
      split.
      * change (fail_state E_k8x) with (ax_setS E_k8x (S_after (ax_S E_k8x) (SLit enomem_ret) (ss_objs (ax_S E_k8x)) (ss_next (ax_S E_k8x)))).
        eapply (smatchA_after_destroy segsA rho _ tp E_k8x [] ms md [] (mmap_fixed_dead_vm (m_vmmaps md) RI pg) RI pg _ (SLit enomem_ret) (ss_next (ax_S E_k8x)) Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact R3.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. lia.
        -- rewrite Upg. exact Hobjs.
        -- intros rr y [] _.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. unfold enomem_ret. apply Z_to_bv_bv_unsigned.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold m8dead, mmap_fixed_dead_model, with_mmap_destroyed. rewrite Upg. rewrite <- Evm. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3).
           unfold paid.
           pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_dead_vm (m_vmmaps md) RI pg) md) (bv_unsigned RI) (bv_unsigned RI + 4096)
                         (tp_forget (bv_unsigned RI) (bv_unsigned RI + 4096) tp) ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3)
                         ltac:(unfold tp_forget; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI))) as L.
           rewrite (unpaid_ext md (with_vmmaps _ md)) in L by reflexivity.
           pose proof (used_destroy_le md (mmap_fixed_dead_vm (m_vmmaps md) RI pg) (bv_unsigned RI) (bv_unsigned RI + 4096) (MI_ivs_wf segsA _ _ HMI) ltac:(lia)
                         ltac:(cbn; rewrite Upg; reflexivity) ltac:(cbn; rewrite Upg; reflexivity)) as UD.
           assert (LT : (length (unpaid md (tp_forget (bv_unsigned RI) (bv_unsigned RI + 4096) tp)) <= length (unpaid md tp))%nat).
           { unfold unpaid, tp_forget.
             apply List.NoDup_incl_length; [apply List.NoDup_filter; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI)|].
             intros p Hpin. apply List.filter_In in Hpin as [Hp1 Hp2]. apply List.filter_In in Hp1 as [Hp0 Hp1]. apply List.filter_In. split; [exact Hp0|exact Hp2]. }
           unfold paid in Hpaid. pose proof page_size_pos as PSP. first [ clear - Hpaid UD L LT PSP; nia | nia ].
Qed.

Lemma lazy_mP : ltac2:(tb__ "0|3|
S0S38S39S26Q40M0A1M1G1A2M2A1S4dVmP;A1S34G2S37G1G1VP;S91A4S34G2S37G1G1S27G0Z2008fff7000A2S27G0Zdfff0001000A2A4S34G2S37G1G1S27G0Z8fff7000A2S27G0Z20000000000A2A4S34G2S37G1G1S27G0Z7fff7000A2S27G0Z10000000A2A4S35G2A1A3A3A3A3A3").
Proof using HPL Hres Htop Hmaps Hlz. clear Ha1 Ha2 HBlim.
  pose proof P_facts as (Pal & Pceil & _ & _ & Phi). unfold alloc_ceiling_hi in Phi. pose proof (urange P) as UP.
  unfold mP, m7, null_none_model. rewrite m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps, Hlz.
  unfold n7. rewrite !lazy_interior_lit; try (rewrite ?u64_of_lit by lia; lia). reflexivity.
Qed.

Lemma lazy_m8 : ltac2:(tb__ "0|3|
S0S38S39S26Q40M0A1M1G1A2A1S4dS67A1S57S4dVmP;A1S25G0S6cA2M2S2bG2Z1000A2A3A3").
Proof. unfold m8. rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity. Qed.

Lemma m8_vmmaps : m_vmmaps m8 = h8.
Proof. unfold m8. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity. Qed.

Lemma m8_ledger : ltac2:(tb__ "0|8|
S1S0S38S39S26Q40M0A1M1G1A2M2A1M3S4aS47S67A1M4A1S4aS47Vm;A1M5A1A3S1S0G3S49G4A1S34G2S37G1G1VP;S91A4M6S49G5A1A3A3S1S0S28S4fG4A1S4fG5A1A3S1S0G1S48G4A1S48G5A1A3S0G3S4eG4A1S57S34G2G6S4eG5A1A3S25G0S6cA2M7S2bG7S25G0S73A2A2A3A3A2A2A2A2").
Proof.
  rewrite m8_vmmaps. unfold h8, mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess]. rewrite mP_vmmaps.
  cbn. repeat split; reflexivity.
Qed.
Lemma top_m8 : ltac2:(tb__ "0|0|
S0S28S4bS47S67A1A1S4bS47Vm;A1A1A3").
Proof. pose proof m8_ledger as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_m8 : init_sp_ok (m_vmmaps m8).
Proof using Htop. clear Ha1 Ha2 HBlim. pose proof m8_ledger as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m8 : ltac2:(tb__ "0|2|
S9eS3bS39S26Q40A1M0G0A2S4aS47S67A1M1A1S49G1A1A3S9dS9cA3").
Proof using Hmaps. clear Ha1 Ha2 HBlim Htop. pose proof m8_ledger as (L1 & L2 & _). rewrite L1, L2. apply (band_covered_after_grant m). exact Hband. Qed.

Lemma high_shadow_lazy_m8 : ltac2:(tb__ "0|1|
S26Q40M0A1S2aZ2008fff7000S25G0R1A2A2S2aS2bS25G0R2A2Z1000A2S9cA2S0S36S52R3S4dS67A1A2S3aA3F_;F_;Fp;").
Proof using HPL Hres Htop Hmaps Hlz. clear Ha1 Ha2 HBlim.
  intros p Hlo Hhi. pose proof RI_range as (R1 & R2 & R3). pose proof P_facts as (Pal & Pceil & _ & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  unfold SHADOW_BAND_HI in Hhi, PLB.
  rewrite lazy_m8, lazy_mP.
  destruct (iv_subtract_keeps (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) (bv_unsigned RI) (bv_unsigned RI + 4096)
              (bv_unsigned p) (bv_unsigned p + 4096)) as (r & Hr & Q1 & Q2).
  - unfold iv_wf, ivB, ivS. cbn [fst snd]. rewrite !u64_of_lit by lia. lia.
  - lia.
  - rewrite u64_of_lit by lia. lia.
  - rewrite !u64_of_lit by lia. lia.
  - lia.
  - left. lia.
  - destruct r as [b s0]. cbn [fst snd] in Q1, Q2. apply (page_in_ranges_of_In p b s0); [|exact Q1|unfold page_size; exact Q2].
    cbn [maps_subtract app]. rewrite !in_app_iff. right. left. exact Hr.
Qed.

Lemma low_shadow_lazy_m8 : ltac2:(tb__ "0|1|
S26Q40M0A1S2aS9dS25G0R1A2A2S2aS2bS25G0R2A2Z1000A2S9fA2S0S36S52R3S4dS67A1A2S3aA3F_;F_;Fp;").
Proof using HPL Hres Htop Hmaps Hlz. clear Ha1 Ha2 HBlim.
  intros p Hlo Hhi. pose proof RI_range as (R1 & R2 & R3). pose proof P_facts as (Pal & Pceil & _ & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  unfold SHADOW_BAND_LO, SHADOW_RW_LO_END, SHADOW_BAND_HI in Hlo, Hhi, PLB.
  rewrite lazy_m8, lazy_mP.
  destruct (iv_subtract_keeps (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) (bv_unsigned RI) (bv_unsigned RI + 4096)
              (bv_unsigned p) (bv_unsigned p + 4096)) as (r & Hr & Q1 & Q2).
  - unfold iv_wf, ivB, ivS. cbn [fst snd]. rewrite !u64_of_lit by lia. lia.
  - lia.
  - rewrite u64_of_lit by lia. lia.
  - rewrite !u64_of_lit by lia. lia.
  - lia.
  - left. lia.
  - destruct r as [b s0]. cbn [fst snd] in Q1, Q2. apply (page_in_ranges_of_In p b s0); [|exact Q1|unfold page_size; exact Q2].
    cbn [maps_subtract app]. rewrite !in_app_iff. right. right. right. left. exact Hr.
Qed.

Lemma shadow_acc_m8 : ltac2:(tb__ "0|0|
S28S3S1S2aZ2008fff7000R1A2S2cR1S9cA2A2S1S2aS9dR1A2S2cR1S9fA2A2A2S0S36SdbS4eS47S67A1A1R2A2S3dA3F_;Fz;").
Proof using HPL Hres Htop Hmaps Hlz Hna. clear Ha1 Ha2 HBlim.
  intros z Hz. pose proof RI_range as (R1 & R2 & R3). pose proof P_facts as (Pal & Pceil & _ & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  unfold SHADOW_BAND_LO, SHADOW_RW_LO_END, SHADOW_BAND_HI in Hz, PLB.
  pose proof m8_ledger as (_ & _ & _ & _ & L5). rewrite L5, Hna.
  destruct (maps_subtract_sem [(P, n7); (Z_to_bv 64 2415882240, Z_to_bv 64 2199023255552)] (bv_unsigned RI) (bv_unsigned RI + bv_unsigned pg)) as (_ & _ & Hc).
  - unfold n7. apply ivs_wf_cons; [|apply ivs_wf_cons; [|apply ivs_wf_nil]]; unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite !u64_of_lit by lia; lia.
  - pose proof (urange pg). lia.
  - rewrite Hc. apply andb_false_iff. left. unfold covered, n7. cbn [existsb]. unfold in_iv, ivB, ivS. cbn [fst snd].
    rewrite !u64_of_lit by lia. rewrite Bool.orb_false_r.
    apply Bool.orb_false_iff. destruct Hz as [Hz|Hz].
    + split; apply andb_false_iff; [left|right]; [apply Z.leb_gt; lia | apply Z.ltb_ge; lia].
    + split; apply andb_false_iff; [left|left]; apply Z.leb_gt; lia.
Qed.

Definition pRI (rho : valuation) : word := eval rho shRI_base.
Definition G8 : list (sv * Z) := ltac2:(tb__ "0|1|
S34S39S7S28A2M0S37S7S28SbP1bA1Z10000A4S34G0S37S7S28SbP1cA1Z38e000A4S34G0S37S7S28SadZ1000A4S35G0A1A3A3A3").
Lemma clearL8m : ltac2:(tb__ "0|0|
S0S36Sc2S74S85Sa3A1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L8m_facts31 : ltac2:(tb__ "0|2|
S1S0S36Sc8SaSfS18S17Sd2SbP1fA1M0S8Z3A1A3SbP1eA1A2A1ScS85Sa3A1A1M1A3S3aA3S0S36Sc8SaSfS16G0S8S30S2fZ2Z3dA2Z1A2A1A2A1G1A3S3aA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma same8m : ltac2:(tb__ "0|1|
S0S36Sd5S85Sa3A1M0Sc7G0S3bS9S10G0A1S34S9S13Sa7S8Z0A1S8S55A1S35S12A1S11A5S35S9A1A3A3A2A2S3aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma M8_eq : ltac2:(tb__ "0|1|
S0S8bSb0SddSc5Sc7S85Sa3A1M0S3bS9S10G0A1S34S9S13Sa7S8Z0A1S8S55A1S35S12A1S11A5S35S9A1A3A3A2A1S3bSaSb8ScG0A1A3A2A3").
Proof. reflexivity. Qed.

Lemma v31_val : ltac2:(tb__ "0|2|
S6Sd0SaS14R1A1ScS85Sa3A1A1A3S0S26Q40M0A1S5R2P1eA2S7fVP;A1M1A3S0S28S2eZ8S25G0S5R3P1fA2A2A2S25G0G1A2A3F_;F_;Frho;").
Proof using HPL. clear Ha1 Ha2 HBlim Htop.
  intros rho HF H30. destruct L8m_facts31 as [X1 X2].
  pose proof (fact_of_state _ _ rho X1 HF) as E1. pose proof (fact_of_state _ _ rho X2 HF) as E2.
  cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2.
  cbn [holds] in E1.
  apply (f_equal bv_unsigned) in E1. change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 31%positive) (SLit 3)))) with (U rho (g8 31%positive)) in E1.
  rewrite (U_g8 rho 31%positive) in E1 by (unfold U; cbn [eval]; exact E2).
  unfold U in E1. cbn [eval] in E1. rewrite H30 in E1. exact E1.
Qed.

Lemma prepay8 : ltac2:(tb__ "0|3|
S6S8cS0S26Q40M0A1M1S5R2P1bA2Va1;A3S0G1S5R3P1cA2Va2;A3S0G1S5R4P1dA2VP;A3S0G1S5R5P1eA2S7fVP;A1A3S0S28S25G0S5R6P1A2A2S25G0S48S47Vm;A1A1A2A3S63S46S5eS67S2bVB;Z1000A2A2Sa3R7S35G1A1M2R6A6S63S46S5eS67S2bVB;Z2000A2A2Sb0R8S34G1S68R8A1G2A3R7A6F_;F_;F_;F_;F_;F_;Fw;Frho;").
Proof using HBlim HPL Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho [tr [ms md]] H27 H28 H29 H30 Hv1 Hsp.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (alloc_top_lt (m_vmmaps m)) as CL. unfold two_pow_64 in CL.
  pose proof a12_off_P as [Q1 Q2]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha1, Ha2.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  pose proof (v31_val rho HF H30) as V31.
  pose proof (erase_mat_eq_fields md m8 Hem) as (Evm & Elz & _).
  assert (Up : bv_unsigned (pRI rho) = bv_unsigned (rw rho 31%positive) + 0x47fff8000).
  { unfold pRI, shRI_base. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
  assert (Hp_lo : 0x2008fff7000 <= bv_unsigned (pRI rho)) by lia.
  assert (Hp_hi : bv_unsigned (pRI rho) + 4096 <= 0x10007fff8000) by lia.
  assert (Hp_al : bv_unsigned (pRI rho) mod page_size = 0).
  { unfold page_size. rewrite Up.
    assert (D : exists k, bv_unsigned (spacebeg P) = 65536 * k).
    { exists ((bv_unsigned P) / 65536 + 1). rewrite SB. rewrite (Z.div_mod (bv_unsigned P) 65536) at 1 by lia. lia. }
    destruct D as [k Hk]. replace (bv_unsigned (rw rho 31%positive)) with (8192 * k) by lia.
    replace (8192 * k + 19327320064) with ((2 * k + 4718584) * 4096) by lia. apply Z_mod_mult. }
  rewrite M8_eq.
  set (J8 := fun (r : valuation) (tp' : list word) (tr0 : list event) (md0 : Model) => KxA m8 (B + 8192) r [pRI rho] tr0 md0).
  assert (Hsp' : SPA segsA J8 L8m rho [] (tr, mkCfg ms md)).
  { split; [exact Hsm|]. subst J8. cbv beta. unfold KxA. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hpaid |- *.
    split; [exact Htr|]. split; [exact Hem|].
    pose proof (paid_cons_le md (pRI rho) []) as PC. unfold page_size in PC. lia. }
  apply SPA_refacts.
  - unfold axA. change (mkAX (set_objs (ax_S L8m) (ss_objs (ax_S L8m) ++ [mkObj shRI_base (SLit 0) (SLit page_size) [] DZero])) [] (SLit SHB))
      with (ax_setS L8m (set_objs (ax_S L8m) (ss_objs (ax_S L8m) ++ [mkObj shRI_base (SLit 0) (SLit page_size) [] DZero]))).
    enough (X : SPA segsA J8 (ax_setS L8m (set_objs (ax_S L8m) (ss_objs (ax_S L8m) ++ [mkObj shRI_base (SLit 0) (SLit page_size) [] DZero]))) rho [pRI rho] (tr, mkCfg ms md)) by exact X.
    apply (SPA_prepay_zero_at segsA J8 rho L8m (pRI rho) shRI_base [] tr ms md).
    + exact Hsp'.
    + reflexivity.
    + exact Hp_al.
    + rewrite Elz. apply high_shadow_lazy_m8; unfold SHADOW_BAND_HI; lia.
    + intros [].
    + intros j Hj. rewrite Evm. apply shadow_acc_m8. left. unfold SHADOW_BAND_HI, page_size in *. lia.
    + unfold headroom. rewrite Evm. pose proof m8_ledger as (_ & _ & L3 & _). rewrite L3. unfold page_size. lia.
    + apply Forall_forall. intros o Ho. unfold page_size.
      apply (objs_clear_e_sound rho G8 (ax_S L8m) (pRI rho) 4096 HF clearL8m); [lia | | intros x Hx; lia | | exact Ho].
      { right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. lia. }
      intros e sz [[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]] x Hx; cbn [eval]; [rewrite H27 | rewrite H28 | ]; try lia.
      change (eval rho ri30) with (eval rho ri30). fold ri30.
      assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RI).
      { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
        change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
      rewrite Eri. lia.
    + exact same8m.
    + reflexivity.
    + intros X; exact X.
  - cbn [ax_S ax_setS set_objs ss_next]. rewrite forallb_app. apply andb_true_intro. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
    destruct Hsm as ((W & _) & _). cbn [ax_S] in W. exact (swf_facts _ W).
  - intros HF'. apply Forall_app. split; [|exact HF'].
    unfold F8m. constructor; [|constructor]. cbn [holds]. change (2 ^ 13) with 8192. split; [lia|].
    assert (D : exists k, bv_unsigned (spacebeg P) = 65536 * k).
    { exists ((bv_unsigned P) / 65536 + 1). rewrite SB. rewrite (Z.div_mod (bv_unsigned P) 65536) at 1 by lia. lia. }
    destruct D as [k Hk]. replace (bv_unsigned (rw rho 31%positive)) with (k * 8192) by lia. apply Z_mod_mult.
Qed.

Let Hfail8k : forall rho tp (Q : assn), triple segsA ok (SPA segsA (KxA mP B) (fail_state E_k8x) rho tp) Q := Hfail8 mP B.
Let Hfail8d : forall rho tp (Q : assn), triple segsA ok (SPA segsA (KxA m8dead B) (fail_state E_k8x) rho tp) Q := Hfail8 m8dead B.

Definition Post8a (rho : valuation) : assn := ltac2:(tb__ "0|3|
S8cS2S6S6S1Sc1P1fM0Vrho;R1A3S1Sc3Vrho;R1A2S1S0S28S2eZ8S25Q40M1S5R1G0A2A2A2S25G1S7fVP;A1A2A3S64S46S5eS67S2bVB;Z2000A2A2P20R1S34S26G1A1M2S68R1A1S35G2A1A3S34S86S87SabSc6A2S35S86A1A3R2A7A2A2A2Lrho1;A2Lw;").

Theorem seg8a : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1A3S0S28S25G0S5R5P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eVmP;VB;A2Sa1R6S35G1A1A5S76R6A1A4F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho H27 H28 H29 H30 Hv1.
  eapply triple_seq; [apply triple1_triple; apply (node_s8 rho [] H27 H28 H29 H30 Hv1)|].
  apply triple_disj; [apply Hfail8k|]. apply triple_disj; [|apply Hfail8d].

  eapply triple_conseq; [intros w Hw; exact (SPA_X0 (KxA m8 (B + 4096)) rho S_k8ok _ w eq_refl Hw) | intros w Hw; exact Hw |].
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact run8a | apply OKFx | reflexivity | apply stableA_KxA]. }
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros HinL. apply triple_pure; intros Hag.
  destruct HinL as [<-|[]]. cbn [la_state].
  assert (N : ss_next (ax_S (withX0 S_k8ok)) = 31%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N in Hag.
  destruct Hag as (V & Lq & Rm).
  assert (H27a : rw rho1 27%positive = a1) by (rewrite <- (V 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite <- (V 28%positive) by lia; exact H28).
  assert (H29a : rw rho1 29%positive = P) by (rewrite <- (V 29%positive) by lia; exact H29).
  assert (H30a : rw rho1 30%positive = spacebeg P) by (rewrite <- (V 30%positive) by lia; exact H30).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite <- (V 1%positive) by lia; exact Hv1).
  change (fun w => smatchA segsA rho1 [] L8mx w /\ KxA m8 (B + 4096) rho1 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m8 (B + 4096)) L8mx rho1 []).
  eapply triple_conseq; [intros w Hw; pose proof (SPA_noX (KxA m8 (B + 4096)) rho1 L8mx [] w Hw) as Hw'; rewrite L8m_eq in Hw'; exact Hw' | intros w Hw; exact Hw |].

  apply triple_factsA. intros HFL. pose proof (v31_val rho1 HFL H30a) as V31.
  eapply triple_conseq; [intros w Hw; exact (prepay8 rho1 w H27a H28a H29a H30a Hv1a Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run8b | apply OKFx | reflexivity | apply stableA_KxA]. }
  intros w Hw. exists rho1. split; [split; [intros i Hi; symmetry; apply V; exact Hi | intros l; symmetry; apply Lq]|].
  split; [intros a _; symmetry; apply Rm|]. split; [exact V31|].
  replace 32%positive with (ss_next (ax_S M8)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact Hw.
Qed.

Lemma paid_ge_used' : ltac2:(tb__ "0|0|
S4cS38S26Q40A1A1S2aS56R2A1SceR2R1A2A2Ftp;Fmd;").
Proof. clear. intros md tp. unfold paid. pose proof page_size_pos. nia. Qed.

Lemma enode_s8 : ltac2:(tb__ "0|2|
S6S38S26Q40M0A1M1A1S0G1S5R2P1bA2Va1;A3S0G1S5R3P1cA2Va2;A3S0G1S5R4P1dA2VP;A3S0G1S5R5P1eA2S7fVP;A1A3S0S28S25G0S5R6P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eVmP;VB;A2Sa1R7R6A5S8cS63S46S5eS67S2bVB;Z1000A2A2Sb2R8R7R1A6Lw;A3F_;F_;F_;F_;F_;Ftp;Frho;").
Proof using HBlim HPL Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho tp H27 H28 H29 H30 Hv1.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (alloc_top_lt (m_vmmaps m)) as CL. unfold two_pow_64 in CL.
  pose proof a12_off_P as [Q1 Q2].
  assert (Ptop : bv_unsigned P + 0x2000011000 <= bv_unsigned (rw rho 1%positive) - 0x800000).
  { revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil. }
  assert (Upg : bv_unsigned pg = 4096) by reflexivity.
  assert (Eri : eval rho ri30 = RI).
  { unfold ri30. cbn [eval]. rewrite H30. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. pose proof (urange P). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
    apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  apply etriple_ecall_detA; [apply stableA_KxA | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mP Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  assert (R17 : reg_sv (ax_S E_k8x) 17 = SLit 222) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R10 : reg_sv (ax_S E_k8x) 10 = ri30) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R11 : reg_sv (ax_S E_k8x) 11 = SLit 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R12 : reg_sv (ax_S E_k8x) 12 = SLit 3) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R13 : reg_sv (ax_S E_k8x) 13 = SLit 50) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R14 : reg_sv (ax_S E_k8x) 14 = SLit 18446744073709551615) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (R15 : reg_sv (ax_S E_k8x) 15 = SLit 0) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E_k8x [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4r & G5).
  rewrite R10, Eri in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4r. rewrite R15 in G5.
  cbn [eval] in G1, G2, G3, G4r, G5. change (Z_to_bv 64 4096) with pg in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_50. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pg) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, top_mP; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact R3).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, mP_vmmaps. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear RI pg b s Hin). lia. }
  assert (Hothers : region_free (vm_maps (m_vmmaps m)) RI pg = true).
  { rewrite Hmaps. apply region_free_of_forall. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha1, Ha2.
    intros b s [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]; unfold iv_overlap; rewrite Upg; rewrite ?u64_of_lit by lia.
    - destruct Q2 as [Q|Q]; apply andb_false_iff; [left|right]; apply Z.ltb_ge; lia.
    - destruct Q1 as [Q|Q]; apply andb_false_iff; [left|right]; apply Z.ltb_ge; lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - apply andb_false_iff. left. apply Z.ltb_ge. lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, mP_vmmaps. cbn [vm_maps].
    unfold map_contains. cbn [existsb fst snd]. unfold n7. rewrite (u64_of_lit 0x2000011000) by lia. rewrite Upg.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hobjs : forall o, In o (ss_objs (ax_S E_k8x)) -> ranges_disjoint (obj_range rho o) (bv_unsigned RI, bv_unsigned RI + 4096)).
  { intros o Ho.
    apply (objs_clear_e_sound rho G4 (ax_S E_k8x) RI 4096 (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) clear8);
      [lia| right; lia | intros x Hx; lia | |exact Ho].
    intros e sz [[= <- <-]|[[= <- <-]|[]]] x Hx; cbn [eval]; [rewrite H27|rewrite H28]; intros Hc; lia. }
  assert (OV : overlap_sum (vm_maps (m_vmmaps md)) (bv_unsigned RI) (bv_unsigned RI + 4096) <= 4096).
  { rewrite Evm, mP_vmmaps. cbn [vm_maps].
    match goal with |- overlap_sum (?r :: ?rest) _ _ <= _ => change (r :: rest) with ([] ++ r :: rest) end.
    replace (bv_unsigned RI + 4096) with (bv_unsigned RI + bv_unsigned pg) by (rewrite Upg; reflexivity).
    replace 4096 with (bv_unsigned pg) at 2 by exact Upg.
    apply overlap_sum_split_le. cbn [app]. exact Hothers. }

  pose proof (MI_ivs_wf segsA _ _ HMI) as (W1 & W2 & W3).
  pose proof (used_commit_le md (mmap_fixed_rw_next (m_vmmaps md) RI pg) RI pg (MI_ivs_wf segsA _ _ HMI) eq_refl eq_refl) as UC0.
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
  assert (Hbud : mmap_fixed_rw_budget_ok (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { unfold mmap_fixed_rw_budget_ok, with_mmap_replacement, with_mmap_backing, vm_backing_within_limit. rewrite Enr, HnZ, G0, Upg.
    rewrite Upg in UC0. apply Z.leb_le. pose proof (paid_ge_used' md tp) as PU.
    match goal with |- _ <= ?l => replace l with (vm_limit (m_vmmaps m))
      by (rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps; cbn [mmap_fixed_rw_next vm_limit]; rewrite Evm, mP_vmmaps; reflexivity) end.
    lia. }
  exists ([], mkCfg (after_sys_mem ms (ms_gpr ms 0) (zero_range (ms_mem ms) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))
                    (mmap_fixed_rw_ok_model (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))).
  split.
  { apply (wstep_fixed_rw_commit_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] Hp Hbud). }
  unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Enr, HnZ, G0, Upg.
  split.
  * change S_k8ok with (ax_setS E_k8x (S_after (ax_S E_k8x) ri30 (ss_objs (ax_S E_k8x) ++ [mkObj ri30 (SLit 0) (SLit (bv_unsigned pg)) [] DZero]) 31%positive)).
    eapply (smatchA_after_commit_obj segsA rho rho tp E_k8x [] ms md [] (mmap_fixed_rw_next (m_vmmaps md) RI pg) RI pg RI ri30 ri30 31%positive Hsp).
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- exact R3.
    -- rewrite Upg. reflexivity.
    -- rewrite Upg. lia.
    -- rewrite Upg. lia.
    -- rewrite Upg. exact OV.
    -- unfold headroom. rewrite Evm, Upg, mP_vmmaps. cbn [vm_limit]. lia.
    -- intros x Hx. apply (grant_no_ro_A RI 4096); [intros z Hz; lia|]. rewrite Upg in Hx. exact Hx.
    -- rewrite Upg. exact Hobjs.
    -- intros rr y [] _.
    -- apply agree_below_refl.
    -- apply Pos.le_refl.
    -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    -- exact Eri.
    -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    -- exact Eri.
  * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
    -- unfold m8, h8. rewrite <- Evm. apply erase_mat_cong_forget. exact Hem.
    -- pose proof (paid_forget_le md (mmap_fixed_rw_next (m_vmmaps md) RI pg) (bv_unsigned RI) (bv_unsigned RI + 4096) tp W3 (MI_nodupT segsA _ _ HMI)) as PF.
       rewrite Upg in UC0. lia.
Qed.

Theorem eseg8a : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1A3S0S28S25G0S5R5P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eVmP;VB;A2Sa1R6S35G1A1A5S76R6A1A3F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho H27 H28 H29 H30 Hv1.
  eapply etriple_seq; [apply (enode_s8 rho [] H27 H28 H29 H30 Hv1)|].
  eapply etriple_conseq; [intros w Hw; exact (SPA_X0 (KxA m8 (B + 4096)) rho S_k8ok _ w eq_refl Hw) | intros w Hw; exact Hw |].
  eapply etriple_seq.
  { eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run8a]. }
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag.
  destruct HinL as [<-|[]]. cbn [la_state].
  assert (N : ss_next (ax_S (withX0 S_k8ok)) = 31%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N in Hag.
  destruct Hag as (V & Lq & Rm).
  assert (H27a : rw rho1 27%positive = a1) by (rewrite <- (V 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite <- (V 28%positive) by lia; exact H28).
  assert (H29a : rw rho1 29%positive = P) by (rewrite <- (V 29%positive) by lia; exact H29).
  assert (H30a : rw rho1 30%positive = spacebeg P) by (rewrite <- (V 30%positive) by lia; exact H30).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite <- (V 1%positive) by lia; exact Hv1).
  change (fun w => smatchA segsA rho1 [] L8mx w /\ KxA m8 (B + 4096) rho1 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA m8 (B + 4096)) L8mx rho1 []).
  eapply etriple_conseq; [intros w Hw; pose proof (SPA_noX (KxA m8 (B + 4096)) rho1 L8mx [] w Hw) as Hw'; rewrite L8m_eq in Hw'; exact Hw' | intros w Hw; exact Hw |].
  apply etriple_factsA. intros HFL. pose proof (v31_val rho1 HFL H30a) as V31.
  eapply etriple_conseq; [intros w Hw; exact (prepay8 rho1 w H27a H28a H29a H30a Hv1a Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run8b]. }
  intros w Hw. exists rho1. split; [split; [intros i Hi; symmetry; apply V; exact Hi | intros l; symmetry; apply Lq]|].
  split; [intros a _; symmetry; apply Rm|]. split; [exact V31|].
  replace 32%positive with (ss_next (ax_S M8)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact Hw.
Qed.

Definition G9 : list (sv * Z) := ltac2:(tb__ "0|1|
S3bS39S7S28A2M0S74S34G0S37S7S28Sa7Z1000A4S35G0A1A3A3").
Definition m9 (b4 : word) : Model := null_none_model 0x800000 m8 b4.
Definition n9 : word := Z_to_bv 64 0x800000.
Definition rho9 (rho : valuation) (b4 : word) : valuation := ltac2:(tb__ "0|0|
ScdSd4Vrho;Sd3SeVrho;A1Vb4;S6aA3A2P20Vb4;A3").

Lemma clear9 : ltac2:(tb__ "0|0|
S0S36Sc2S71S85SabA1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma HG9 : ltac2:(tb__ "0|7|
S6S28S0S26Q40M0A1M1S5R2P1bA2Va1;A3S0G1S5R3P1cA2Va2;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S38S39G1G1A2M3A1M4S2G4G4S0G4R2S3bG3R1S49S47S67A1A1A3A3Ll;A2S7S28Sc9S39S7S28A2S37S7S28R2R1A4S71A3S3S2G1G1S2G1G1S1Sc9G3S37G1G1R2R1A4R7A3S1S2aS25G0R2A2M5S25G0SdRdR5A2A2M6A2S2aS2bG6R4A2S2bG5S25G0R1A2A2A2A2A2Ls;A2Lb;A2S2aS2bS25G0SdRbR3A2A2R2A2RaA2A2F_;Fsz;Fe;F_;Fmaps;F_;F_;F_;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho LB H27 H28 H30 H31 maps [l ->] e sz Hin.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof m8_ledger as (_ & L2 & _). rewrite L2, Hmaps. left.
  unfold G9, G8 in Hin. cbn [app] in Hin.
  destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; cbn [eval].
  - rewrite H27. exists a1, (Z_to_bv 64 0x10000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - rewrite H28. exists a2, (Z_to_bv 64 0x38e000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  -   exists P, n7. split; [apply in_app_iff; right; cbn [In]; tauto|].
    assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RI).
    { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    change (eval rho ri30) with (eval rho ri30). fold ri30. rewrite Eri. unfold n7. rewrite u64_of_lit by lia. lia.
  -
    exists (Z_to_bv 64 0x2008fff7000), (Z_to_bv 64 0xdfff0001000). split; [apply in_app_iff; right; cbn [In]; tauto|].
    change (eval rho shRI_base) with (pRI rho).
    assert (Up : bv_unsigned (pRI rho) = bv_unsigned (rw rho 31%positive) + 0x47fff8000).
    { unfold pRI, shRI_base. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
    rewrite !u64_of_lit by lia. lia.
Qed.

Lemma seg9 : ltac2:(tb__ "0|5|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0S28S25G0S5R6P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eS67S2bVB;Z2000A2M3A2SabR7S34G1S68R7A1S35G1A1M4A3A5S8cS2G1G1S1S5fS27G0Z0A2S67S6aR1A4S64S46S5eS69R1A1G3A2P21S78R9R1A2S34G1S68R9A1G4A3S34S86S87Sa4Sc6A2S35S86A1A3R2A7A2Lb4;A2Lw;A4F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho H27 H28 H29 H30 H31 Hv1. pose proof m8_ledger as (L1 & L2 & L3 & L4 & L5).
  eapply triple_seq.
  { apply triple1_triple.
    apply (lazy_null_none_node ok OKF OKP E_k9 0x800000 m8 (B + 8192) G9 33%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear9.
    + rewrite L1. exact Hres.
    + exact init_sp_ok_m8.
    + exact band_m8.
    + intros rho0 a. unfold rho9.
      assert (N : ss_next (ax_S E_k9) = 32%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      apply (agree_below_set_rw _ 32%positive a 32%positive). lia.
    + intros rho0 a. unfold rho9.
      assert (N : ss_next (ax_S E_k9) = 32%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N. apply rho_set_rw_at.
    + apply (HG9 rho _ H27 H28 H30 H31). exists []. reflexivity.
    + rewrite L4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m8 (B + 8192)) (OKFx _ _) (fun n => stableA_KxA segsA n m8 (B + 8192)) _ SPIN9 200%nat SPIN_RAR);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run9_fail | exact spin9].
  - apply triple_ex; intros b4. apply triple_pure; intros HPL4.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b4; split; [exact HPL4|exact Hw] |].
    apply triple1_triple.
    change (null_none_ok E_k9 0x800000 33) with S_k9ok.
    eapply sym_run_soundA; [exact run9_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Definition B11 : Z := B + 8192 + 4096 + 65536.
Definition sbZ (rho : valuation) : Z := bv_unsigned (rw rho 35%positive) + 0x7fff8000.
Definition priZ (rho : valuation) : Z := bv_unsigned (rw rho 31%positive) + 0x47fff8000.
Definition q1Z (rho : valuation) : Z := ltac2:(tb__ "0|1|
S30S72Vrho;A1M0S2dG0Z1000A2A2").
Definition TP11 (rho : valuation) : list word := ltac2:(tb__ "0|7|
S36S38S26Q40M0A1M1A1L_;S32S7eVrho;A1M2S70Vrho;A1M3A2S34G1S27G0S2bG3Z2000M4A2A2S34G1S27G0S2bG3Z1000M5A2A2S34G1S68Vrho;A1S35G1A1A3M6A3A3S34G1S27G0S2bG2G4A2A2S34G1S27G0S2bG2G5A2A2S34G1S27G0G2A2G6A3A3A3X36x2").

Lemma TP11_agree : ltac2:(tb__ "0|0|
S6S6Sc1P24R2R1A3S0S38S26Q40A1A1S6bR2A1S6bR3A1A3F_;Frho';Frho;").
Proof.
  clear. intros rho rho' [A1 _]. unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base. cbn [eval].
  rewrite (A1 35%positive), (A1 31%positive) by lia. reflexivity.
Qed.
Lemma priZ_ext : ltac2:(tb__ "0|1|
S6S6S0S26Q40A1S5R1P1fM0A2S5R2G0A2A3S0S28S70R2A1S70R3A1A3F_;Frho';Frho;").
Proof. clear. intros rho rho' H. unfold priZ. rewrite H. reflexivity. Qed.
Lemma sbZ_ext : ltac2:(tb__ "0|1|
S6S6S0S26Q40A1S5R1P23M0A2S5R2G0A2A3S0S28S72R2A1S72R3A1A3F_;Frho';Frho;").
Proof. clear. intros rho rho' H. unfold sbZ. rewrite H. reflexivity. Qed.

Definition Z11 (rho : valuation) : Prop := ltac2:(tb__ "0|7|
S28S26Q40M0A1M1Sc9G1R1S6bVrho;A1A3S1S2aS25G0R2A2M2R3A2S2cR3S2bG2Z1000A2A2A2S2cR4S2fZ2Z40A2A2S4S1S2aS70Vrho;A1M3R5A2S2cR5S2bG3Z200A2A2A2A1S4S1S2aS72Vrho;A1M4R6A2S2cR6S2bG4Z2000A2A2A2A1S0S3cS26Q8M5A1M6A1SeVrho;S27G0R7A2A2S3fG6S27G5Z0A2A2A3F_;F_;F_;F_;F_;Fp;Fa;").
Lemma Z11_ext : ltac2:(tb__ "0|4|
S6S6S0S26Q40A1M0S5R1P1fM1A2S5R2G1A2A3S0G0S5R2P23M2A2S5R3G2A2A3G0S0S3cS26Q8A1A1SeR4R1A2SeR5R1A2A3Fa;S6dR5A1M3G3F_;F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H31 H35 Hrm HZ a p Hp Ha H64 N1 N2. rewrite Hrm.
  assert (ET : TP11 rho' = TP11 rho) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite H31, H35; reflexivity).
  unfold priZ, sbZ in *. rewrite H31 in N1. rewrite H35 in N2. rewrite ET in Hp. exact (HZ a p Hp Ha H64 N1 N2).
Qed.

Definition ZD11 (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S28S26Q40M0A1M1Sc9G1R1S6bVrho;A1A3S1S2aS25G0R2A2M2R3A2S2cR3S2bG2Z1000A2A2A2S2cR4S2fZ2Z40A2A2S4S1S2aS70Vrho;A1M3R5A2S2cR5S2bG3Z200A2A2A2A1S4S0S3cS26Q8A1M4A1SeVrho;S27G0R6A2A2S43G4A1A3A1F_;F_;F_;F_;Fp;Fa;").
Lemma ZD11_ext : ltac2:(tb__ "0|4|
S6S6S0S26Q40A1M0S5R1P1fM1A2S5R2G1A2A3S0G0S5R2P23M2A2S5R3G2A2A3G0S0S3cS26Q8A1A1SeR4R1A2SeR5R1A2A3Fa;S6fR5A1M3G3F_;F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H31 H35 Hrm HZ a p Hp Ha H64 N1. rewrite Hrm.
  assert (ET : TP11 rho' = TP11 rho) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite H31, H35; reflexivity).
  unfold priZ in *. rewrite H31 in N1. rewrite ET in Hp. exact (HZ a p Hp Ha H64 N1).
Qed.

Section S10.
Variable b4 : word.
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S5fS27Q40Z0A2S67S6aVb4;A4").

Lemma m9_ledger : ltac2:(tb__ "0|6|
S1S0S38S39S26Q40A1M0G0A2M1A1M2S4aS47S69Vb4;A1A1M3A1S4aS47Vm;A1M4A1A3S1S0G2S49G3A1S34G1S37G0G0Vb4;S6aA4M5S34G1S37G0G0VP;S91A4S49G4A1A3A3A3S1S0S28S4fG3A1S4fG4A1A3S1S0G0S48G3A1S48G4A1A3S0G2S4eG3A1S34G1G5S4eS47S67A1A1A3A3A2A2A2A2").
Proof.
  clear. pose proof m8_ledger as (L1 & L2 & L3 & L4 & L5).
  unfold m9, null_none_model, null_none_h. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess].
  rewrite L1, L2, L3, L4. repeat split; reflexivity.
Qed.
Lemma top_m9 : ltac2:(tb__ "0|0|
S0S28S4bS47S69Vb4;A1A1A1S4bS47Vm;A1A1A3").
Proof. clear. pose proof m9_ledger as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_m9 : init_sp_ok (m_vmmaps (m9 b4)).
Proof using Htop. clear -Htop. pose proof m9_ledger as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m9 : ltac2:(tb__ "0|2|
S9eS3bS39S26Q40A1M0G0A2S4aS47S69Vb4;A1A1M1A1S49G1A1A3S9dS9cA3").
Proof using Hmaps. clear -Hmaps. pose proof m9_ledger as (L1 & L2 & _). pose proof m8_ledger as (K1 & K2 & _).
  rewrite L1, L2, <- K1, <- K2. apply (band_covered_after_grant m8). exact band_m8. Qed.

Lemma b4_facts : ltac2:(tb__ "0|5|
S1S2aZ646000S25Q40M0Vb4;A2M1A2S1S3S2aS2bG1Z800000A2M2S9dA2S2aS9cG1A2A2S1S2aG2S4bS47Vm;A1A1A2S1S0S28S2dG1Z1000A2Z0A3S0S36S53S3bS39S26G0A1M3G3A2S4aS47S67A1M4A1S49G4A1A3Vb4;S6aA3S3aA3A2A2A2A2").
Proof using HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m8_ledger as (L1 & L2 & L3 & L4 & L5).
  pose proof (place_LB_A m8 0x800000 b4 init_sp_ok_m8 ltac:(rewrite L1; exact Hres) band_m8 ltac:(lia) ltac:(reflexivity) HPL4) as (PLB & _ & Pband & Ptop & _).
  pose proof HPL4 as (Hal & _ & _ & Hfree). rewrite top_m8 in Ptop.
  assert (Hn : mmap_n n9 = n9) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 0x800000) with 0x646000 in PLB. repeat split; assumption.
Qed.

Definition m10 (b5 : word) : Model := eager_model 4096 (m9 b4) b5.
Lemma clear10 : ltac2:(tb__ "0|0|
S0S36Sc2S71S85Sa4A1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg10 : ltac2:(tb__ "0|7|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0G1S5R6P20A2Vb4;A3S0S28S25G0S5R7P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eS69Vb4;A1M3S2bVB;Z2000A2M4A2Sa4R8S34G1S68R8A1S35G1A1M5A3A5S8cS2G1G1S1S5fS27G0Z0A2G3S27G0Z1000M6A2R1A4S64S46S5eSa0R1A1S2bG4G6A2A2P22ScdRaP21R1A3S34G1S68RaA1G5A3S34S86S87Sa5Sc6A2S35S86A1A3R2A7A2Lb5;A2Lw;A4F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho H27 H28 H29 H30 H31 H32 Hv1. pose proof m9_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_k10 4096 (m9 b4) (B + 8192) G9 34%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear10.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m9.
    + exact band_m9.
    + rewrite M3. lia.
    + apply (HG9 rho _ H27 H28 H30 H31). rewrite M2. exists [(b4, n9)]. pose proof m8_ledger as (_ & K2 & _). rewrite K2. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m9 b4) (B + 8192)) (OKFx _ _) (fun n => stableA_KxA segsA n (m9 b4) (B + 8192)) _ SPIN10 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run10_fail | exact spin10].
  - apply triple_ex; intros b5. apply triple_pure; intros HPL5.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b5; split; [exact HPL5|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_k10) = 33%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_k10 4096 34) with S_k10ok. rewrite N.
    eapply sym_run_soundA; [exact run10_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Section S11.
Variable b5 : word.
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S5fS27Q40M0Z0A2S69Vb4;A1S27G0Z1000A2Vb5;A4").

Lemma m10_ledger : ltac2:(tb__ "0|7|
S1S0S38S39S26Q40M0A1M1G1A2M2A1M3S4aS47Sa0Vb5;A1A1M4A1S4aS47Vm;A1M5A1A3S1S0G3S49G4A1S34G2S37G1G1Vb5;S27G0Z1000A2A4S34G2S37G1G1Vb4;S6aA4M6S34G2S37G1G1VP;S91A4S49G5A1A3A3A3A3S1S0S28S4fG4A1S4fG5A1A3S1S0G1S48G4A1S48G5A1A3S0G3S4eG4A1S34G2G6S4eS47S67A1A1A3A3A2A2A2A2").
Proof.
  clear. pose proof m9_ledger as (L1 & L2 & L3 & L4 & L5).
  unfold m10, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess].
  rewrite L1, L2, L3, L4, L5. repeat split; reflexivity.
Qed.
Lemma top_m10 : ltac2:(tb__ "0|0|
S0S28S4bS47Sa0Vb5;A1A1A1S4bS47Vm;A1A1A3").
Proof. clear. pose proof m10_ledger as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_m10 : ltac2:(tb__ "0|0|
S62S47Sa0Vb5;A1A1A1").
Proof using Htop. clear -Htop. pose proof m10_ledger as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m10 : ltac2:(tb__ "0|2|
S9eS3bS39S26Q40A1M0G0A2S4aS47Sa0Vb5;A1A1M1A1S49G1A1A3S9dS9cA3").
Proof using Hmaps. clear -Hmaps b4. pose proof m10_ledger as (L1 & L2 & _). pose proof m9_ledger as (K1 & K2 & _).
  rewrite L1, L2, <- K1, <- K2. apply (band_covered_after_grant (m9 b4)). exact band_m9. Qed.

Lemma b5_facts : ltac2:(tb__ "0|6|
S1S2aZ1000M0S25Q40M1Vb5;A2M2A2S1S3S2aS2bG2G0A2M3Z10000A2S2aZ646000G2A2A2S1S3S2aG3S9dA2S2aS9cG2A2A2S1S2aG3S4bS47Vm;A1A1A2S1S0S28S2dG2G0A2Z0A3S0S36S53S3bS39S26G1A1M4G4A2S4aS47S69Vb4;A1A1M5A1S49G5A1A3Vb5;S27G1G0A2A3S3aA3A2A2A2A2A2").
Proof using HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m9_ledger as (L1 & L2 & L3 & L4 & L5).
  pose proof (place_LB_A (m9 b4) 4096 b5 init_sp_ok_m9 ltac:(rewrite L1; exact Hres) band_m9 ltac:(lia) ltac:(reflexivity) HPL5) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL5 as (Hal & _ & _ & Hfree). rewrite top_m9 in Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. repeat split; assumption.
Qed.

Definition m11 (b6 : word) : Model := ltac2:(tb__ "0|0|
Se4Z10000Sa0Vb5;A1Vb6;A3").
Definition G10 : list (sv * Z) := ltac2:(tb__ "0|1|
S3bS39S7S28A2M0S71S34G0S37S7S28SbP21A1Z1000A4S35G0A1A3A3").
Lemma clear11 : ltac2:(tb__ "0|0|
S0S36Sc2SbdS85Sa5A1A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg11a : ltac2:(tb__ "0|7|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0G1S5R6P20A2Vb4;A3S0G1S5R7P21A2Vb5;A3S0S28S25G0S5R8P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eSa0Vb5;A1M3S2bS2bVB;Z2000A2Z1000A2M4A2Sa5R9S34G1S68R9A1S35G1A1M5A3A5S8cS2G1G1S1S5fS27G0Z0A2G3S27G0Z10000M6A2R1A4S63S46S5eSbcR1A1S2bG4G6A2A2SdaSb1A1ScdRbP22R1A3S34G1S68RbA1G5A3R2A6A2Lb6;A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho H27 H28 H29 H30 H31 H32 H33 Hv1. pose proof m10_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_k11 65536 (m10 b5) (B + 8192 + 4096) G10 35%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear11.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m10.
    + exact band_m10.
    + rewrite M3. lia.
    + intros e sz Hin. unfold G10 in Hin. apply in_app_iff in Hin as [Hin|[[= <- <-]|[]]].
      * apply (HG9 rho _ H27 H28 H30 H31); [|exact Hin]. rewrite M2. exists [(b5, Z_to_bv 64 4096); (b4, n9)].
        pose proof m8_ledger as (_ & K2 & _). rewrite K2. reflexivity.
      * left. cbn [eval]. rewrite H33. exists b5, (Z_to_bv 64 4096). split; [rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m10 b5) (B + 8192 + 4096)) (OKFx _ _) (fun n => stableA_KxA segsA n (m10 b5) (B + 8192 + 4096)) _ SPIN11 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run11_fail | exact spin11].
  - apply triple_ex; intros b6. apply triple_pure; intros HPL6.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b6; split; [exact HPL6|exact Hw] |].
    assert (N : ss_next (ax_S E_k11) = 34%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_k11 65536 35) with S_k11ok. rewrite N.
    eapply triple_conseq; [intros w Hw; exact (SPA_X0 (KxA (m11 b6) (B + 8192 + 4096 + 65536)) _ S_k11ok _ w eq_refl Hw) | intros w Hw; exact Hw |].
    apply triple_refl.
Qed.

Definition bandav (a len : Z) : Prop := ltac2:(tb__ "0|0|
S3S2aS2bVa;Vlen;A2Z7fff7000A2S2aZ10007fff8000Va;A2A2").
Lemma bandav_intro : ltac2:(tb__ "0|0|
S28S28S3S2aS2bR2R1A2S9dA2S2aS9cR2A2A2SbeR3R2A2F_;Flen;Fa;").
Proof. clear. intros a len H. exact H. Qed.

Lemma b6_facts : ltac2:(tb__ "0|8|
S26Q40M0A1M1S5fS27G0Z0M2A2Sa0Vb5;A1M3S27G0Z10000M4A2M5R1A4S1S2aZ646000S25G0R2A2M6A2S1SbeG6G4A2S1S2aS2bG6G4A2S4bS47Vm;A1A1A2S1S0S28S2dG6Z1000A2G2A3S0S36S53S3bS39G1G1A2S4aS47G3A1M7A1S49G7A1A3R2G5A3S3aA3A2A2A2A2F_;Fb6;").
Proof using HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros b6 HPL6. pose proof m10_ledger as (L1 & L2 & L3 & L4 & L5).
  pose proof (place_LB_A (m10 b5) 65536 b6 init_sp_ok_m10 ltac:(rewrite L1; exact Hres) band_m10 ltac:(lia) ltac:(reflexivity) HPL6) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL6 as (Hal & _ & _ & Hfree). rewrite top_m10 in Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 65536) = Z_to_bv 64 65536) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 65536) with 0x646000 in PLB. split; [exact PLB|]. split; [exact Pband|]. repeat split; assumption.
Qed.

Definition clsZ (hi : bool) (b6 : word) : Prop := ltac2:(tb__ "0|1|
S36OLhi;Vhi;S2aS9cS25Q40Vb6;A2M0A2S2aS2bG0Z10000A2S9dA2X36x2").

Lemma CLS11_holds : ltac2:(tb__ "0|1|
S36S26Q40A1M0S6S0G0S5R1P22A2R2A3SbfR4R3A2S14R3Sb7R5A1A2F_;F_;Frho;Fb6;Fhi;").
Proof.
  clear. intros hi b6 rho H34 Hc. unfold clsZ in Hc. unfold SHADOW_BAND_HI, SHADOW_BAND_LO in Hc.
  destruct hi; cbn [CLS11 holds eval]; rewrite H34, u64_of_lit by lia; lia.
Qed.

Definition shpg (q : Z) : Prop := ltac2:(tb__ "0|1|
S3S1S2aZ2008fff7000Vq;A2S2aS2bVq;Z1000A2M0Z10007fff8000A2A2S1S2aZ7fff7000Vq;A2S2aG0Z8fff7000A2A2A2").
Definition clswin (q : Z) : Prop := ltac2:(tb__ "0|1|
S3S1S2aZ2008fff7000Vq;A2S2aS2bVq;Z3000A2M0Z10007fff8000A2A2S1S2aZ7fff7000Vq;A2S2aG0Z8fff7000A2A2A2").

Section S11m.
Variables (b6 : word) (hi : bool).
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S5fS27Q40M0Z0A2Sa0Vb5;A1S27G0Z10000A2Vb6;A4").
Hypothesis Hcls : clsZ hi b6.

Definition G11 : list (sv * Z) := ltac2:(tb__ "0|1|
S3bS39S7S28A2M0SbdS34G0S37S7S28SbP22A1Z10000A4S35G0A1A3A3").

Definition G11c : list (sv * Z) := ltac2:(tb__ "0|3|
S34S39S7S28A2M0S37S7S28SbP1bA1Z10000M1A4S34G0S37S7S28SbP1cA1Z38e000A4S34G0S37S7S28SadZ1000M2A4S34G0S37S7S28Sa7Z200A4S34G0S37S7S28SbP21A1G2A4S34G0S37S7S28SbP22A1G1A4S35G0A1A3A3A3A3A3A3").
Definition tail11 : sobj := ltac2:(tb__ "0|0|
S13Sa7S8Z200A1S8Z1000A1S35S12A1S11A5").
Definition C11 : sstate := ltac2:(tb__ "0|1|
Sc7SacVhi;A1M0Sd1S9U10S10G0A1A3A2").

Lemma L11m_X : ltac2:(tb__ "0|2|
S1S0S38S39S7S7A2M0A1S89Sa2Vhi;A1M1A1S35G0A1A3S0S7S8aG1A1S8Sc4A1A3A2").
Proof. clear. destruct hi; split; reflexivity. Qed.
Lemma L11m_len : ltac2:(tb__ "0|2|
S1S0S45S44S9S10S85Sa2Vhi;A1A1M0A1A2U10A3S1S0S29S1dSacVhi;A1M1A1P24A3S0S38SaA1ScG1A1ScG0A1A3A2A2").
Proof. clear. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma T2_objs : ltac2:(tb__ "0|1|
S0S38S9A1S10SacVhi;A1A1M0S3bS9Sd1S9U10G0A3S34S9S84S35S9A1A3A3A3").
Proof. clear. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma clear_T2 : ltac2:(tb__ "0|0|
S0S36Sc2S82SacVhi;A1A2S3aA3"). Proof. clear. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma clear_C11 : ltac2:(tb__ "0|0|
S0S36Sc2S83S81A2S3aA3"). Proof. clear. unfold C11. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma carve_swf : ltac2:(tb__ "0|0|
S0S36S21S1aS1eS81A1S1fS81A1S1cS81A1S1bS81A1S20S81A1S3bS9S10S81A1S34S9S13SaeS8Z0A1S8Z2000A1S35S12A1S11A5S35S9A1A3A3ScS81A1P24S19S81A1A9A1S3aA3").
Proof. clear. unfold C11. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma carve_below : ltac2:(tb__ "0|0|
S0S36ScaSaS23P24A1S3bSaSafScS81A1A3A3S3aA3").
Proof. clear. unfold C11. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma carve_M11 : ltac2:(tb__ "0|1|
S0S8bSddS88S88S88Sa2Vhi;A1SbaVhi;A1A2S81A2S1aS1eS81A1S1fS81A1S1cS81A1S1bS81A1S20S81A1S3bS9S10S81A1S34S9S13SaeS8Z0A1S8Z2000A1S35S12A1S11A5S35S9A1A3A3ScS81A1M0P24S19S81A1A9A2S3bSaSafG0A3A2Sa6Vhi;A1A3").
Proof. clear. unfold C11. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L11m_facts35 : ltac2:(tb__ "0|2|
S1S0S36Sc8SaSfS18S17Sd2SbP23A1M0S8Z3A1A3SbP22A1A2A1ScS85Sa2Vhi;A1A1A1M1A3S3aA3S0S36Sc8SaSfS16G0S8S30S2fZ2Z3dA2Z1A2A1A2A1G1A3S3aA3A2").
Proof. clear. destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma v35_val : ltac2:(tb__ "0|2|
S6Sd0SaS14R1A1ScS85Sa2Vhi;A1A1A1A3S0S26Q40M0A1S5R2P22A2Vb6;A3S1S0S28S2eZ8S25G0S5R3P23A2A2M1A2S25G0Vb6;A2A3S2aG1S30S2fZ2Z3dA2Z1A2A2A2F_;F_;Frho;").
Proof.
  clear. intros rho HF H34. destruct L11m_facts35 as [X1 X2].
  pose proof (fact_of_state _ _ rho X1 HF) as E1. pose proof (fact_of_state _ _ rho X2 HF) as E2.
  cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2.
  cbn [holds] in E1.
  apply (f_equal bv_unsigned) in E1. change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (U rho (g8 35%positive)) in E1.
  rewrite (U_g8 rho 35%positive) in E1 by (unfold U; cbn [eval]; exact E2).
  unfold U in E1. cbn [eval] in E1. rewrite H34 in E1. split; [exact E1 | exact E2].
Qed.

Lemma lazy_m11 : ltac2:(tb__ "0|2|
S0S38S39S26Q40A1M0G0A2M1A1S4dSbcVb6;A1A1S3bG1S51Vb4;S6aA2S4dS67A1A3A3").
Proof. clear. unfold m11, m10, m9, eager_model, null_none_model. rewrite !m_vm_lazy_with_vmmaps, m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps. reflexivity. Qed.
Lemma noacc_m11 : ltac2:(tb__ "0|2|
S0S38S39S26Q40A1M0G0A2M1A1S4eS47SbcVb6;A1A1A1S34G1S37G0G0Vb4;S6aA4S4eS47S67A1A1A3A3").
Proof.
  clear. unfold m11, m10, m9, eager_model, null_none_model, eager_h, null_none_h.
  rewrite !m_vmmaps_with_vmmaps. cbn [vm_noaccess]. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps. reflexivity.
Qed.
Lemma limit_m11 : ltac2:(tb__ "0|0|
S0S28S4fS47SbcVb6;A1A1A1S4fS47Vm;A1A1A3").
Proof. clear. pose proof m10_ledger as (_ & _ & M3 & _). unfold m11, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. exact M3. Qed.

Lemma LZ11 : ltac2:(tb__ "0|2|
S4cS28S0S38S39S26Q40M0A1M1G1A2A1S4dR2A1S4dSbcVb6;A1A1A3Sc0R2A1S0S36S52S27G0R3A2S4dR4A1A2S3aA3F_;F_;Fq;Fmd;").
Proof using HPL Hres Htop Hmaps Hlz.
  clear Ha1 Ha2 HBlim Hcls HPL6. intros md q Elz Hq. unfold shpg in Hq. rewrite Elz, lazy_m11, page_in_ranges_app. apply orb_true_intro. right.
  destruct Hq as [Hq|Hq].
  - apply high_shadow_lazy_m8; rewrite u64_of_lit by lia; unfold SHADOW_BAND_HI; lia.
  - apply low_shadow_lazy_m8; rewrite u64_of_lit by lia; unfold SHADOW_BAND_LO, SHADOW_RW_LO_END; lia.
Qed.
Lemma NA11 : ltac2:(tb__ "0|0|
S4cS28S0S54S47R2A1S47SbcVb6;A1A1A3S3S1S2aZ2008fff7000R2A2S2cR2Z10007fff8000A2A2S1S2aZ7fff7000R2A2S2cR2Z8fff7000A2A2A2S0S36SdbS4eS47R4A1A1R3A2S3dA3F_;F_;Fz;Fmd;").
Proof using HPL HPL4 Hres Htop Hmaps Hlz Hna.
  clear Ha1 Ha2 HBlim Hcls HPL6. intros md z Evm Hz. pose proof b4_facts as (_ & F4band & _).
  rewrite Evm, noacc_m11. unfold covered. cbn [existsb]. apply Bool.orb_false_iff. split.
  - unfold in_iv, ivB, ivS, in_rng, n9. cbn [fst snd]. rewrite u64_of_lit by lia. apply andb_false_iff.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI in F4band. destruct F4band as [F4b|F4b]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  - apply shadow_acc_m8. unfold SHADOW_BAND_HI, SHADOW_BAND_LO, SHADOW_RW_LO_END. lia.
Qed.

Lemma step11m : ltac2:(tb__ "0|4|
S6S8cS0S26Q40M0A1M1S5R2P1bA2Va1;A3S0G1S5R3P1cA2Va2;A3S0G1S5R4P1dA2VP;A3S0G1S5R5P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R6P1fA2A2A2S25G0G2A2A3S0G1S5R7P20A2Vb4;A3S0G1S5R8P21A2Vb5;A3S0G1S5R9P22A2Vb6;A3S2aZ7fff80000000S25G0S5RaP1A2A2A2S63S46S5eSbcVb6;A1M3S6eA2Sa2Vhi;A1RbS34G1S68RbA1S35G1A1A3RaA6S2S6S6S1Sc1P24RdR1A3S1Sc3RdR1A2S1S6dR1A1S63S46S5eG3S2bS6eZ3000A2A2Sa6Vhi;A1R1S6bRdA1RcA6A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Hcls Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho [tr [ms md]] H27 H28 H29 H30 H31 H32 H33 H34 HX1 Hsp.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (alloc_top_lt (m_vmmaps m)) as CL. unfold two_pow_64 in CL.
  pose proof m10_ledger as (M1 & M2 & M3 & M4 & M5).
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof (bandav_intro _ _ (proj1 (proj2 Ha1))) as HA1. pose proof (bandav_intro _ _ (proj1 (proj2 Ha2))) as HA2.
  pose proof b5_facts as (F5lo & _ & F5band' & F5top & F5al & _). pose proof (bandav_intro _ _ F5band') as F5band. clear F5band'.
  pose proof (b6_facts b6 HPL6) as (F6lo & F6band & F6top & F6al & Hfree6).
  clear Ha1 Ha2.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  destruct (v35_val rho HF H34) as [V35 U35].
  pose proof (erase_mat_eq_fields md (m11 b6) Hem) as (Evm & Elz & _).

  assert (Upri : bv_unsigned (pRI rho) = priZ rho).
  { unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
  assert (Hpri_al : priZ rho mod 4096 = 0).
  { unfold priZ.
    assert (D : exists k, bv_unsigned (spacebeg P) = 65536 * k).
    { exists ((bv_unsigned P) / 65536 + 1). rewrite SB. rewrite (Z.div_mod (bv_unsigned P) 65536) at 1 by lia. lia. }
    destruct D as [k Hk]. replace (bv_unsigned (rw rho 31%positive)) with (8192 * k) by lia.
    replace (8192 * k + 19327320064) with ((2 * k + 4718584) * 4096) by lia. apply Z_mod_mult. }
  assert (Hpri_RI : priZ rho = bv_unsigned RI / 8 + 0x7fff8000).
  { unfold priZ. rewrite RV. rewrite <- H31.
    replace (8 * bv_unsigned (rw rho 31%positive) + 2 ^ 37) with ((bv_unsigned (rw rho 31%positive) + 2 ^ 34) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  assert (Hsb : sbZ rho = bv_unsigned b6 / 8 + 0x7fff8000).
  { unfold sbZ. rewrite <- V35. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  pose proof F6al as Hk6'. apply Z.mod_divide in Hk6' as [k6 Hk6]; [|lia].
  assert (Hsb_al : sbZ rho mod 512 = 0).
  { replace (sbZ rho) with ((k6 + 4194240) * 512) by (unfold sbZ; lia). apply Z_mod_mult. }
  pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Qmod.
  assert (Hq1_al : q1Z rho mod 4096 = 0).
  { unfold q1Z. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. }
  assert (Hq1_le : q1Z rho <= sbZ rho < q1Z rho + 4096) by (unfold q1Z; lia).
  pose proof Hq1_al as Hq1_al'. apply Z.mod_divide in Hq1_al' as [t1 Ht1]; [|lia].
  pose proof Hpri_al as Hpri_al'. apply Z.mod_divide in Hpri_al' as [tp1 Htp1]; [|lia].

  assert (Hside : bv_unsigned b6 + 65536 <= bv_unsigned P \/ bv_unsigned P + 0x2000011000 <= bv_unsigned b6).
  { pose proof (region_free_In _ _ _ P n7 Hfree6 ltac:(apply in_app_iff; right; rewrite M2; cbn [In]; right; right; left; reflexivity)) as Hf.
    unfold iv_overlap in Hf. apply andb_false_iff in Hf. unfold n7 in Hf. rewrite !u64_of_lit in Hf by lia.
    destruct Hf as [Hf|Hf]; apply Z.ltb_ge in Hf; lia. }

  assert (KCL : clswin (q1Z rho)).
  { clear -Hcls Hsb Hq1_le F6lo F6top Phi Ht1. unfold clswin. destruct hi; cbn [clsZ] in Hcls; unfold SHADOW_BAND_HI, SHADOW_BAND_LO in Hcls; [left|right]; lia. }
  assert (Hq1_lo : 0x7fff7000 <= q1Z rho) by (clear -KCL; unfold clswin in KCL; lia).
  assert (Hq3_hi : q1Z rho + 12288 <= 0x10007fff8000) by (clear -KCL; unfold clswin in KCL; lia).
  assert (K3 : shpg (q1Z rho) /\ shpg (q1Z rho + 4096) /\ shpg (q1Z rho + 8192)) by (clear -KCL; unfold clswin in KCL; unfold shpg; lia).
  assert (KP : shpg (priZ rho + 4096) /\ shpg (priZ rho + 8192)) by (clear -Hpri_RI R1 R2 PLB Pceil Phi CL; unfold shpg; lia).
  assert (LIM : vm_limit (m_vmmaps md) = vm_limit (m_vmmaps m)) by (rewrite Evm; apply limit_m11).

  assert (DISJ : forall rho0 (S0 : sstate) q, Forall (holds rho0) (ss_facts S0) -> objs_clear_e G11 S0 = true ->
            rw rho0 27%positive = a1 -> rw rho0 28%positive = a2 -> rw rho0 30%positive = spacebeg P ->
            rw rho0 31%positive = rw rho 31%positive -> rw rho0 33%positive = b5 -> rw rho0 34%positive = b6 ->
            0x7fff7000 <= q -> q + 4096 <= 0x10007fff8000 -> (q + 4096 <= priZ rho \/ priZ rho + 4096 <= q) ->
            forall o, In o (ss_objs S0) -> ranges_disjoint (obj_range rho0 o) (bv_unsigned (Z_to_bv 64 q), bv_unsigned (Z_to_bv 64 q) + 4096)).
  { intros rho0 S0 q HF0 HC E27 E28 E30 E31 E33 E34 Hq0 Hq1 Hqp o Ho.
    apply (objs_clear_e_sound rho0 G11 S0 (Z_to_bv 64 q) 4096 HF0 HC); [lia | rewrite u64_of_lit by lia; lia | intros x Hx; rewrite u64_of_lit in Hx by lia; lia | | exact Ho].
    intros e sz Hin x Hx. rewrite u64_of_lit in Hx by lia.
    unfold G11, G10, G9, G8 in Hin. cbn [app] in Hin.
    destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]; cbn [eval].
    - rewrite E27. clear -HA1 Hx Hq0 Hq1. unfold bandav in HA1. lia.
    - rewrite E28. clear -HA2 Hx Hq0 Hq1. unfold bandav in HA2. lia.
    - change (eval rho0 ri30) with (eval rho0 ri30).
      assert (Eri : bv_unsigned (eval rho0 ri30) = bv_unsigned RI).
      { unfold ri30. cbn [eval]. rewrite E30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
        change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
      rewrite Eri. clear -R1 PLB Hx Hq1. lia.
    - change (eval rho0 shRI_base) with (pRI rho0).
      replace (bv_unsigned (pRI rho0)) with (priZ rho); [clear -Hqp Hx; lia|].
      rewrite <- Upri. unfold pRI, shRI_base. cbn [eval]. rewrite E31. reflexivity.
    - rewrite E33. clear -F5band Hx Hq0 Hq1. unfold bandav in F5band. lia.
    - rewrite E34. clear -F6band Hx Hq0 Hq1. unfold bandav in F6band. lia. }

  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m11 b6) (B11 + 12288) r (TP11 rho) tr0 md0).
  assert (HBlim' : B11 + 12288 + 4096 * 16 <= vm_limit (m_vmmaps m)) by (unfold B11; lia).

  assert (Hsp1 : SPA segsA J' (L11m hi) rho [pRI rho] (tr, mkCfg ms md)).
  { split; [exact Hsm|]. subst J'. cbv beta. unfold KxA. cbn [w_tr w_cfg cfg_model fst snd].
    split; [exact Htr|]. split; [exact Hem|].
    unfold TP11. destruct (q1Z rho =? priZ rho);
      pose proof (paid_cons_le md (Z_to_bv 64 (priZ rho + 4096)) [pRI rho]);
      pose proof (paid_cons_le md (Z_to_bv 64 (priZ rho + 8192)) (Z_to_bv 64 (priZ rho + 4096) :: [pRI rho]));
      pose proof (paid_cons_le md (Z_to_bv 64 (q1Z rho)) [pRI rho]);
      pose proof (paid_cons_le md (Z_to_bv 64 (q1Z rho + 4096)) (Z_to_bv 64 (q1Z rho) :: [pRI rho]));
      pose proof (paid_cons_le md (Z_to_bv 64 (q1Z rho + 8192)) (Z_to_bv 64 (q1Z rho + 4096) :: Z_to_bv 64 (q1Z rho) :: [pRI rho]));
      unfold page_size in *; lia. }
  pose proof L11m_len as (LEN & NX2 & FT2).
  assert (Hsp2 : SPA segsA J' (ax_setS (L11m hi) (T1_11 hi)) rho [pRI rho] (tr, mkCfg ms md)).
  { rewrite <- T1_11_eq. apply SPA_move_last; [rewrite LEN; lia | exact (proj1 L11m_X) | rewrite T1_11_eq; exact (same_T1_11 hi) | exact Hsp1]. }
  assert (Hsp3 : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (T2_11 hi)) rho [pRI rho] (tr, mkCfg ms md)).
  { apply (SPA_split segsA J' rho (ax_setS (L11m hi) (T1_11 hi)) 15 (SLit 512) (T2_11 hi)). exact (split_T2_11 hi). exact Hsp2. }
  assert (HF2 : Forall (holds rho) (ss_facts (T2_11 hi))) by (rewrite FT2; exact HF).

  assert (REL : forall R tp', let A5 := ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ R)) in
            SPA segsA J' A5 rho tp' (tr, mkCfg ms md) ->
            Forall (fun o => ob_dflt o = DZero /\ ob_cells o = [] /\ 0x646000 <= fst (obj_range rho o)) (tail11 :: R) ->
            let rho' := rho_absorb rho (tail11 :: R) (vms md tp' ms) in
            SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) C11) rho' tp' (tr, mkCfg ms md)
            /\ (forall a o, In o (tail11 :: R) -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0))).
  { intros R tp' A5 HA HR rho'.
    assert (Eo : ss_objs (ax_S A5) = firstn 16 (ss_objs (T2_11 hi)) ++ (tail11 :: R)).
    { subst A5. cbn [ax_S ax_setS set_objs ss_objs]. rewrite T2_objs at 1. rewrite <- app_assoc. reflexivity. }
    split.
    - pose proof (SPA_unobj segsA J' rho A5 (firstn 16 (ss_objs (T2_11 hi))) (tail11 :: R) tp' tr ms md Eo HA ltac:(intros X; exact X)) as X.
      exact X.
    - intros a o Ho Ha. subst rho'. rewrite rm_absorb_inside.
      + pose proof (proj1 (Forall_forall _ _) HR o Ho) as (D1 & D2 & D3).
        apply (SPA_dzero_bytes_A J' A5 rho tp' tr ms md o HA); [rewrite Eo; apply in_app_iff; right; exact Ho | exact D1 | exact D2 | exact D3 | exact Ha].
      + exists o. split; [exact Ho|]. rewrite u64_of_lit; [exact Ha|].
        pose proof (proj1 (Forall_forall _ _) HR o Ho) as (_ & _ & D3).
        split; [lia|].
        destruct HA as [HsmA _]. pose proof (smatchA_smatch segsA _ _ _ _ HsmA) as S0. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0.
        pose proof (smatch_mm segsA _ _ _ _ _ S0) as (Hh & _ & _).
        pose proof (proj1 (Forall_forall _ _) Hh o ltac:(rewrite Eo; apply in_app_iff; right; exact Ho)) as ((B1 & B2 & B3 & B4) & _).
        unfold obj_range in Ha. cbn [fst snd] in Ha. lia. }

  assert (Rtail : obj_range rho tail11 = (priZ rho + 512, priZ rho + 4096)).
  { unfold obj_range, obj_lo_of, obj_hi_of, soff, tail11. cbn [ob_base ob_lo ob_hi].
    change (eval rho shRI_base) with (pRI rho). rewrite Upri.
    replace (bv_signed (eval rho (SLit 512))) with 512 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    replace (bv_signed (eval rho (SLit 4096))) with 4096 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). reflexivity. }
  assert (Rzp : forall q, 0 <= q -> q + 4096 <= 2 ^ 64 -> obj_range rho (zero_page_obj (Z_to_bv 64 q)) = (q, q + 4096)).
  { intros q Hq0 Hq1. unfold obj_range, obj_lo_of, obj_hi_of, soff, zero_page_obj. cbn [ob_base ob_lo ob_hi eval].
    rewrite (u64_of_lit q) by lia. rewrite ?(u64_of_lit q) by lia.
    replace (bv_signed (Z_to_bv 64 0)) with 0 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change page_size with 4096. replace (bv_signed (Z_to_bv 64 4096)) with 4096 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Z.add_0_r. reflexivity. }

  assert (PRE : forall R tp' q, let A5 := ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ R)) in
            SPA segsA J' A5 rho tp' (tr, mkCfg ms md) ->
            shpg q -> q mod 4096 = 0 ->
            (q + 4096 <= priZ rho \/ priZ rho + 4096 <= q) ->
            (forall p, In p tp' -> bv_unsigned p <> q) ->
            (exists l, TP11 rho = l ++ (Z_to_bv 64 q :: tp')) ->
            Forall (fun o => ranges_disjoint (obj_range rho o) (q, q + 4096)) R ->
            SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ (R ++ [zero_page_obj (Z_to_bv 64 q)]))))
                rho (Z_to_bv 64 q :: tp') (tr, mkCfg ms md)).
  { intros R tp' q A5 HA Hq Hqal Hqp Hnin [l Hl] HR.
    assert (Hq01 : 0x7fff7000 <= q /\ q + 4096 <= 0x10007fff8000) by (clear -Hq; unfold shpg in Hq; lia). destruct Hq01 as [Hq0 Hq1].
    assert (Uq : bv_unsigned (Z_to_bv 64 q) = q) by (apply u64_of_lit; lia).
    replace (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ (R ++ [zero_page_obj (Z_to_bv 64 q)])))
      with (set_objs (ax_S A5) (ss_objs (ax_S A5) ++ [zero_page_obj (Z_to_bv 64 q)])).
    2:{ subst A5. cbn [ax_S ax_setS set_objs ss_objs]. rewrite app_assoc. reflexivity. }
    change (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (ax_S A5) (ss_objs (ax_S A5) ++ [zero_page_obj (Z_to_bv 64 q)])))
      with (ax_setS A5 (set_objs (ax_S A5) (ss_objs (ax_S A5) ++ [zero_page_obj (Z_to_bv 64 q)]))).
    apply (SPA_prepay_zero segsA J' rho A5 (Z_to_bv 64 q) tp' tr ms md HA).
    - rewrite Uq. exact Hqal.
    - apply (LZ11 md q Elz Hq).
    - intros Hi. exact (Hnin _ Hi Uq).
    - intros j Hj. unfold page_size in Hj. rewrite Uq. apply (NA11 md _ Evm). clear -Hq Hj. unfold shpg in Hq. lia.
    -
      destruct HA as [_ HK]. subst J'. cbv beta in HK. destruct HK as (_ & _ & HP). cbn [w_tr w_cfg cfg_model fst snd] in HP.
      unfold headroom. rewrite LIM.
      enough (paid md tp' <= paid md (TP11 rho)) by (unfold page_size; lia).
      rewrite Hl. etransitivity; [apply (paid_cons_ge md (Z_to_bv 64 q)) | apply paid_app_ge].
    - subst A5. cbn [ax_S ax_setS set_objs ss_objs]. apply Forall_app. split.
      + apply Forall_forall. intros o Ho. rewrite Uq.
        pose proof (DISJ rho (T2_11 hi) q HF2 clear_T2 H27 H28 H30 eq_refl H33 H34 Hq0 Hq1 Hqp o Ho) as X.
        rewrite Uq in X. exact X.
      + rewrite Uq. exact HR.
    - intros X; exact X. }

  assert (FIN : forall R tp6,
            SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ R))) rho tp6 (tr, mkCfg ms md) ->
            Forall (fun o => ob_dflt o = DZero /\ ob_cells o = [] /\ 0x646000 <= fst (obj_range rho o) /\ snd (obj_range rho o) <= 0x10007fff8000) (tail11 :: R) ->
            (forall a, sbZ rho <= a < sbZ rho + 8192 -> exists o, In o (tail11 :: R) /\ fst (obj_range rho o) <= a < snd (obj_range rho o)) ->
            tp6 = TP11 rho -> priZ rho + 512 <= sbZ rho \/ sbZ rho + 8192 <= priZ rho ->
            (forall a p, In p tp6 -> bv_unsigned p <= a < bv_unsigned p + 4096 -> ~ (priZ rho <= a < priZ rho + 512) ->
               exists o, In o (tail11 :: R) /\ fst (obj_range rho o) <= a < snd (obj_range rho o)) ->
            exists rho', agree_vars 36%positive rho rho' /\ RMH rho rho' /\ Z11 rho' /\ SPA segsA (KxA (m11 b6) (B11 + 12288)) (M11 hi) rho' (TP11 rho) (tr, mkCfg ms md)).
  { intros R tp6 HA HR COV Etp Hfar COVT.
    destruct (REL R tp6 HA (Forall_impl _ (fun o X => conj (proj1 X) (conj (proj1 (proj2 X)) (proj1 (proj2 (proj2 X))))) HR)) as [Hsp6 ZERO]. cbv zeta in Hsp6, ZERO.
    set (rho' := rho_absorb rho (tail11 :: R) (vms md tp6 ms)) in *.
    exists rho'. split; [subst rho'; split; intros; reflexivity|].
    split.
    { subst rho'. apply RMH_absorb; [apply RMH_refl|]. intros a [Ha _] (o & Ho & Hr).
      pose proof (proj1 (Forall_forall _ _) HR o Ho) as (_ & _ & _ & Hhi). clear -Ha Hr Hhi HX1. lia. }
    split.
    { intros a p Hp Ha H64 N1 N2.
      assert (ET : TP11 rho' = TP11 rho) by (subst rho'; unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite !rw_absorb; reflexivity).
      rewrite ET, <- Etp in Hp. unfold priZ in N1. subst rho'. rewrite rw_absorb in N1. fold (priZ rho) in N1.
      destruct (COVT a p Hp Ha N1) as (o & Ho & Hao). exact (ZERO a o Ho Hao). }
    pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp6) as HF6. cbn [ax_S ax_setS] in HF6.
    assert (Esb : bv_unsigned (eval rho' shB6_base) = sbZ rho).
    { subst rho'. rewrite eval_absorb. unfold shB6_base, sbZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 0x7fff8000) with 0x7fff8000. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    assert (Hsp7 : SPA segsA J' (ax_setS (ax_setS (ax_setS (L11m hi) (T1_11 hi)) C11)
                     (mkSS (ss_pc C11) (ss_regs C11) (ss_fregs C11) (ss_fcsr C11) (ss_resv C11)
                           (ss_objs C11 ++ [mkObj shB6_base (SLit 0) (SLit 8192) [] DZero]) (ss_facts C11) 36%positive (ss_lenient C11)))
                     rho' tp6 (tr, mkCfg ms md)).
    { apply (SPA_carve_zero segsA J' rho' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) C11) tp6 tr ms md shB6_base 0 8192 36%positive Hsp6).
      - exact carve_swf.
      - cbn [ax_S ax_setS C11 set_objs ss_next]. rewrite NX2. lia.
      - lia. - lia. - lia.
      - rewrite Esb. lia.
      - rewrite Esb. lia.
      - cbn [ax_S ax_setS]. apply Forall_forall. intros o Ho. rewrite Esb.
        pose proof (objs_clear_e_sound rho' G11c C11 (Z_to_bv 64 (sbZ rho)) 8192 HF6 clear_C11 ltac:(lia)
                      ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros x Hx; rewrite u64_of_lit in Hx by lia; lia)) as X.
        rewrite u64_of_lit in X by lia. replace (sbZ rho + 0) with (sbZ rho) by lia. apply X; [|exact Ho].
        intros e sz Hin x Hx. unfold G11c in Hin.
        assert (Hblk : 0x7fff7000 <= sbZ rho /\ sbZ rho + 8192 <= 0x10007fff8000) by (clear -Hq1_le Hq1_lo Hq3_hi; lia).
        subst rho'. destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]; rewrite eval_absorb; cbn [eval].
        + rewrite H27. clear -HA1 Hx Hblk. unfold bandav in HA1. lia.
        + rewrite H28. clear -HA2 Hx Hblk. unfold bandav in HA2. lia.
        + change (eval rho ri30) with (eval rho ri30).
          assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RI).
          { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
            change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
          rewrite Eri. clear -R1 PLB Hx Hblk. lia.
        + change (eval rho shRI_base) with (pRI rho). rewrite Upri. clear -Hfar Hx. lia.
        + rewrite H33. clear -F5band Hx Hblk. unfold bandav in F5band. lia.
        + rewrite H34. clear -F6band Hx Hblk. unfold bandav in F6band. lia.
      - intros a Ha. rewrite Esb in Ha. destruct (COV a ltac:(lia)) as (o & Ho & Hao). exact (ZERO a o Ho Hao).
      - intros rr y j Hrr. cbn [ax_X ax_setS] in Hrr. rewrite (proj1 L11m_X) in Hrr. destruct Hrr. }
    pose proof (SPA_refacts segsA J' rho' _ (F11m ++ ss_facts C11) tp6 _ Hsp7 carve_below) as Hsp8.
    assert (HF11 : Forall (holds rho') (ss_facts (ax_S (ax_setS (ax_setS (ax_setS (L11m hi) (T1_11 hi)) C11)
                     (mkSS (ss_pc C11) (ss_regs C11) (ss_fregs C11) (ss_fcsr C11) (ss_resv C11)
                           (ss_objs C11 ++ [mkObj shB6_base (SLit 0) (SLit 8192) [] DZero]) (ss_facts C11) 36%positive (ss_lenient C11))))) ->
                   Forall (holds rho') (F11m ++ ss_facts C11)).
    { intros HF'. cbn [ax_S ax_setS ss_facts] in HF'. apply Forall_app. split; [|exact HF']. unfold F11m. constructor; [|constructor].
      cbn [holds]. subst rho'. rewrite rw_absorb. change (2 ^ 9) with 512. split; [lia|].
      replace (bv_unsigned (rw rho 35%positive)) with (k6 * 512) by lia. apply Z_mod_mult. }
    specialize (Hsp8 HF11). rewrite carve_M11 in Hsp8.
    rewrite Etp in Hsp8. exact Hsp8. }

  assert (HRI8 : bv_unsigned RI = 8 * (bv_unsigned (rw rho 31%positive) + 2 ^ 34)) by (rewrite RV, <- H31; lia).
  assert (Hsp3' : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ []))) rho [pRI rho] (tr, mkCfg ms md)).
  { rewrite app_nil_r. exact Hsp3. }
  pose proof K3 as (K30 & K31 & K32). pose proof KP as (KP1 & KP2).
  destruct (Z.eqb_spec (q1Z rho) (priZ rho)) as [EQ|NE].
  -
    assert (Habove : bv_unsigned P + 0x2000011000 <= bv_unsigned b6).
    { destruct Hside as [Hlow|Hhigh]; [|exact Hhigh]. exfalso. unfold q1Z, sbZ, priZ in EQ. lia. }
    assert (Hsb_ge : priZ rho + 512 <= sbZ rho) by (unfold sbZ, priZ; lia).
    assert (Hsb_lt : sbZ rho < priZ rho + 4096) by (unfold q1Z in EQ; lia).
    clear Hside.
    assert (ETP : TP11 rho = [Z_to_bv 64 (priZ rho + 8192); Z_to_bv 64 (priZ rho + 4096); pRI rho]).
    { unfold TP11. rewrite (proj2 (Z.eqb_eq _ _) EQ). reflexivity. }
    assert (Hsp4 : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ ([] ++ [zero_page_obj (Z_to_bv 64 (priZ rho + 4096))]))))
                     rho (Z_to_bv 64 (priZ rho + 4096) :: [pRI rho]) (tr, mkCfg ms md)).
    { apply (PRE [] [pRI rho] (priZ rho + 4096) Hsp3'); [exact KP1 | | right; lia | | exists [Z_to_bv 64 (priZ rho + 8192)]; rewrite ETP; reflexivity | constructor].
      - replace (priZ rho + 4096) with ((tp1 + 1) * 4096) by lia. apply Z_mod_mult.
      - intros p0 [<-|[]]. rewrite Upri. lia. }
    cbn [app] in Hsp4.
    assert (Hsp5 : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ ([zero_page_obj (Z_to_bv 64 (priZ rho + 4096))] ++ [zero_page_obj (Z_to_bv 64 (priZ rho + 8192))]))))
                     rho (Z_to_bv 64 (priZ rho + 8192) :: Z_to_bv 64 (priZ rho + 4096) :: [pRI rho]) (tr, mkCfg ms md)).
    { apply (PRE [zero_page_obj (Z_to_bv 64 (priZ rho + 4096))] _ (priZ rho + 8192) Hsp4); [exact KP2 | | right; lia | | exists []; rewrite ETP; reflexivity |].
      - replace (priZ rho + 8192) with ((tp1 + 2) * 4096) by lia. apply Z_mod_mult.
      - intros p0 [<-|[<-|[]]]; [rewrite u64_of_lit by lia; lia | rewrite Upri; lia].
      - constructor; [|constructor]. rewrite (Rzp (priZ rho + 4096)) by lia. unfold ranges_disjoint. cbn [fst snd]. lia. }
    cbn [app] in Hsp5.
    apply (FIN [zero_page_obj (Z_to_bv 64 (priZ rho + 4096)); zero_page_obj (Z_to_bv 64 (priZ rho + 8192))] _ Hsp5).
    + constructor; [|constructor; [|constructor; [|constructor]]].
      * split; [reflexivity|]. split; [reflexivity|]. rewrite Rtail. cbn [fst snd]. lia.
      * split; [reflexivity|]. split; [reflexivity|]. rewrite (Rzp (priZ rho + 4096)) by lia. cbn [fst snd]. lia.
      * split; [reflexivity|]. split; [reflexivity|]. rewrite (Rzp (priZ rho + 8192)) by lia. cbn [fst snd]. lia.
    + intros a Ha.
      destruct (Z_lt_dec a (priZ rho + 4096)) as [L1|L1].
      { exists tail11. split; [left; reflexivity|]. rewrite Rtail. cbn [fst snd]. lia. }
      destruct (Z_lt_dec a (priZ rho + 8192)) as [L2|L2].
      { exists (zero_page_obj (Z_to_bv 64 (priZ rho + 4096))). split; [right; left; reflexivity|]. rewrite (Rzp (priZ rho + 4096)) by lia. cbn [fst snd]. lia. }
      exists (zero_page_obj (Z_to_bv 64 (priZ rho + 8192))). split; [right; right; left; reflexivity|]. rewrite (Rzp (priZ rho + 8192)) by lia. cbn [fst snd]. lia.
    + symmetry. exact ETP.
    + left. exact Hsb_ge.
    + intros a p0 Hp0 Ha0 N1.
      destruct Hp0 as [<-|[<-|[<-|[]]]].
      * exists (zero_page_obj (Z_to_bv 64 (priZ rho + 8192))). split; [right; right; left; reflexivity|]. rewrite (Rzp (priZ rho + 8192)) by lia. cbn [fst snd]. rewrite u64_of_lit in Ha0 by lia. lia.
      * exists (zero_page_obj (Z_to_bv 64 (priZ rho + 4096))). split; [right; left; reflexivity|]. rewrite (Rzp (priZ rho + 4096)) by lia. cbn [fst snd]. rewrite u64_of_lit in Ha0 by lia. lia.
      * exists tail11. split; [left; reflexivity|]. rewrite Rtail. cbn [fst snd]. rewrite Upri in Ha0. lia.
  -
    assert (Hfar : q1Z rho + 12288 <= priZ rho \/ priZ rho + 4096 <= q1Z rho).
    { destruct Hside as [Hlow|Hhigh].
      - left. unfold sbZ, priZ in *. lia.
      - right. assert (Hsb_ge : priZ rho + 512 <= sbZ rho) by (unfold sbZ, priZ; lia).

        assert (tp1 <= t1) by lia. assert (tp1 <> t1) by (intros ->; apply NE; lia). lia. }
    clear Hside.
    assert (ETP : TP11 rho = [Z_to_bv 64 (q1Z rho + 8192); Z_to_bv 64 (q1Z rho + 4096); Z_to_bv 64 (q1Z rho); pRI rho]).
    { unfold TP11. rewrite (proj2 (Z.eqb_neq _ _) NE). reflexivity. }
    assert (Hsp4 : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ ([] ++ [zero_page_obj (Z_to_bv 64 (q1Z rho))]))))
                     rho (Z_to_bv 64 (q1Z rho) :: [pRI rho]) (tr, mkCfg ms md)).
    { apply (PRE [] [pRI rho] (q1Z rho) Hsp3'); [exact K30 | exact Hq1_al | clear -Hfar; lia | | exists [Z_to_bv 64 (q1Z rho + 8192); Z_to_bv 64 (q1Z rho + 4096)]; rewrite ETP; reflexivity | constructor].
      intros p0 [<-|[]]. rewrite Upri. clear -Hfar. lia. }
    cbn [app] in Hsp4.
    assert (Hsp5 : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++ ([zero_page_obj (Z_to_bv 64 (q1Z rho))] ++ [zero_page_obj (Z_to_bv 64 (q1Z rho + 4096))]))))
                     rho (Z_to_bv 64 (q1Z rho + 4096) :: Z_to_bv 64 (q1Z rho) :: [pRI rho]) (tr, mkCfg ms md)).
    { apply (PRE _ _ (q1Z rho + 4096) Hsp4); [exact K31 | | clear -Hfar; lia | | exists [Z_to_bv 64 (q1Z rho + 8192)]; rewrite ETP; reflexivity |].
      - replace (q1Z rho + 4096) with ((t1 + 1) * 4096) by lia. apply Z_mod_mult.
      - intros p0 [<-|[<-|[]]]; [rewrite u64_of_lit by lia; lia | rewrite Upri; clear -Hfar; lia].
      - constructor; [|constructor]. rewrite (Rzp (q1Z rho)) by lia. unfold ranges_disjoint. cbn [fst snd]. lia. }
    cbn [app] in Hsp5.
    assert (Hsp5b : SPA segsA J' (ax_setS (ax_setS (L11m hi) (T1_11 hi)) (set_objs (T2_11 hi) (ss_objs (T2_11 hi) ++
                        ([zero_page_obj (Z_to_bv 64 (q1Z rho)); zero_page_obj (Z_to_bv 64 (q1Z rho + 4096))] ++ [zero_page_obj (Z_to_bv 64 (q1Z rho + 8192))]))))
                     rho (Z_to_bv 64 (q1Z rho + 8192) :: Z_to_bv 64 (q1Z rho + 4096) :: Z_to_bv 64 (q1Z rho) :: [pRI rho]) (tr, mkCfg ms md)).
    { apply (PRE _ _ (q1Z rho + 8192) Hsp5); [exact K32 | | clear -Hfar; lia | | exists []; rewrite ETP; reflexivity |].
      - replace (q1Z rho + 8192) with ((t1 + 2) * 4096) by lia. apply Z_mod_mult.
      - intros p0 [<-|[<-|[<-|[]]]]; [rewrite u64_of_lit by lia; lia | rewrite u64_of_lit by lia; lia | rewrite Upri; clear -Hfar; lia].
      - constructor; [|constructor; [|constructor]].
        + rewrite (Rzp (q1Z rho)) by lia. unfold ranges_disjoint. cbn [fst snd]. lia.
        + rewrite (Rzp (q1Z rho + 4096)) by lia. unfold ranges_disjoint. cbn [fst snd]. lia. }
    cbn [app] in Hsp5b.
    apply (FIN _ _ Hsp5b).
    + constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * split; [reflexivity|]. split; [reflexivity|]. rewrite Rtail. cbn [fst snd]. lia.
      * split; [reflexivity|]. split; [reflexivity|]. rewrite (Rzp (q1Z rho)) by lia. cbn [fst snd]. lia.
      * split; [reflexivity|]. split; [reflexivity|]. rewrite (Rzp (q1Z rho + 4096)) by lia. cbn [fst snd]. lia.
      * split; [reflexivity|]. split; [reflexivity|]. rewrite (Rzp (q1Z rho + 8192)) by lia. cbn [fst snd]. lia.
    + intros a Ha.
      destruct (Z_lt_dec a (q1Z rho + 4096)) as [L1|L1].
      { exists (zero_page_obj (Z_to_bv 64 (q1Z rho))). split; [right; left; reflexivity|]. rewrite (Rzp (q1Z rho)) by lia. cbn [fst snd]. lia. }
      destruct (Z_lt_dec a (q1Z rho + 8192)) as [L2|L2].
      { exists (zero_page_obj (Z_to_bv 64 (q1Z rho + 4096))). split; [right; right; left; reflexivity|]. rewrite (Rzp (q1Z rho + 4096)) by lia. cbn [fst snd]. lia. }
      exists (zero_page_obj (Z_to_bv 64 (q1Z rho + 8192))). split; [right; right; right; left; reflexivity|]. rewrite (Rzp (q1Z rho + 8192)) by lia. cbn [fst snd]. lia.
    + symmetry. exact ETP.
    + clear -Hfar Hq1_le. lia.
    + intros a p0 Hp0 Ha0 N1.
      destruct Hp0 as [<-|[<-|[<-|[<-|[]]]]].
      * exists (zero_page_obj (Z_to_bv 64 (q1Z rho + 8192))). split; [right; right; right; left; reflexivity|]. rewrite (Rzp (q1Z rho + 8192)) by lia. cbn [fst snd]. rewrite u64_of_lit in Ha0 by lia. lia.
      * exists (zero_page_obj (Z_to_bv 64 (q1Z rho + 4096))). split; [right; right; left; reflexivity|]. rewrite (Rzp (q1Z rho + 4096)) by lia. cbn [fst snd]. rewrite u64_of_lit in Ha0 by lia. lia.
      * exists (zero_page_obj (Z_to_bv 64 (q1Z rho))). split; [right; left; reflexivity|]. rewrite (Rzp (q1Z rho)) by lia. cbn [fst snd]. rewrite u64_of_lit in Ha0 by lia. lia.
      * exists tail11. split; [left; reflexivity|]. rewrite Rtail. cbn [fst snd]. rewrite Upri in Ha0. lia.
Qed.

Definition sub12 (hi : bool) : wsub := infer_sub 36%positive (set_objs (ax_S (E_k12c hi)) (ss_objs (ax_S E_k12))) (ax_S E_k12d).
Lemma merge12_id : forall hi, wsub_id_below (sub12 hi) 36%positive = true.
Proof. clear. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k12c_X : ltac2:(tb__ "0|3|
S36S1S0S38S39S7S7A2M0A1S89Sa8R1A1M1A1S35G0A1A3S1S0S7S8aG1A1S8Sc4A1A3S1S0S29S1dS85Sa6R1A1A1M2A1P24A3S0S36S19G2A1S3dA3A2A2A2Fhi;").
Proof. clear. intros [|]; repeat split; reflexivity. Qed.
Lemma objShB6_last : ltac2:(tb__ "0|1|
S36S2S38S12A1M0G0S0S9SccS9S10S85Sa8R2A1A1A1SbbA3S13SaeS8Z0A1S8Z2000A1R1S11A5A3Lcells;A2Fhi;").
Proof. clear. intros [|]; eexists; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k12c_facts35 : ltac2:(tb__ "0|3|
S36S1S0S36Sc8SaSfS16SbP23A1M0S8S30S2fZ2Z3dA2Z1A2A1A2A1ScS85Sa8R1A1A1A1M1A3S3aA3S1S0S36Sc8SaSfS18S17Sd2G0S8Z3A1A3SbP22A1M2A2A1G1A3S3aA3S0S36Sc8SaSfS16G2S8S30Z7fffff800000Z10000A2A1A2A1G1A3S3aA3A2A2Fhi;").
Proof. clear. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma seg11b_post : ltac2:(tb__ "0|3|
S6S38S50A1M0Se1S4cS6dR4A1S2aZ7fff80000000S25Q40S5R5P1A2A2A2S64S46S5eSbcVb6;A1S2bS6eZ3000A2A2M1P24M2R6S6bR6A1S34S86S87Sa8Vhi;A1Sc6A2S35S86A1A3S37G0Sd7R5Sd8R4R3A2A4A7S2S6S6S1Sc1G2R8R1A3S1Sc3R8R1A2S1S6dR1A1S1S6fR1A1S63S46G1Sa9R1S6bR8A1S37G0Sd7R7Sd8R6R5A2A4A6A2A2A2A2Lrho';A2F_;F_;F_;Fmd;Fms;Ftr;Frho;").
Proof.
  clear. intros rho tr ms md HZ HX1 Hw.
  apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho' & Hag & Hsp).
  set (rho2 := rho_absorb rho' [last (ss_objs (ax_S (E_k12c hi))) objShB6] (vms md (TP11 rho) ms)).
  destruct (objShB6_last hi) as [cells SH].
  assert (RNG : forall a, bv_unsigned (rw rho 1%positive) + 16 <= bv_unsigned a \/ ~ (sbZ rho' <= bv_unsigned a < sbZ rho' + 8192) ->
                ~ in_ranges rho' [last (ss_objs (ax_S (E_k12c hi))) objShB6] a).
  { intros a Ha (o & [<-|[]] & Hr). revert Hr. rewrite SH. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite !soff_lit_small by lia.
    unfold shB6_base. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0x7fff8000) with 0x7fff8000.
    pose proof (urange (rw rho' 35%positive)) as U35. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (E_k12c_facts35 hi) as (X35 & X34 & X34c). pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HFs.
    pose proof (fact_of_state _ _ rho' X35 HFs) as B35. cbn [holds eval] in B35.
    rewrite Z_to_bv_unsigned in B35. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in B35.
    pose proof (fact_of_state _ _ rho' X34 HFs) as B34. cbn [holds] in B34. apply (f_equal bv_unsigned) in B34. cbn [eval] in B34.
    rewrite sll_val in B34. change (3 mod 64) with 3 in B34. rewrite Z.shiftl_mul_pow2 in B34 by lia. change (2 ^ 3) with 8 in B34.
    rewrite Z.mod_small in B34 by lia.
    pose proof (fact_of_state _ _ rho' X34c HFs) as C34. cbn [holds eval] in C34. rewrite Z_to_bv_unsigned in C34.
    change (bv_wrap 64 (0x7fffff800000 - 0x10000)) with (0x7fffff800000 - 0x10000) in C34.
    rewrite Z.mod_small by lia. unfold sbZ in Ha. intros Hr. lia. }
  assert (Hsp2 : SPA segsA (KxA (m11 b6) (B11 + 12288)) (ax_setS (E_k12c hi) (set_objs (ax_S (E_k12c hi)) (ss_objs (ax_S E_k12)))) rho2 (TP11 rho) (tr, mkCfg ms md)).
  { apply (SPA_unobj segsA _ rho' (E_k12c hi) (ss_objs (ax_S E_k12)) [last (ss_objs (ax_S (E_k12c hi))) objShB6] (TP11 rho) tr ms md (E_k12_split hi) Hsp).
    intros X; exact X. }
  pose proof (SPA_entails segsA (KxA (m11 b6) (B11 + 12288)) 36%positive _ E_k12d (sub12 hi) rho2 (TP11 rho) _ (merge12_ok hi) (merge12_id hi)
                (stableA_KxA segsA _ _ _) Hsp2) as Hsp3.
  pose proof (rho_sub_agree (sub12 hi) 36%positive rho2 (merge12_id hi)) as (V2 & L2 & R2).
  exists (rho_sub rho2 (sub12 hi)).
  destruct Hag as (V & L & R).
  assert (E2 : forall i, (i < 36)%positive -> rw (rho_sub rho2 (sub12 hi)) i = rw rho' i).
  { intros i Hi. rewrite <- (V2 i Hi). subst rho2. apply rw_absorb. }
  assert (RNGo : obj_range rho' (last (ss_objs (ax_S (E_k12c hi))) objShB6) = (sbZ rho', sbZ rho' + 8192)).
  { rewrite SH. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite !soff_lit_small by lia.
    unfold shB6_base, sbZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0x7fff8000) with 0x7fff8000.
    pose proof (E_k12c_facts35 hi) as (X35 & _ & _). pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HFs.
    pose proof (fact_of_state _ _ rho' X35 HFs) as B35. cbn [holds eval] in B35. rewrite Z_to_bv_unsigned in B35. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in B35.
    pose proof (urange (rw rho' 35%positive)). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. f_equal; lia. }
  split; [|split; [|split; [|split]]].
  - split; [intros i Hi; rewrite (E2 i Hi); symmetry; apply V; exact Hi | intros l; rewrite <- (L2 l); subst rho2; rewrite rl_absorb; symmetry; apply L].
  -
    intros a Ha. rewrite <- (R2 a). subst rho2. rewrite rm_absorb_outside; [symmetry; apply R|]. apply RNG. left. exact (proj1 Ha).
  -
    assert (HZ' : Z11 rho') by (apply (Z11_ext rho rho'); [symmetry; apply V; lia | symmetry; apply V; lia | intros a; symmetry; apply R | exact HZ]).
    assert (AGV : agree_vars 36 rho' (rho_sub rho2 (sub12 hi))).
    { split; [exact E2 | intros l; rewrite <- (L2 l); subst rho2; apply rl_absorb]. }
    pose proof (TP11_agree _ _ AGV) as ET.
    intros a p Hp Ha H64 N1 N2. rewrite <- (R2 (Z_to_bv 64 a)).
    rewrite ET in Hp. rewrite (priZ_ext _ _ (E2 31%positive ltac:(lia))) in N1. rewrite (sbZ_ext _ _ (E2 35%positive ltac:(lia))) in N2.
    subst rho2. rewrite rm_absorb_outside; [exact (HZ' a p Hp Ha H64 N1 N2)|].
    apply RNG. right. rewrite u64_of_lit by (pose proof (urange p); lia). exact N2.
  -
    assert (HZ' : Z11 rho') by (apply (Z11_ext rho rho'); [symmetry; apply V; lia | symmetry; apply V; lia | intros a; symmetry; apply R | exact HZ]).
    assert (AGV : agree_vars 36 rho' (rho_sub rho2 (sub12 hi))).
    { split; [exact E2 | intros l; rewrite <- (L2 l); subst rho2; apply rl_absorb]. }
    pose proof (TP11_agree _ _ AGV) as ET.
    intros a p Hp Ha H64 N1. rewrite <- (R2 (Z_to_bv 64 a)).
    rewrite ET in Hp. rewrite (priZ_ext _ _ (E2 31%positive ltac:(lia))) in N1. pose proof (urange p) as Up.
    destruct (Z_lt_ge_dec a (sbZ rho')) as [Hlt|Hge]; [|destruct (Z_lt_ge_dec a (sbZ rho' + 8192)) as [Hin|Hout]].
    + subst rho2. rewrite rm_absorb_outside; [rewrite (HZ' a p Hp Ha H64 N1 ltac:(lia)); discriminate|]. apply RNG. right. rewrite u64_of_lit by lia. lia.
    + subst rho2. exact (SPA_released_defined (KxA (m11 b6) (B11 + 12288)) (E_k12c hi) rho' (TP11 rho) tr ms md (ss_objs (ax_S E_k12)) _ (E_k12_split hi)
                            ltac:(rewrite SH; reflexivity) ltac:(rewrite RNGo; cbn [fst]; pose proof (urange (rw rho' 35%positive)); unfold sbZ; lia) Hsp a ltac:(rewrite RNGo; cbn [fst snd]; lia)).
    + subst rho2. rewrite rm_absorb_outside; [rewrite (HZ' a p Hp Ha H64 N1 ltac:(lia)); discriminate|]. apply RNG. right. rewrite u64_of_lit by lia. lia.
  - exact Hsp3.
Qed.

Lemma seg11b : ltac2:(tb__ "0|2|
S6S6dR1A1M0S2aZ7fff80000000S25Q40S5R2P1A2A2A2S8eS46Vok;S63S46S5eSbcVb6;A1S2bS6eZ3000A2A2M1Sa6Vhi;A1R3S6bR3A1A5S8cS2S6S6S1Sc1P24R5R1A3S1Sc3R5R1A2S1G0S1S6fR1A1S63S46G1Sa9R1S6bR5A1R2A6A2A2A2A2Lrho';A2Lw;A4F_;F_;Frho;").
Proof using OKF.
  clear Ha1 Ha2 HBlim Htop Hcls HPL6 HPL5 HPL4 HPL. intros rho HZ HX1.
  pose proof (E_k12c_X hi) as (EX & EB & EN & EL).
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact (run11b hi) | apply OKFx | exact EL | apply stableA_KxA]. }
  intros [tr [ms md]] Hw. rewrite EN in Hw. exact (seg11b_post rho tr ms md HZ HX1 Hw).
Qed.
Lemma eseg11b : ltac2:(tb__ "0|2|
S6S6dR1A1M0S2aZ7fff80000000S25Q40S5R2P1A2A2A2S8dS46S63S46S5eSbcVb6;A1S2bS6eZ3000A2A2M1Sa6Vhi;A1R3S6bR3A1A5S8cS2S6S6S1Sc1P24R5R1A3S1Sc3R5R1A2S1G0S1S6fR1A1S63S46G1Sa9R1S6bR5A1R2A6A2A2A2A2Lrho';A2Lw;A3F_;F_;Frho;").
Proof.
  clear. intros rho HZ HX1.
  pose proof (E_k12c_X hi) as (EX & EB & EN & EL).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [exact EL | apply stableA_KxA | exact (run11b hi)]. }
  intros [tr [ms md]] Hw. rewrite EN in Hw. exact (seg11b_post rho tr ms md HZ HX1 Hw).
Qed.
End S11m.

Hypothesis Hwit11 : ltac2:(tb__ "0|2|
S2S26Q40M0A1M1G1S5fS27G0Z0A2Sa0Vb5;A1S27G0Z10000A2R1A4La;A2").
Lemma eseg11a : ltac2:(tb__ "0|7|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0G1S5R6P20A2Vb4;A3S0G1S5R7P21A2Vb5;A3S0S28S25G0S5R8P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eSa0Vb5;A1M3S2bS2bVB;Z2000A2Z1000A2M4A2Sa5R9S34G1S68R9A1S35G1A1M5A3A5S8cS2G1G1S1S5fS27G0Z0A2G3S27G0Z10000M6A2R1A4S63S46S5eSbcR1A1S2bG4G6A2A2SdaSb1A1ScdRbP22R1A3S34G1S68RbA1G5A3R2A6A2Lb6;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 Hmaps Hres Htop Hlz Hwit11.
  clear Ha1 Ha2. intros rho H27 H28 H29 H30 H31 H32 H33 Hv1. pose proof m10_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (eager_rw_enode E_k11 65536 (m10 b5) (B + 8192 + 4096) G10 35%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear11.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m10.
    + exact band_m10.
    + rewrite M3. lia.
    + exact Hwit11.
    + intros e sz Hin. unfold G10 in Hin. apply in_app_iff in Hin as [Hin|[[= <- <-]|[]]].
      * apply (HG9 rho _ H27 H28 H30 H31); [|exact Hin]. rewrite M2. exists [(b5, Z_to_bv 64 4096); (b4, n9)].
        pose proof m8_ledger as (_ & K2 & _). rewrite K2. reflexivity.
      * left. cbn [eval]. rewrite H33. exists b5, (Z_to_bv 64 4096). split; [rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
    + rewrite M4. exact Hv1. }
  intros w (b6 & HPL6 & Hsp). exists b6. split; [exact HPL6|].
  assert (N : ss_next (ax_S E_k11) = 34%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N in Hsp.
  exact (SPA_X0 (KxA (m11 b6) (B + 8192 + 4096 + 65536)) _ S_k11ok _ w eq_refl Hsp).
Qed.

End S11.

Hypothesis Hwit10 : ltac2:(tb__ "0|2|
S2S26Q40M0A1M1G1S5fS27G0Z0A2S69Vb4;A1S27G0Z1000A2R1A4La;A2").
Lemma eseg10 : ltac2:(tb__ "0|7|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0G1S5R6P20A2Vb4;A3S0S28S25G0S5R7P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eS69Vb4;A1M3S2bVB;Z2000A2M4A2Sa4R8S34G1S68R8A1S35G1A1M5A3A5S8cS2G1G1S1S5fS27G0Z0A2G3S27G0Z1000M6A2R1A4S64S46S5eSa0R1A1S2bG4G6A2A2P22ScdRaP21R1A3S34G1S68RaA1G5A3S34S86S87Sa5Sc6A2S35S86A1A3R2A7A2Lb5;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 Hmaps Hres Htop Hlz Hwit10.
  clear Ha1 Ha2. intros rho H27 H28 H29 H30 H31 H32 Hv1. pose proof m9_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply etriple_seq.
  { apply (eager_rw_enode E_k10 4096 (m9 b4) (B + 8192) G9 34%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear10.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m9.
    + exact band_m9.
    + rewrite M3. lia.
    + exact Hwit10.
    + apply (HG9 rho _ H27 H28 H30 H31). rewrite M2. exists [(b4, n9)]. pose proof m8_ledger as (_ & K2 & _). rewrite K2. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b5. intros w [HPL5 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_k10) = 33%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m10 b5) (B + 8192 + 4096)) (eager_ok E_k10 4096 34) (rho_set_rw rho (ss_next (ax_S E_k10)) b5) [pRI rho])
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) (m9 b4) (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m10 b0) (B + 8192 + 4096)) 34 (rho_set_rw rho 33 b0) [pRI rho] [mkLeafA E_k11 RsCut] w)).
  rewrite N. change (eager_ok E_k10 4096 34) with S_k10ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b5; split; [exact HPL5|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run10_ok].
Qed.
End S10.

Lemma pRI_agree : ltac2:(tb__ "0|2|
S6S6S0S26Q40A1M0S5R1P1fM1A2S5R2G1A2A3S0G0S68R2A1S68R3A1A3F_;Frho';Frho;").
Proof. clear. intros rho rho' H. unfold pRI, shRI_base. cbn [eval]. rewrite H. reflexivity. Qed.

Definition B12 : Z := ltac2:(tb__ "0|0|
S2bS2bS2bS2bVB;Z2000A2Z1000A2Z10000A2Z3000A2").
Definition Post4b (rho : valuation) : assn := ltac2:(tb__ "0|4|
S8cS2S26Q40M0A1M1G1S2G1G1S2G1G1S2S36S36S2S6S6S1S5fS27G0Z0A2M2S67S6aR5A4S1S5fG2S69R5A1S27G0Z1000A2R4A4S1S5fG2S77R5R4A2S27G0Z10000A2R3A4S1S7aR2R3A2S1Sc1P1fM3Vrho;R1A3S1Sc3Vrho;R1A2S1S0S28S2eZ8S25G0S5R1G3A2A2A2S25G0S7fVP;A1A2A3S1S0G1S5R1P20A2R5A3S1S0G1S5R1P21A2R4A3S1S0G1S5R1P22A2R3A3S1S6dR1A1S1S6fR1A1S63S46S5eS7cR5R4R3A3S79A2Sa9R1S6bR1A1R6A6A2A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lhi;A2Lb6;A2Lb5;A2Lb4;A2Lw;").

Theorem seg4b : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1A3S0S28S25G0S5R5P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eVmP;VB;A2Sa1R6S35G1A1A5S75R6A1A4F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho H27 H28 H29 H30 Hv1.
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive)) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo in Htop; lia).
  eapply triple_seq; [apply (seg8a rho H27 H28 H29 H30 Hv1)|]. unfold Post8a.
  apply triple_ex; intros rho1. apply triple_pure; intros Hag1. apply triple_pure; intros RM1. apply triple_pure; intros V31.
  pose proof Hag1 as [A1 _].
  assert (H27a : rw rho1 27%positive = a1) by (rewrite (A1 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite (A1 28%positive) by lia; exact H28).
  assert (H29a : rw rho1 29%positive = P) by (rewrite (A1 29%positive) by lia; exact H29).
  assert (H30a : rw rho1 30%positive = spacebeg P) by (rewrite (A1 30%positive) by lia; exact H30).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (A1 1%positive) by lia; exact Hv1).

  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho2. apply triple_pure; intros Hag2.
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag2 ltac:(lia)) as H27b. rewrite H27a in H27b.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag2 ltac:(lia)) as H28b. rewrite H28a in H28b.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag2 ltac:(lia)) as H29b. rewrite H29a in H29b.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag2 ltac:(lia)) as H30b. rewrite H30a in H30b.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag2 ltac:(lia)) as H31b.
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag2 ltac:(lia)); exact Hv1a).
  assert (V31b : 8 * bv_unsigned (rw rho2 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31b; exact V31).
  rewrite <- (pRI_agree rho1 rho2 H31b).
  eapply triple_seq; [apply (seg9 rho2 H27b H28b H29b H30b V31b Hv1b)|].
  apply triple_ex; intros b4. apply triple_pure; intros HPL4.

  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho3. apply triple_pure; intros Hag3.
  assert (R9 : forall i, (i < 32)%positive -> rw (rho9 rho2 b4) i = rw rho2 i).
  { intros i Hi. unfold rho9, rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 32%positive); [lia | reflexivity]. }
  assert (R9_32 : rw (rho9 rho2 b4) 32%positive = b4) by (unfold rho9, rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag3 ltac:(lia)) as H27c. rewrite R9, H27b in H27c by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag3 ltac:(lia)) as H28c. rewrite R9, H28b in H28c by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag3 ltac:(lia)) as H29c. rewrite R9, H29b in H29c by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag3 ltac:(lia)) as H30c. rewrite R9, H30b in H30c by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag3 ltac:(lia)) as H31c. rewrite R9 in H31c by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag3 ltac:(lia)) as H32c. rewrite R9_32 in H32c.
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag3 ltac:(lia)), R9 by lia; exact Hv1b).
  assert (V31c : 8 * bv_unsigned (rw rho3 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31c; exact V31b).
  rewrite <- (pRI_agree rho2 rho3 H31c).
  eapply triple_seq; [apply (seg10 b4 HPL4 rho3 H27c H28c H29c H30c V31c H32c Hv1c)|].
  apply triple_ex; intros b5. apply triple_pure; intros HPL5.

  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho4. apply triple_pure; intros Hag4.
  assert (R10 : forall i, (i < 33)%positive -> rw (rho_set_rw rho3 33%positive b5) i = rw rho3 i).
  { intros i Hi. unfold rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 33%positive); [lia | reflexivity]. }
  assert (R10_33 : rw (rho_set_rw rho3 33%positive b5) 33%positive = b5) by (unfold rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag4 ltac:(lia)) as H27d. rewrite R10, H27c in H27d by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag4 ltac:(lia)) as H28d. rewrite R10, H28c in H28d by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag4 ltac:(lia)) as H29d. rewrite R10, H29c in H29d by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag4 ltac:(lia)) as H30d. rewrite R10, H30c in H30d by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag4 ltac:(lia)) as H31d. rewrite R10 in H31d by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag4 ltac:(lia)) as H32d. rewrite R10, H32c in H32d by lia.
  pose proof (rw_of_agree_below _ _ _ 33%positive Hag4 ltac:(lia)) as H33d. rewrite R10_33 in H33d.
  assert (Hv1d : bv_unsigned (rw rho4 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag4 ltac:(lia)), R10 by lia; exact Hv1c).
  assert (V31d : 8 * bv_unsigned (rw rho4 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31d; exact V31c).
  rewrite <- (pRI_agree rho3 rho4 H31d).
  eapply triple_seq; [apply (seg11a b4 HPL4 b5 HPL5 rho4 H27d H28d H29d H30d V31d H32d H33d Hv1d)|].
  apply triple_ex; intros b6. apply triple_pure; intros HPL6.

  pose proof (b6_facts b4 HPL4 b5 HPL5 b6 HPL6) as (F6lo & F6band & _).
  assert (HCLS : exists hi, clsZ hi b6).
  { unfold bandav in F6band. destruct F6band as [F|F]; [exists false | exists true]; unfold clsZ, SHADOW_BAND_LO, SHADOW_BAND_HI; lia. }
  destruct HCLS as [hi Hcls].
  set (rho5 := rho_set_rw rho4 34%positive b6).
  assert (R11 : forall i, (i < 34)%positive -> rw rho5 i = rw rho4 i).
  { intros i Hi. unfold rho5, rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 34%positive); [lia | reflexivity]. }
  assert (R11_34 : rw rho5 34%positive = b6) by (unfold rho5, rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).

  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    assert (X : SPA segsA (KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536)) (withX0 (S_k11c hi)) rho5 [pRI rho4] w).
    { split; [|exact Hk]. change (withX0 (S_k11c hi)) with (ax_add_facts [CLS11 hi] (withX0 S_k11ok)).
      apply smatchA_add_facts; [exact Hsm | | destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
      apply Forall_cons; [|apply Forall_nil]. apply (CLS11_holds hi b6 rho5 R11_34 Hcls). }
    exact X. }
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact (run11a hi) | apply OKFx | destruct hi; reflexivity | apply stableA_KxA]. }
  apply triple_ex; intros L. apply triple_ex; intros rho6. apply triple_pure; intros HinL. apply triple_pure; intros Hag6.
  destruct HinL as [<-|[]]. cbn [la_state].
  assert (N : ss_next (ax_S (withX0 (S_k11c hi))) = 35%positive) by (destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N in Hag6.
  change (fun w => smatchA segsA rho6 [pRI rho4] (L11mx hi) w /\ KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536) rho6 [pRI rho4] (w_tr w) (cfg_model (w_cfg w)))
    with (SPA segsA (KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536)) (L11mx hi) rho6 [pRI rho4]).
  eapply triple_conseq; [intros w Hw; pose proof (SPA_noX _ rho6 (L11mx hi) _ w Hw) as Hw'; rewrite L11m_eq in Hw'; exact Hw' | intros w Hw; exact Hw |].
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag6 ltac:(lia)) as H27e. rewrite R11, H27d in H27e by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag6 ltac:(lia)) as H28e. rewrite R11, H28d in H28e by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag6 ltac:(lia)) as H29e. rewrite R11, H29d in H29e by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag6 ltac:(lia)) as H30e. rewrite R11, H30d in H30e by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag6 ltac:(lia)) as H31e. rewrite R11 in H31e by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag6 ltac:(lia)) as H32e. rewrite R11, H32d in H32e by lia.
  pose proof (rw_of_agree_below _ _ _ 33%positive Hag6 ltac:(lia)) as H33e. rewrite R11, H33d in H33e by lia.
  pose proof (rw_of_agree_below _ _ _ 34%positive Hag6 ltac:(lia)) as H34e. rewrite R11_34 in H34e.
  assert (Hv1e : bv_unsigned (rw rho6 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag6 ltac:(lia)), R11 by lia; exact Hv1d).
  assert (V31e : 8 * bv_unsigned (rw rho6 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31e; exact V31d).
  rewrite <- (pRI_agree rho4 rho6 H31e).
  assert (HX1e : 0x7fff80000000 <= bv_unsigned (rw rho6 1%positive)) by (rewrite Hv1e, <- Hv1; exact HX1).
  change (B + 8192 + 4096 + 65536) with B11.
  eapply triple_conseq; [intros w Hw; exact (step11m b4 HPL4 b5 HPL5 b6 hi HPL6 Hcls rho6 w H27e H28e H29e H30e V31e H32e H33e H34e HX1e Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho7. apply triple_pure; intros Hag7. apply triple_pure; intros RM7. apply triple_pure; intros HZ7.
  rewrite <- (TP11_agree rho6 rho7 Hag7).
  assert (HX1f : 0x7fff80000000 <= bv_unsigned (rw rho7 1%positive)) by (rewrite (proj1 Hag7 1%positive) by lia; exact HX1e).
  eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg11b b4 b5 b6 hi rho7 HZ7 HX1f)].
  intros w (rho8 & Hag8 & RM8 & HZ8 & HD8 & Hsp). exists b4, b5, b6, hi, rho8.
  pose proof Hag7 as [A7 L7]. pose proof Hag8 as [A8 L8].
  split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|]. split; [exact Hcls|].
  assert (E6lo : forall i, (i < 31)%positive -> rw rho6 i = rw rho i).
  { intros i Hi. rewrite (rw_of_agree_below _ _ _ i Hag6) by lia. rewrite R11 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag4) by lia. rewrite R10 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag3) by lia. rewrite R9 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag2) by lia. apply A1. lia. }
  split.
  { split.
    - intros i Hi. rewrite (A8 i), (A7 i) by lia. apply E6lo. exact Hi.
    - intros l. rewrite (L8 l), (L7 l).
      destruct Hag6 as (_ & X6 & _). rewrite <- (X6 l). change (rl rho5 l) with (rl rho4 l).
      destruct Hag4 as (_ & X4 & _). rewrite <- (X4 l). change (rl (rho_set_rw rho3 33 b5) l) with (rl rho3 l).
      destruct Hag3 as (_ & X3 & _). rewrite <- (X3 l). change (rl (rho9 rho2 b4) l) with (rl rho2 l).
      destruct Hag2 as (_ & X2 & _). rewrite <- (X2 l). apply (proj2 Hag1). }
  split.
  {
    pose proof (b4_facts b4 HPL4) as (F4lo & _ & F4top & _).
    eapply RMH_trans; [| intros i Hi; rewrite (A7 i) by lia; apply E6lo; lia | exact RM8].
    eapply RMH_trans; [| intros i Hi; apply E6lo; lia | exact RM7].
    eapply RMH_below; [|exact Hag6]. unfold rho5. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag4]. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag3]. unfold rho9. apply RMH_set_rw. apply RMH_unmap.
    2:{ unfold n9. rewrite (u64_of_lit 0x800000) by lia. rewrite Hv1.
        revert F4top. unfold alloc_top. rewrite stack_max_size_val. intros F4top. lia. }
    eapply RMH_below; [|exact Hag2]. exact RM1. }
  split; [rewrite (A8 31%positive), (A7 31%positive) by lia; exact V31e|].
  split; [rewrite (A8 32%positive), (A7 32%positive) by lia; exact H32e|].
  split; [rewrite (A8 33%positive), (A7 33%positive) by lia; exact H33e|].
  split; [rewrite (A8 34%positive), (A7 34%positive) by lia; exact H34e|].
  split; [exact HZ8|]. split; [exact HD8|].
  unfold B12. change (B + 8192 + 4096 + 65536) with B11. rewrite (TP11_agree rho7 rho8 Hag8). exact Hsp.
Qed.

Hypothesis Hwit9 : ltac2:(tb__ "0|2|
S2S26Q40M0A1M1G1S5fS27G0Z0A2S67S6aR1A4La;A2").
Lemma eseg9 : ltac2:(tb__ "0|5|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1M2A3S0S28S2eZ8S25G0S5R5P1fA2A2A2S25G0G2A2A3S0S28S25G0S5R6P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eS67S2bVB;Z2000A2M3A2SabR7S34G1S68R7A1S35G1A1M4A3A5S8cS2G1G1S1S5fS27G0Z0A2S67S6aR1A4S64S46S5eS69R1A1G3A2P21S78R9R1A2S34G1S68R9A1G4A3S34S86S87Sa4Sc6A2S35S86A1A3R2A7A2Lb4;A2Lw;A3F_;F_;F_;F_;F_;F_;Frho;").
Proof using HPL Hmaps Hres Htop Hlz Hwit9.
  clear Ha1 Ha2 HBlim. intros rho H27 H28 H29 H30 H31 Hv1. pose proof m8_ledger as (L1 & L2 & L3 & L4 & L5).
  eapply etriple_seq.
  { apply (lazy_null_none_enode E_k9 0x800000 m8 (B + 8192) G9 33%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear9.
    + rewrite L1. exact Hres.
    + exact init_sp_ok_m8.
    + exact band_m8.
    + intros rho0 a. unfold rho9.
      assert (N : ss_next (ax_S E_k9) = 32%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      apply (agree_below_set_rw _ 32%positive a 32%positive). lia.
    + intros rho0 a. unfold rho9.
      assert (N : ss_next (ax_S E_k9) = 32%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N. apply rho_set_rw_at.
    + exact Hwit9.
    + apply (HG9 rho _ H27 H28 H30 H31). exists []. reflexivity.
    + rewrite L4. exact Hv1. }
  apply etriple_ex; intros b4. intros w [HPL4 Hsp]. revert w Hsp.
  change (etriple segsA (SPA segsA (KxA (m9 b4) (B + 8192)) S_k9ok (rho9 rho b4) [pRI rho])
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) m8 n9 b0 /\ LQA segsA (KxA (m9 b0) (B + 8192)) 33 (rho9 rho b0) [pRI rho] [mkLeafA E_k10 RsCut] w)).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b4; split; [exact HPL4|exact Hw] |].
  eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run9_ok].
Qed.

Hypothesis Hwit10g : ltac2:(tb__ "0|3|
S26Q40M0A1M1S5fS27G0Z0A2M2S67S6aR1A4S2G1G1S5fG2S69R3A1S27G0Z1000A2R1A4La;A2F_;Fb4;").
Hypothesis Hwit11g : ltac2:(tb__ "0|3|
S26Q40M0A1M1G1S5fS27G0Z0A2M2S67S6aR2A4S5fG2S69R3A1S27G0Z1000A2R2A4S2G1G1S5fG2S77R5R4A2S27G0Z10000A2R1A4La;A2F_;F_;Fb5;Fb4;").

Theorem eseg4b : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0G1S5R3P1dA2VP;A3S0G1S5R4P1eA2S7fVP;A1A3S0S28S25G0S5R5P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eVmP;VB;A2Sa1R6S35G1A1A5S75R6A1A3F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL Ha1 Ha2 Hmaps Hna Hres Htop Hlz Hwit9 Hwit10g Hwit11g.
  intros rho H27 H28 H29 H30 Hv1.
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive)) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo in Htop; lia).
  eapply etriple_seq; [apply (eseg8a rho H27 H28 H29 H30 Hv1)|]. unfold Post8a.
  apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1. apply etriple_pure; intros RM1. apply etriple_pure; intros V31.
  pose proof Hag1 as [A1 _].
  assert (H27a : rw rho1 27%positive = a1) by (rewrite (A1 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite (A1 28%positive) by lia; exact H28).
  assert (H29a : rw rho1 29%positive = P) by (rewrite (A1 29%positive) by lia; exact H29).
  assert (H30a : rw rho1 30%positive = spacebeg P) by (rewrite (A1 30%positive) by lia; exact H30).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (A1 1%positive) by lia; exact Hv1).

  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho2. apply etriple_pure; intros Hag2.
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag2 ltac:(lia)) as H27b. rewrite H27a in H27b.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag2 ltac:(lia)) as H28b. rewrite H28a in H28b.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag2 ltac:(lia)) as H29b. rewrite H29a in H29b.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag2 ltac:(lia)) as H30b. rewrite H30a in H30b.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag2 ltac:(lia)) as H31b.
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag2 ltac:(lia)); exact Hv1a).
  assert (V31b : 8 * bv_unsigned (rw rho2 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31b; exact V31).
  rewrite <- (pRI_agree rho1 rho2 H31b).
  eapply etriple_seq; [apply (eseg9 rho2 H27b H28b H29b H30b V31b Hv1b)|].
  apply etriple_ex; intros b4. apply etriple_pure; intros HPL4.

  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3.
  assert (R9 : forall i, (i < 32)%positive -> rw (rho9 rho2 b4) i = rw rho2 i).
  { intros i Hi. unfold rho9, rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 32%positive); [lia | reflexivity]. }
  assert (R9_32 : rw (rho9 rho2 b4) 32%positive = b4) by (unfold rho9, rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag3 ltac:(lia)) as H27c. rewrite R9, H27b in H27c by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag3 ltac:(lia)) as H28c. rewrite R9, H28b in H28c by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag3 ltac:(lia)) as H29c. rewrite R9, H29b in H29c by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag3 ltac:(lia)) as H30c. rewrite R9, H30b in H30c by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag3 ltac:(lia)) as H31c. rewrite R9 in H31c by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag3 ltac:(lia)) as H32c. rewrite R9_32 in H32c.
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag3 ltac:(lia)), R9 by lia; exact Hv1b).
  assert (V31c : 8 * bv_unsigned (rw rho3 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31c; exact V31b).
  rewrite <- (pRI_agree rho2 rho3 H31c).
  eapply etriple_seq; [apply (eseg10 b4 HPL4 (Hwit10g b4 HPL4) rho3 H27c H28c H29c H30c V31c H32c Hv1c)|].
  apply etriple_ex; intros b5. apply etriple_pure; intros HPL5.

  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho4. apply etriple_pure; intros Hag4.
  assert (R10 : forall i, (i < 33)%positive -> rw (rho_set_rw rho3 33%positive b5) i = rw rho3 i).
  { intros i Hi. unfold rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 33%positive); [lia | reflexivity]. }
  assert (R10_33 : rw (rho_set_rw rho3 33%positive b5) 33%positive = b5) by (unfold rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag4 ltac:(lia)) as H27d. rewrite R10, H27c in H27d by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag4 ltac:(lia)) as H28d. rewrite R10, H28c in H28d by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag4 ltac:(lia)) as H29d. rewrite R10, H29c in H29d by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag4 ltac:(lia)) as H30d. rewrite R10, H30c in H30d by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag4 ltac:(lia)) as H31d. rewrite R10 in H31d by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag4 ltac:(lia)) as H32d. rewrite R10, H32c in H32d by lia.
  pose proof (rw_of_agree_below _ _ _ 33%positive Hag4 ltac:(lia)) as H33d. rewrite R10_33 in H33d.
  assert (Hv1d : bv_unsigned (rw rho4 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag4 ltac:(lia)), R10 by lia; exact Hv1c).
  assert (V31d : 8 * bv_unsigned (rw rho4 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31d; exact V31c).
  rewrite <- (pRI_agree rho3 rho4 H31d).
  eapply etriple_seq; [apply (eseg11a b4 HPL4 b5 HPL5 (Hwit11g b4 b5 HPL4 HPL5) rho4 H27d H28d H29d H30d V31d H32d H33d Hv1d)|].
  apply etriple_ex; intros b6. apply etriple_pure; intros HPL6.
  pose proof (b6_facts b4 HPL4 b5 HPL5 b6 HPL6) as (F6lo & F6band & _).
  assert (HCLS : exists hi, clsZ hi b6).
  { unfold bandav in F6band. destruct F6band as [F|F]; [exists false | exists true]; unfold clsZ, SHADOW_BAND_LO, SHADOW_BAND_HI; lia. }
  destruct HCLS as [hi Hcls].
  set (rho5 := rho_set_rw rho4 34%positive b6).
  assert (R11 : forall i, (i < 34)%positive -> rw rho5 i = rw rho4 i).
  { intros i Hi. unfold rho5, rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i 34%positive); [lia | reflexivity]. }
  assert (R11_34 : rw rho5 34%positive = b6) by (unfold rho5, rho_set_rw; cbn [rw]; rewrite Pos.eqb_refl; reflexivity).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w [Hsm Hk].
    assert (X : SPA segsA (KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536)) (withX0 (S_k11c hi)) rho5 [pRI rho4] w).
    { split; [|exact Hk]. change (withX0 (S_k11c hi)) with (ax_add_facts [CLS11 hi] (withX0 S_k11ok)).
      apply smatchA_add_facts; [exact Hsm | | destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
      apply Forall_cons; [|apply Forall_nil]. apply (CLS11_holds hi b6 rho5 R11_34 Hcls). }
    exact X. }
  eapply etriple_seq.
  { eapply sym_run_etripleA; [destruct hi; reflexivity | apply stableA_KxA | exact (run11a hi)]. }
  apply etriple_ex; intros L. apply etriple_ex; intros rho6. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag6.
  destruct HinL as [<-|[]]. cbn [la_state].
  assert (N : ss_next (ax_S (withX0 (S_k11c hi))) = 35%positive) by (destruct hi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N in Hag6.
  change (fun w => smatchA segsA rho6 [pRI rho4] (L11mx hi) w /\ KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536) rho6 [pRI rho4] (w_tr w) (cfg_model (w_cfg w)))
    with (SPA segsA (KxA (m11 b4 b5 b6) (B + 8192 + 4096 + 65536)) (L11mx hi) rho6 [pRI rho4]).
  eapply etriple_conseq; [intros w Hw; pose proof (SPA_noX _ rho6 (L11mx hi) _ w Hw) as Hw'; rewrite L11m_eq in Hw'; exact Hw' | intros w Hw; exact Hw |].
  pose proof (rw_of_agree_below _ _ _ 27%positive Hag6 ltac:(lia)) as H27e. rewrite R11, H27d in H27e by lia.
  pose proof (rw_of_agree_below _ _ _ 28%positive Hag6 ltac:(lia)) as H28e. rewrite R11, H28d in H28e by lia.
  pose proof (rw_of_agree_below _ _ _ 29%positive Hag6 ltac:(lia)) as H29e. rewrite R11, H29d in H29e by lia.
  pose proof (rw_of_agree_below _ _ _ 30%positive Hag6 ltac:(lia)) as H30e. rewrite R11, H30d in H30e by lia.
  pose proof (rw_of_agree_below _ _ _ 31%positive Hag6 ltac:(lia)) as H31e. rewrite R11 in H31e by lia.
  pose proof (rw_of_agree_below _ _ _ 32%positive Hag6 ltac:(lia)) as H32e. rewrite R11, H32d in H32e by lia.
  pose proof (rw_of_agree_below _ _ _ 33%positive Hag6 ltac:(lia)) as H33e. rewrite R11, H33d in H33e by lia.
  pose proof (rw_of_agree_below _ _ _ 34%positive Hag6 ltac:(lia)) as H34e. rewrite R11_34 in H34e.
  assert (Hv1e : bv_unsigned (rw rho6 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (rw_of_agree_below _ _ _ 1%positive Hag6 ltac:(lia)), R11 by lia; exact Hv1d).
  assert (V31e : 8 * bv_unsigned (rw rho6 31%positive) = bv_unsigned (spacebeg P)) by (rewrite H31e; exact V31d).
  rewrite <- (pRI_agree rho4 rho6 H31e).
  assert (HX1e : 0x7fff80000000 <= bv_unsigned (rw rho6 1%positive)) by (rewrite Hv1e, <- Hv1; exact HX1).
  change (B + 8192 + 4096 + 65536) with B11.
  eapply etriple_conseq; [intros w Hw; exact (step11m b4 HPL4 b5 HPL5 b6 hi HPL6 Hcls rho6 w H27e H28e H29e H30e V31e H32e H33e H34e HX1e Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho7. apply etriple_pure; intros Hag7. apply etriple_pure; intros RM7. apply etriple_pure; intros HZ7.
  rewrite <- (TP11_agree rho6 rho7 Hag7).
  assert (HX1f : 0x7fff80000000 <= bv_unsigned (rw rho7 1%positive)) by (rewrite (proj1 Hag7 1%positive) by lia; exact HX1e).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (eseg11b b4 b5 b6 hi rho7 HZ7 HX1f)].
  intros w (rho8 & Hag8 & RM8 & HZ8 & HD8 & Hsp). exists b4, b5, b6, hi, rho8.
  pose proof Hag7 as [A7 L7]. pose proof Hag8 as [A8 L8].
  split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|]. split; [exact Hcls|].
  assert (E6lo : forall i, (i < 31)%positive -> rw rho6 i = rw rho i).
  { intros i Hi. rewrite (rw_of_agree_below _ _ _ i Hag6) by lia. rewrite R11 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag4) by lia. rewrite R10 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag3) by lia. rewrite R9 by lia.
    rewrite (rw_of_agree_below _ _ _ i Hag2) by lia. apply A1. lia. }
  split.
  { split.
    - intros i Hi. rewrite (A8 i), (A7 i) by lia. apply E6lo. exact Hi.
    - intros l. rewrite (L8 l), (L7 l).
      destruct Hag6 as (_ & X6 & _). rewrite <- (X6 l). change (rl rho5 l) with (rl rho4 l).
      destruct Hag4 as (_ & X4 & _). rewrite <- (X4 l). change (rl (rho_set_rw rho3 33 b5) l) with (rl rho3 l).
      destruct Hag3 as (_ & X3 & _). rewrite <- (X3 l). change (rl (rho9 rho2 b4) l) with (rl rho2 l).
      destruct Hag2 as (_ & X2 & _). rewrite <- (X2 l). apply (proj2 Hag1). }
  split.
  { pose proof (b4_facts b4 HPL4) as (F4lo & _ & F4top & _).
    eapply RMH_trans; [| intros i Hi; rewrite (A7 i) by lia; apply E6lo; lia | exact RM8].
    eapply RMH_trans; [| intros i Hi; apply E6lo; lia | exact RM7].
    eapply RMH_below; [|exact Hag6]. unfold rho5. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag4]. apply RMH_set_rw.
    eapply RMH_below; [|exact Hag3]. unfold rho9. apply RMH_set_rw. apply RMH_unmap.
    2:{ unfold n9. rewrite (u64_of_lit 0x800000) by lia. rewrite Hv1.
        revert F4top. unfold alloc_top. rewrite stack_max_size_val. intros F4top. lia. }
    eapply RMH_below; [|exact Hag2]. exact RM1. }
  split; [rewrite (A8 31%positive), (A7 31%positive) by lia; exact V31e|].
  split; [rewrite (A8 32%positive), (A7 32%positive) by lia; exact H32e|].
  split; [rewrite (A8 33%positive), (A7 33%positive) by lia; exact H33e|].
  split; [rewrite (A8 34%positive), (A7 34%positive) by lia; exact H34e|].
  split; [exact HZ8|]. split; [exact HD8|].
  unfold B12. change (B + 8192 + 4096 + 65536) with B11. rewrite (TP11_agree rho7 rho8 Hag8). exact Hsp.
Qed.

End WithP.

Definition Post4 (rho : valuation) : assn := ltac2:(tb__ "0|3|
S8cS2S26Q40M0A1M1G1S2S6S6S1S5fS27G0Z0A2Vm;S91R2A4S1Sc1P1dM2Vrho;R1A3S1Sc3Vrho;R1A2S1S0G1S5R1G2A2R2A3S1S0G1S5R1P1eA2S7fR2A1A3S99R2R1R3A3A2A2A2A2A2Lrho1;A2LP;A2Lw;").

Theorem start4_sum_A : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0S28S25G0S5R3P1A2A2S25G0S48S47Vm;A1A1A2A3S8eS46Vok;S63S46S5eVm;VB;A2ScfR4S35G1A1A5S96R4A1A4F_;F_;F_;Frho;").
Proof using All.
  intros rho H27 H28 Hv1.
  eapply triple_seq; [apply (seg7 rho H27 H28 Hv1)|].
  apply triple_ex; intros P. apply triple_pure; intros HPL.
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros HinL. apply triple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  pose proof (P_facts P HPL) as (Pal & Pceil & _ & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  pose proof Hag1 as (V & Lq & Rm).
  assert (H29 : rw rho1 29%positive = P).
  { rewrite <- (V 29%positive) by lia. unfold rho7. rewrite rho_set_rw_other by discriminate. apply rho_set_rw_at. }
  assert (H30 : rw rho1 30%positive = spacebeg P).
  { rewrite <- (V 30%positive) by lia. unfold rho7. apply rho_set_rw_at. }
  assert (A1 : agree_vars 29%positive rho rho1).
  { split; [|intros l; rewrite <- (Lq l); reflexivity]. intros i Hi. rewrite <- (V i) by lia. unfold rho7. rewrite !rho_set_rw_other by lia. reflexivity. }
  assert (H27a : rw rho1 27%positive = a1) by (rewrite (proj1 A1 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite (proj1 A1 28%positive) by lia; exact H28).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (proj1 A1 1%positive) by lia; exact Hv1).
  change (fun w => smatchA segsA rho1 [] E_k8 w /\ KxA (m7 P) B rho1 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA (m7 P) B) E_k8 rho1 []).
  eapply triple_conseq; [intros w Hw; exact (restate8 P rho1 w H29 H30 Pal PLB ltac:(lia) Hw) | | apply (seg4b P HPL rho1 H27a H28a H29 H30 Hv1a)].
  intros w Hw. exists P, rho1. split; [exact HPL|]. split; [exact A1|]. split; [|split; [exact H29 | split; [exact H30 | exact Hw]]].
  eapply RMH_below; [|exact Hag1]. unfold rho7. apply RMH_set_rw. apply RMH_set_rw. apply RMH_unmap; [apply RMH_refl|].
  unfold n7. rewrite (u64_of_lit 0x2000011000) by lia. rewrite Hv1. revert Pceil. unfold alloc_top. rewrite stack_max_size_val. intros Pceil. lia.
Qed.

Hypothesis Hwit7 : ltac2:(tb__ "0|2|
S2S26Q40M0A1M1G1S5fS27G0Z0A2Vm;S91R1A4LP;A2").
Lemma eseg7 : ltac2:(tb__ "0|3|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0S28S25G0S5R3P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eVm;VB;A2ScfR4S35G1A1M2A5S8cS2G1G1S1S5fS27G0Z0A2Vm;S91R1A4S64S46S5eS92R1A1VB;A2P1fS98R6R1A2G2S34S86S87SaaSc6A2S35S86A1A3R2A7A2LP;A2Lw;A3F_;F_;F_;Frho;").
Proof using Hmaps Hres Htop Hwit7.
  clear Ha1 Ha2 HBlim. intros rho H27 H28 Hv1.
  eapply etriple_seq.
  { apply (lazy_null_none_enode E_k7 0x2000011000 m B G4 31%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear7.
    + exact Hres.
    + exact Htop.
    + exact Hband.
    + intros rho0 a. unfold rho7.
      assert (N : ss_next (ax_S E_k7) = 29%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      eapply agree_below_trans; [apply (agree_below_set_rw _ 29%positive a 29%positive); lia | apply (agree_below_set_rw _ 30%positive (spacebeg a) 29%positive); lia].
    + intros rho0 a. unfold rho7.
      assert (N : ss_next (ax_S E_k7) = 29%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite N.
      rewrite rho_set_rw_other by discriminate. apply rho_set_rw_at.
    + exact Hwit7.
    + exact (HG4 rho H27 H28).
    + exact Hv1. }
  apply etriple_ex; intros P. intros w [HPL Hsp]. revert w Hsp.
  change (etriple segsA (SPA segsA (KxA (m7 P) B) S_k7ok (rho7 rho P) [])
            (fun w => exists P0, mmap_place_ok_none (Z_to_bv 64 0) m n7 P0 /\ LQA segsA (KxA (m7 P0) B) 31 (rho7 rho P0) [] [mkLeafA E_k8 RsCut] w)).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists P; split; [exact HPL|exact Hw] |].
  eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run7_ok].
Qed.

Hypothesis Hwit9g : ltac2:(tb__ "0|3|
S26Q40M0A1M1S5fS27G0Z0A2M2Vm;S91R1A4S2G1G1S5fG2S93R3A1S94R1A4La;A2F_;FP;").
Hypothesis Hwit10g : ltac2:(tb__ "0|3|
S26Q40M0A1M1G1S5fS27G0Z0A2M2Vm;S91R2A4S5fG2S93R3A1S94R2A4S2G1G1S5fG2S97R5R4A2S27G0Z1000A2R1A4La;A2F_;F_;Fb4;FP;").
Hypothesis Hwit11g : ltac2:(tb__ "0|3|
S26Q40M0A1M1G1G1S5fS27G0Z0A2M2Vm;S91R3A4S5fG2S93R4A1S94R3A4S5fG2S97R5R4A2S27G0Z1000A2R3A4S2G1G1S5fG2S9aR7R6R5A3S27G0Z10000A2R1A4La;A2F_;F_;F_;Fb5;Fb4;FP;").

Theorem start4_sum_ex_A : ltac2:(tb__ "0|2|
S6S0S26Q40M0A1M1S5R1P1bA2Va1;A3S0G1S5R2P1cA2Va2;A3S0S28S25G0S5R3P1A2A2S25G0S48S47Vm;A1A1A2A3S8dS46S63S46S5eVm;VB;A2ScfR4S35G1A1A5S96R4A1A3F_;F_;F_;Frho;").
Proof using HBlim Ha1 Ha2 Hmaps Hna Hres Htop Hlz Hwit7 Hwit9g Hwit10g Hwit11g.
  intros rho H27 H28 Hv1.
  eapply etriple_seq; [apply (eseg7 rho H27 H28 Hv1)|].
  apply etriple_ex; intros P. apply etriple_pure; intros HPL.
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state].
  pose proof (P_facts P HPL) as (Pal & Pceil & _ & PLB & Phi). unfold alloc_ceiling_hi in Phi.
  pose proof Hag1 as (V & Lq & Rm).
  assert (H29 : rw rho1 29%positive = P).
  { rewrite <- (V 29%positive) by lia. unfold rho7. rewrite rho_set_rw_other by discriminate. apply rho_set_rw_at. }
  assert (H30 : rw rho1 30%positive = spacebeg P).
  { rewrite <- (V 30%positive) by lia. unfold rho7. apply rho_set_rw_at. }
  assert (A1 : agree_vars 29%positive rho rho1).
  { split; [|intros l; rewrite <- (Lq l); reflexivity]. intros i Hi. rewrite <- (V i) by lia. unfold rho7. rewrite !rho_set_rw_other by lia. reflexivity. }
  assert (H27a : rw rho1 27%positive = a1) by (rewrite (proj1 A1 27%positive) by lia; exact H27).
  assert (H28a : rw rho1 28%positive = a2) by (rewrite (proj1 A1 28%positive) by lia; exact H28).
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m))) by (rewrite (proj1 A1 1%positive) by lia; exact Hv1).
  change (fun w => smatchA segsA rho1 [] E_k8 w /\ KxA (m7 P) B rho1 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA (KxA (m7 P) B) E_k8 rho1 []).
  eapply etriple_conseq; [intros w Hw; exact (restate8 P rho1 w H29 H30 Pal PLB ltac:(lia) Hw) | |
    apply (eseg4b P HPL (Hwit9g P HPL) (fun b4 H4 => Hwit10g P b4 HPL H4) (fun b4 b5 H4 H5 => Hwit11g P b4 b5 HPL H4 H5) rho1 H27a H28a H29 H30 Hv1a)].
  intros w Hw. exists P, rho1. split; [exact HPL|]. split; [exact A1|]. split; [|split; [exact H29 | split; [exact H30 | exact Hw]]].
  eapply RMH_below; [|exact Hag1]. unfold rho7. apply RMH_set_rw. apply RMH_set_rw. apply RMH_unmap; [apply RMH_refl|].
  unfold n7. rewrite (u64_of_lit 0x2000011000) by lia. rewrite Hv1. revert Pceil. unfold alloc_top. rewrite stack_max_size_val. intros Pceil. lia.
Qed.

End Seg4.
End Start4.

(* [comment removed for export] *)
Module Lib_realloc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "list"; "None"; "nat"; "false"; "app"; "bool"; "true"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "SPUle"; "cell"; "mkCell"; "sobj"; "SAlu"; "mkObj"; "valuation"; "DUnknown"; "SPAlign"; "SPBranch"; "FcsrFrm0"; "mkSS"; "DImage"; "SPNot"; "SPEq"; "eval"; "ss_next"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "rw"; "ss_facts"; "sv_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "mkAX"; "ax_X"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "leavesA_at"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "JA"; "JLA"; "ejcertA"; "ffinA"; "nodeIA"; "ok_frameKA"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc"; "ndR"; "vNS"; "tv0"; "vA"; "vOS"; "vPn"; "P0_ra"; "vP"; "E_m"; "bd0"; "c8"; "vD"; "z0"; "E_f"; "bd1"; "s_f"; "s_m"; "Pre_ra"; "R_m"; "tv1"; "O_D"; "O_F"; "O_al"; "Pre_m"; "R_f"; "pN"; "ra_facts"; "FUEL_ra"; "O_old"; "P_fail"; "P_ok"; "Pre_f"; "T_free"; "T_mnull"; "cutpcs_ra"; "cutsE"; "exitsE"; "spm"; "tvP"; "two40"; "two47"; "C_L"; "C_L_S"; "E_f_S"; "O_new"; "P_ok_S"; "T_mok"; "T_mok0"; "cp_var"; "ok_facts"; "pre_regs_ra"; "tv2"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "ulink"; "L_free"; "unwind_stopJ"; "JL_free"; "J_alloc_pre"; "J_free_pre"; "L_malloc_null"; "L_malloc_ok"; "NPOSTM"; "Posts_malloc"; "Pre_free"; "Pre_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "opp"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "uval"; "BIc"; "BIs"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc.Sum"; "Posts_ra"; "JL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "site_okA"; "cmaddrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc.ReallocAddr"; "ra_ret"; "free_pc"; "malloc_pc"; "ra_L"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ReallocAddr.
  Definition ra_entry : Z := 0xa6338.
  Definition ra_L : Z := 0xa65a0.
  Definition ra_ret : Z := 0xa6490.
  Definition ra_malloc_ret : Z := 0xa656c.
  Definition ra_free_ret : Z := 0xa6634.
  Definition malloc_pc : Z := 0x5e060.
  Definition free_pc : Z := 0x5e05c.
  Definition thunk_alloc : Z := 0x8c86c.
  Definition thunk_calloc : Z := 0x8c878.
  Definition thunk_free : Z := 0x8c88c.
End ReallocAddr.
Import ReallocAddr.

Definition FUEL_ra : nat := 400%nat.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition vA : sv := SVar 12. Definition vP : sv := SVar 13. Definition vOS : sv := SVar 14. Definition vNS : sv := SVar 33.
Definition vD : sv := SVar 19. Definition vUD : sv := SVar 52.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S17S32S10PaA1S11Sa1Vk;A1A1A3").

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S10PaA1S11N60A1S11Z0A1Vcells;S1aA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S18S6aZ60A1S50S11Z0A1S2S14A1S1aA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S18S48S11Z0M0A1M1S11Z30A1S0S14S4fG0S11Sc2A1A2S0S14S4fZ8S11Sc3A1A2S0S14S4fZ10G1A2S0S14S4fZ18S11Sc4A1A2S0S14S4fZ20G1A2S0S14S4fZ28S79A2S2S14A1A3A3A3A3A3A3S1aA5").
Definition O_old : sobj := ltac2:(tb__ "0|0|
S18S4cS11Z0A1S49S2S14A1S1aA5").

Definition ra_facts : list sprop := ltac2:(tb__ "0|a|
S0S12S1bPaM0Z4M1A2S0S12S13S10G0A1M2S11S6dA1M3A2S0S12S13S10P1eA1M4S17S32S6aZ60A1M5S50A3A2S0S12S13G4G5A2S0S12S13G4G2A2S0S12S1cS33S11N1000A1S50A3S0S12S1cS33S50S11Sa1S6cA1A1A3S0S12S1bPcZ3A2S0S12S13S11Z1000A1M6S48A2S0S12S13S17S32S48S11Z30A1A3G4A2S0S12S13S48G3A2S0S12S1bPdG1A2S0S12S13G6S4cA2S0S12S13S17S32S4cS49A3G4A2S0S12S13S4cG3A2S0S12S13S11Z1A1M7S49A2S0S12S13S49S11S6cA1M8A2S0S12S13G7S46A2S0S12S13S46G8A2S0S12S13S46S11ZffffffffA1A2S0S12S13S11Z7fff7f800000A1M9G4A2S0S12S13G4S11Z7fffff800000A1A2S0S12S13G9G2A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_ra : list sv := ltac2:(tb__ "0|1|
S7cS7eS0S3S6SfA2M0S1S6SfUeS11Z10A1A4S2G0A1A3A2").
Definition X_ra : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS48S11Z30A1A4S0G0S1SfSfS4cS49A4S2G0A1A3A3").
Definition Pre_ra_S : sstate := ltac2:(tb__ "0|0|
S1eSc1S77S7bS1dS5SfA1S8S16S0S16S5aS2S14A1A1S0S16S59S0S16S5bS0S16S61S2S16A1A3A3A3A3S37A3S5fS7aS7A9").
Definition Pre_ra : axst := mkA Pre_ra_S X_ra.

Definition cutpcs_ra : list Z := ltac2:(tb__ "0|0|
S0S2cSc0S0S2cSbfS0S2cSbeS2S2cA1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_ra end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
ScbS2eVk;S38S60S67VS;Vpc;A4S56A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : axst := Eval vm_compute in leafA_at Pre_ra malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S2dSfA2S1S2dSfPfS50A4Sc5PaS2fS4dA1S2fS5cA1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).

Definition pN : positive := pos_add_nat (ss_next (ax_S E_m)) 10.
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := ltac2:(tb__ "0|0|
S44S1SfSfS10S5eA1S46A4A1").
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition C_L_S : sstate := ltac2:(tb__ "0|29|
S1eZa65a0S0SfS11Z0A1M0S0SfS11Za656cA1S0SfS17S32S10PaM1A1M2S11N60A1M3A3M4S0SfS10P17A1S0SfS10P18A1S0SfS17S32S10P6fM5A1M6S10P96A1M7A3M8S0SfS10P98A1S0SfS10P99A1S0SfS17S32S10PcM9A1MaS11Z18A1MbA3McS0SfS17S32GaS11Z28A1MdA3S0SfG6S0SfS10PdMeA1MfS0SfS10PeA1M10S0SfGaS0SfS17S32GfG7A3M11S0SfG8S0SfS10P97A1M12S0SfG11S0SfS10P21A1M13S0SfS11Z7fff8000A1M14S0SfS17S32S10P64A1M15G14A3S0SfS17S32G15S11Z7fff8003A1A3S0SfS17S32G15S11Z7fff8005A1A3S0SfGaS0SfG13S0SfG10S0SfGfS0SfS10P2fA1S0SfS10P9aA1S0SfS10P9bA1S0SfS10P9cA1S0SfS10P9dA1S2SfA1M16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0SfS10P3cA1S0SfS10P3dA1S0SfS10P3eA1S0SfS10P3fA1S0SfS10P40A1S0SfS10P41A1S0SfS10P42A1S0SfS10P43A1S0SfS10P44A1S0SfS10P45A1S0SfS10P46A1S0SfS10P47A1S0SfS10P48A1S0SfS10P49A1S0SfS10P4aA1S0SfS10P4bA1S0SfS10P4cA1S0SfS10P4dA1S0SfS10P4eA1S0SfS10P4fA1S0SfS10P50A1S0SfS10P51A1S0SfS10P52A1S0SfS10P53A1S0SfS10P54A1S0SfS10P55A1S0SfS10P56A1S0SfS10P57A1S0SfS10P58A1S0SfS10P59A1S0SfS10P5aA1S0SfS10P5bA1G16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S1dS5SfA1S0S16S18G4S10P13A1M17G0S2S14A1M18S1aA5S0S16S18G6G0G13G18S1aA5S0S16S18G0S11Ze7bd8A1S11Ze8978A1G18S1fA5S0S16S18G0S11Zf13f8A1M19S11Zf1404A1S0S14S15G19Z8M1aG14A3S0S14S15S11Zf1400A1Z4M1bS11Z1A1M1cA3G18A3A3S1fA5S0S16S18G2G3G0S0S14S15G3G1aS10P2eA1A3S0S14S15S11N58A1G1aS10P2dA1A3S0S14S15S11N50A1G1aS10P2cA1A3S0S14S15S11N48A1G1aS10P2bA1A3S0S14S15S11N40A1G1aS10P2aA1A3S0S14S15S11N38A1G1aS10P29A1A3S0S14S15S11N30A1G1aS10P28A1A3S0S14S15S11N28A1G1aS10P27A1A3S0S14S15S11N20A1G1aS10P26A1A3S0S14S15S11N18A1G1aS10P1dA1A3S0S14S15S11N10A1G1aS10P1cA1A3S0S14S15S11N8A1G1aS10PbA1A3G18A3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S16S18GaG0S11Z30A1M1dS0S14S15G0G1aS11Z8c86cA1A3S0S14S15S11G1aA1G1aS11Z8c878A1A3S0S14S15S11Z10A1G1aG0A3S0S14S15GbG1aS11Z8c88cA1A3S0S14S15S11Z20A1G1aG0A3S0S14S15GdG1aS10P34A1A3G18A3A3A3A3A3A3S1aA5S0S16S18GfG0G10G18S1aA5S2S16A1A3A3A3A3A3A3A3S0S12S13S17S32G7G12A3M1eG10A2S0S12S13G1eG13A2S0S12S13G1cG12A2S0S12S13G12S11Z10000000000A1M1fA2S0S12S13G7G1fA2S0S12S13G6S10P1eA1M20A2S0S12S13G13G20A2S0S12S21S17S35G15S11Z3M21A1A3M22GaA2S0S12S13G15S11Z1fffffffffffffffA1A2S0S12S13G22GaA2S0S12S13GaG22A2S0S12S1bG1G1bA2S0S12S13G2S11Z800000000000A1M23A2S0S12S13G20G2A2S0S12S13G20S17S32G4G17A3A2M24S0S12S13G20G4A2S0S12S1cS33S11N1000A1G17A3M25S0S12S1cS33G17S11N10000000000A1A3M26S0S12S1bG9G21A2S0S12S13S11Z1000A1M27GaA2S0S12S13S17S32GaG1dA3G20A2S0S12S13GaG23A2S0S12S1bGeG1bA2S0S12S13G27GfA2S0S12S13S17S32GfG10A3G20A2S0S12S13GfG23A2S0S12S13G1cG10A2S0S12S13G10G1fA2S0S12S13G1cG13A2S0S12S13G13G1fA2S0S12S13G13S11ZffffffffA1A2S0S12S1bG5G1bA2S0S12S20S1cS34G6G0A3A1S0S12S13G27G6A2S0S12S13S11Z646000A1G6A2S0S12S13S17S32G6G13A3G20A2S0S12S13GcG4A2S0S12G24S0S12G25S0S12G26S0S12S13S11Z7fff7f800000A1M28G20A2S0S12S13G20S11Z7fffff800000A1A2S0S12S13G28G2A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Pa0S7A9").
Definition C_L : axst := ltac2:(tb__ "0|1|
S30S6fS0S3SfSfA2M0S1SfSfS10PcA1S11Z30A1A4S0G0S1SfSfS10PdA1S10PeA1A4S0G0S1SfSfS10P6fA1S10P21A1A4S2G0A1A3A3A3S11Z7fff8000A1A3").

Definition E_f_S : sstate := ltac2:(tb__ "0|24|
S1eZ5e05cS0SfS11Z0A1M0S0SfS11Za6634A1S0SfS17S32S10PaM1A1M2S11N60A1M3A3M4S0SfS10P17A1S0SfS10P18A1S0SfS10Pa0A1S0SfS10Pa1A1S0SfS10Pa5A1S0SfS10P6fM5A1M6S0SfS17S32S10PcM7A1M8S11Z28A1M9A3S0SfS10PdMaA1MbS0SfGbS0SfS10PeA1McS0SfS11Z8c88cA1MdS0SfG0S0SfS10Pa2A1S0SfS10Pa3A1S0SfS10Pa4A1S0SfS10P21A1MeS0SfS11Z7fff8000A1MfS0SfS17S32S10P64A1M10GfA3S0SfS17S32G10S11Z7fff8003A1A3S0SfS17S32G10S11Z7fff8005A1A3S0SfG8S0SfGeS0SfGcS0SfGbS0SfS10P2fA1S0SfS10P9aA1S0SfS10P9bA1S0SfS10P9cA1S0SfS10P9dA1S2SfA1M11A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0SfS10P3cA1S0SfS10P3dA1S0SfS10P3eA1S0SfS10P3fA1S0SfS10P40A1S0SfS10P41A1S0SfS10P42A1S0SfS10P43A1S0SfS10P44A1S0SfS10P45A1S0SfS10P46A1S0SfS10P47A1S0SfS10P48A1S0SfS10P49A1S0SfS10P4aA1S0SfS10P4bA1S0SfS10P4cA1S0SfS10P4dA1S0SfS10P4eA1S0SfS10P4fA1S0SfS10P50A1S0SfS10P51A1S0SfS10P52A1S0SfS10P53A1S0SfS10P54A1S0SfS10P55A1S0SfS10P56A1S0SfS10P57A1S0SfS10P58A1S0SfS10P59A1S0SfS10P5aA1S0SfS10P5bA1G11A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S1dS5SfA1S0S16S18G4S10P13A1M12G0S2S14A1M13S1aA5S0S16S18G6G0GeG13S1aA5S0S16S18G0S11Ze7bd8A1S11Ze8978A1G13S1fA5S0S16S18G0S11Zf13f8A1M14S11Zf1404A1S0S14S15G14Z8M15GfA3S0S14S15S11Zf1400A1Z4M16S11Z1A1M17A3G13A3A3S1fA5S0S16S18G2G3G0S0S14S15G3G15S10P2eA1A3S0S14S15S11N58A1G15S10P2dA1A3S0S14S15S11N50A1G15S10P2cA1A3S0S14S15S11N48A1G15S10P2bA1A3S0S14S15S11N40A1G15S10P2aA1A3S0S14S15S11N38A1G15S10P29A1A3S0S14S15S11N30A1G15S10P28A1A3S0S14S15S11N28A1G15S10P27A1A3S0S14S15S11N20A1G15S10P26A1A3S0S14S15S11N18A1G15S10P1dA1A3S0S14S15S11N10A1G15S10P1cA1A3S0S14S15S11N8A1G15S10PbA1A3G13A3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S16S18G8G0S11Z30A1M18S0S14S15G0G15S11Z8c86cA1A3S0S14S15S11G15A1G15S11Z8c878A1A3S0S14S15S11Z10A1G15G0A3S0S14S15S11Z18A1M19G15GdA3S0S14S15S11Z20A1G15G0A3S0S14S15G9G15S10P34A1A3G13A3A3A3A3A3A3S1aA5S0S16S18GbG0GcG13S1aA5S2S16A1A3A3A3A3A3A3A3S0S12S13G6S11Z800000000000A1M1aA2S0S12S13GeS10P1eA1M1bA2S0S12S21S17S35G10S11Z3M1cA1A3M1dG8A2S0S12S13G10S11Z1fffffffffffffffA1A2S0S12S13G1dG8A2S0S12S13G8G1dA2S0S12S1bG1G16A2S0S12S13G2G1aA2S0S12S13G1bG2A2S0S12S13G1bS17S32G4G12A3A2M1eS0S12S13G1bG4A2S0S12S1cS33S11N1000A1G12A3M1fS0S12S1cS33G12S11N10000000000A1A3M20S0S12S1bG7G1cA2S0S12S13S11Z1000A1M21G8A2S0S12S13S17S32G8G18A3G1bA2S0S12S13G8G1aA2S0S12S1bGaG16A2S0S12S13G21GbA2S0S12S13S17S32GbGcA3G1bA2S0S12S13GbG1aA2S0S12S13G17GcA2S0S12S13GcS11Z10000000000A1M22A2S0S12S13G17GeA2S0S12S13GeG22A2S0S12S13GeS11ZffffffffA1A2S0S12S1bG5G16A2S0S12S20S1cS34G6G0A3A1S0S12S13G21G6A2S0S12S13S11Z646000A1G6A2S0S12S13S17S32G6GeA3G1bA2S0S12S13S17S32G8G19A3G4A2S0S12G1eS0S12G1fS0S12G20S0S12S13S11Z7fff7f800000A1M23G1bA2S0S12S13G1bS11Z7fffff800000A1A2S0S12S13G23G2A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3PaaS7A9").
Definition E_f : axst := ltac2:(tb__ "0|1|
S30S70S0S3SfSfA2M0S1SfSfS10PcA1S11Z30A1A4S0G0S1SfSfS10P6fA1S10P21A1A4S2G0A1A3A3S11Z7fff8000A1A3").

Definition Pre_f : axst := Pre_free AE_A [] UStopLe.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S0S3S2dSfA2M0S1S2dSfPfS50A4S0G0S1S2dSfPdS49A4Sc5PaS2fS52A1S2fS64A1A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_f Pre_f s_f).
Definition T_free : axst := Eval vm_compute in T_afterA Pre_f E_f s_f R_f (L_free AE_A [] UStopLe).

Definition vPn : sv := SVar 140.
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S1eSbdS7cS7dS7aA1S0S3S6SfA2M0S1S6SfUaS11Z0A1A4S2G0A1A3A2S7bS1dS5SfA1S8S16S0S16S5aS2S14A1A1S0S16S59S0S16S5bS0S16S61S2S16A1A3A3A3A3S37A3S5fS96S7A9").
Definition P_fail : axst := mkA P_fail_S X_ra.
Definition ok_facts : list sprop := ltac2:(tb__ "0|0|
S0S12S1bP8cZ4A2S0S12S20S1cS34S4aS11Z0A1A3A1S0S12S13S11Z1000A1S4aA2S0S12S13S17S32S4aS46A3S10P1eA1A2S0S12S13S4aS11S6dA1A2S0S12S13S11SbcA1S4aA2S2S12A1A3A3A3A3A3A3").
Definition O_new (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S4aS11Z0A1S46Vcells;S1aA5").
Definition P_ok_S : sstate := ltac2:(tb__ "0|2|
S1eSbdS7cS7dS7aA1S0S3S6SfA2M0S1S6SfUaS4aA4S2G0A1A3A2S7bS1dS5SfA1S8S16S0S16S5aS2S14A1M1A1S0S16S59S0S16S5bS0S16S71G1A1S2S16A1A3A3A3A3S37A3S8S12S76S5fA3P8dS7A9").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S39S72S0S3SfSfA2M0S1SfSfS48S11Z30A1A4S0G0S1SfSfS4aS46A4S2G0A1A3A3A2").

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS4cS49A4S2G0A1A3").
Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS10S5eA1S46A4S0G0S1SfSfS4cS49A4S2G0A1A3A3").
Definition tv2 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS10S5eA1S46A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS4aS46A4S2G0A1A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|2|
S0SacSafZ1M0Z0M1S46A3S0SacSaeG1S9fZ2Sb0A2G0A3S2SacA1A3A3").
Definition bd1 : list bitem := [BIc 0 KU 1].
Definition ndR (tv : list (sv * sv)) (bd : list bitem) : ndesc := ND tv [] bd.

Definition z0 : sv := SLit 0.
Definition cp_var : sv := SVar 151.
Definition cutsE : list edescA := ltac2:(tb__ "0|5|
S0S3S3S2eS3aA2M0S3S2cSfA2M1A2M2S1G0G1S1S2eS3aS56S45S47S4eA2A4S1S2cSfZ64S51A4A4S0G2S1G0G1S1S2eS3aS66S45S47S53A2A4S1S2cSfZ50S51A4M3A4S0G2S1G0G1S1S2eS3aS73S45S58S53A2M4A4G3A4S0G2S1G0G1S1S2eS3aS6eG4A4S1S2cSfZ46S75A4A4S0G2S1G0G1S1S2eS3aS65S45S78S2SacA1A2A4S1S2cSfZ3cS51A4A4S2G2A1A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|5|
S0S3S3S2eS3aA2M0S3S2cSfA2M1A2M2S1G0G1S1S2eS3aS4dS45S47S4eA2A4S1S2cSfZ5aS51A4A4S0G2S1G0G1S1S2eS3aS52S45S58S53A2A4S1S2cSfZ41S51A4A4S0G2S1G0G1S1S2eS3aS62S45S47S2SacA1M3A2A4S1S2cSfZ0S51A4M4A4S0G2S1G0G1S1S2eS3aS63S45S6bG3A2A4G4A4S2G2A1A3A3A3A3").

Definition P0_ra (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S81S2cS2cS81S2cS2cS81S2cS2cS7fSa2S3S3S2cS2cA2M0S2cA2S1G0S2cS1S2cS2cR3R2A4R1A4VFF;A3S7fS9cR3S86Q40S29Vr;PcA2A2M1A2S9cS9eG1Z30A2S9eR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").

Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S80S2eSb9S5cS4dS55S57S94S8dS2S8eA1S8cA3A5S66A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S80S2eSb9S5cS4dS55S57S95S8dS2S8eA1S8cA3A5S74A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_free_eq : ltac2:(tb__ "0|0|
S80S2eSb9S64S52S54S5dS8fS8dS2S8eA1S8cA3A5S65A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S80S9S40S36S7aS60S67P64S68S69A7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb1S19S4S85Q40A1A1Sb3OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2cSc8VCST;R1A2S7fS9cZ0R2A2S9dR2SbcA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2cSc8VXGL;R1A2S7fS9cZ0R2A2S9dR2SbcA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S3S3S2cS2cA2S2cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 2 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;VKc;S4bVFB;VFF;A2VFB;VFF;VBX;S3bVnd;Aa").
Definition Posts_ra : list (axst * jpostA) := ltac2:(tb__ "0|2|
S0S3S2eS87A2M0S1S2eS87S62Sb6S45S47S2SacA1M1A2A1A4S0G0S1S2eS87S63Sb6S45S6bG1A2A1A4S2G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3eVAInv;VCST;VXGL;S7aVKc;Vrho0;S4bVFB;VFF;A2VFB;VFF;VBX;S3bVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S3S2eS3aA2SccFn;") := ltac2:(tb__ "0|0|
S42VAInv;VCST;VXGL;S7aVKc;Vrho0;S4bVFB;VFF;A2VFB;VFF;VBX;S3bAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S88S36S7aVrho0;Vtp0;Sb5A5").

Lemma P0_frame : ltac2:(tb__ "0|1|
Sb1S19Sc6S7aVrho0;R1A3S4bVFB;VFF;Vrho0;A3S41VFF;R4A2SdS2cA1S2cS7fS9cS86Q40S22R6S48A2A2M0R1A2S9dR1S9eG0Z30A2A2A2SbbVCST;R8R3R2A4F_;Fa;Fx;F_;F_;F_;Frho;FAi;").
Proof.
  intros Ai rho Hav (f & s & fl & Hin & H1 & H2) HFF x a Ha.
  assert (E12 : rw rho 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold vA in Ha. cbn [eval] in Ha. rewrite E12 in Ha.
  right; right; right. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | lia].
Qed.

Lemma al_obj_range : ltac2:(tb__ "0|3|
S19S16S2cS80S9S2bS25R2A1S48A2SaA3S80SfS27R3A1S11Z0A1A3S80SfS26R4A1S11Z30M0A1A3S7fS9cScS2cS2cS28R6R5A2M1A3R4A2S9dR4SeS2cS2cG1A3A2A2S7fS9cS86Q40S22R7S48A2A2M2R5A2S9dR5S9eG2G0A2A2A2F_;F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a Hb Hl Hh Hr. apply sv_eqb_sound in Hb. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
  cbn [fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S19SbaVAInv;VCST;VXGL;S7aVrho0;S4bVFB;VFF;A2VFB;VFF;S4dS55S57R1S45S47S4eA2S5S2cA1Sb1Sb2S7fS7fS9cZ1SadR3Sa9S55PcA2A2M0A2S9dG0Sa0Z2Z27A2A2A2S90S2S8eA1S8cSa8Sa7R3S57R1A3S55A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun o => sv_eqb (ob_base o) vA) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[<-|[]]]]; [cbn in Hb; discriminate| |cbn in Hb; discriminate]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun r => sv_eqb (fst r) vA) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exact I.
  - pick_facts HF [21%nat; 23%nat]. change (wsub_get s_m 12) with vNS. unfold uval, vNS in *. zfacts; lia.
Qed.

Lemma site_f : ltac2:(tb__ "0|2|
S19SbaVAInv;VCST;VXGL;S7aVrho0;S4bVFB;VFF;A2VFB;VFF;S52S54S5dR1S45S58S53A2SbS2cSadR1Sa9S54PcA2M0A2A2Sb1Sb2S7fScdR3S1SfSfS4cS49A4M1A2S7fS80S3S2cS2cA2SceR3G1A2S1S2cS2cSadR3G0A2SadR3Sa9S54PdA2A2A4A3S90S2S8eA1S8cSa8Sa7R3S5dR1A3S54A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  change (wsub_get s_f 12) with vP. change (wsub_get s_f 13) with vOS.
  assert (Hnz : tnz rho (vP, vOS)).
  { pick_facts HF [18%nat]. unfold tnz, vP. cbn [fst eval]. zfacts; lia. }
  split; [|split; [|split; [exact Hnz|split; [reflexivity|exact I]]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_f)) tv1 (Some 1%nat) (fun o => sv_eqb (ob_base o) vA) R_f _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[<-|[]]]]; [cbn in Hb; discriminate|cbn in Hb; discriminate|]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exists (vP, vOS). split; [reflexivity|]. split; [exact Hnz | reflexivity].
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_f)) tv1 (Some 1%nat) (ss_objs (ax_S E_f)) (fun r => sv_eqb (fst r) vA) (ax_X E_f) _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exists (vP, vOS). split; [reflexivity|]. split; [exact Hnz | reflexivity].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2cS4S85Q40A1A1Sa3F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S83S2eS19S4S85Q40A1A1Sa3Sc9S12S24R3A1S2aS2fR4A1A1A3VTR;S82S36R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa3Sa3Sa3Sa6R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S83S83S2eS2eSaaS4S16A1M0S4S3S2eS87A2M1A1S4S3SfSfA2M2A1Sa3S19S4S85Q40A1A1M3G2Sa2G2R1R5A3Sa2G2R2S31RbA1A3F_;Fr;S80SdG0A1S8bRaR9R8A3SbG0R7A2A3S80S9S8aRbRaR9R8ScaG1S2eScS2eS87A2R7A4A5SaA3S19G3VTR;S82S36RfRdR2R1A5S88S36S23S2fRdA1A1R2R1RaA5A2Ftp1;Frho1;S4Sb4A1M4Sb2Sb3S84S36R9R8R10S1G4Sb7R3Sb8R2R1A2A4A5R13RaR9R4R2A4R13Sa8Sa7RbRfSabR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2eS87G4Sb2Sb3S19G3G4Sb2Sb3Sa2G1S1S2eS87RaR9A4R14A3S84S36R12R11R19S1G4Sb7R9Sb8R8R7A2A4A5R1cR13R12RaR8A4Sc6S23S2fR1aA1A1Sa8Sa7R14R18SabR9R13RaA3A3R19A2R8A3S84S36R9R8ReS1G4Sb7R7Sb8R6R5A2A4A5ReSa8Sa7R16R1aSabRbR15RcA3A3R1bA2R15RaR9R8R6A6S7fScfR17SabRcR16RdA3R1bR1cR1dR10R1eR19RbA9S19Sc7R18SabRdR17ReA3R1cR1dS2fR1eA1S2fR1fA1S2fR11A1R1RcA9VTR;S82S36S89R11Sa8Sa7R19R1dSabReR18RfA3A3R1eA2R18RdRcA5Sd0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S82S36R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sb1S19S4S85Q40A1A1VTR;S82S36S92VAInv;S2S8eA1M0S8cR3VKc;S10PcA1A6S99S8dG0S8cA3R2R1A5S88S36S7aR2R1S97S8dVAInv;VCST;VXGL;G0S8cR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CFREE : ltac2:(tb__ "0|2|
Sb1S19S4S85Q40A1A1VTR;S82S36S93VAInv;S2S8eA1M0S8cR3VKc;A5S98S8dG0S8cA3R2R1A5S88S36S7aR2R1S0S3S2eS87A2M1S1S2eS87S8fS8dG0S8cA3S91VAInv;VCST;VXGL;R3VKc;A5A4S2G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S2eS3aS3S2cSfA2M0S19S4S85Q40A1A1M1S2cG1Sa2S3S3S2eS3aA2M2G0A2S1G2G0S1S2eS3aR7R6A4R5A4S68A3S7fS9cZ0S3dS1G2G0S1S2eS3aR8R7A4R6A4R5A2M3A2S9dG3R3A2A2VTR;S82S36VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2eS3aS19S4S85Q40A1A1M0S2cG0Sa2S3S2eS87A2S1S2eS87R6Sb6R5A1A4Sb5A3VTR;S82S36VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Lemma X_E_m : ltac2:(tb__ "0|1|
S19S4S85Q40A1A1M0S2cG0S9cS9fZ5aSa0Z2Z40A2A2R2A2VTR;S82S36VJAv;S45S47S4eA2A1S4dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp (ndR tv0 bd0) bd1 (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr ndR]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull (ndR tv0 bd1) (80, z0)); [right; left; reflexivity|].
    unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned. cbn. lia.
  - intros rho' tp'. cbn [nd_tv nd_fr ndR]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok (ndR tv1 bd1) (80, z0)); [right; right; left; reflexivity|]].
    + intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF].
      eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
      pick_facts HF [28%nat]. eapply tnz_of_fact. eassumption.
    + unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned. cbn. lia.
Qed.

Lemma X_E_f : ltac2:(tb__ "0|1|
S19S4S85Q40A1A1M0S2cG0S9cS9fZ41Sa0Z2Z40A2A2R2A2VTR;S82S36VJAv;S45S58S53A2A1S52R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (free_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_f s_f R_f rho tp (ndR tv1 bd1) 1%nat (vP, vOS) [] (FAM b tp0) CFREE).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - reflexivity.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_f rho).
  - intros rho' tp'. cbn [nd_tv nd_fr ndR remove_nth]. fold Pre_f. rewrite T_free_eq. apply (REENTER T_free (ndR tv2 []) (60, z0)); [do 4 right; left; reflexivity|].
    unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned. cbn. lia.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2eS3aS3S2cSfA2M0S19S4S85Q40A1A1M1G1Sa2S3S3S2eS3aA2M2G0A2S1G2G0S1S2eS3aR6R5A4R4A4S69A3VTR;S82S36VJAv;R6A1R7R4R3A5VFAM;S3dS1G2G0S1S2eS3aR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_m. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned. cbn. lia.
  - apply X_E_f. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned. cbn. lia.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S43S36VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S9aS36S8dVAInv;VCST;VXGL;A5").

Theorem realloc_sum : ltac2:(tb__ "0|0|
S4S85Q40A1A1Sa5S36Vok;S82S36S3cVAInv;VCST;VXGL;VKc;S4bVFB;VFF;A2VFB;VFF;VBX;S3bS45S47S4eA2AaS56Vrho0;R1A5S88S36S7aVrho0;R1Sb5A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue HKc ALA FUEL_ra cutpcs_ra 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := ndR tv0 bd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ra FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ra P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9bS36S8dVAInv;VCST;VXGL;A5").

Theorem realloc_sum_ex : ltac2:(tb__ "0|0|
S4S85Q40A1A1Sa4S36S82S36S3cVAInv;VCST;VXGL;VKc;S4bVFB;VFF;A2VFB;VFF;VBX;S3bS45S47S4eA2AaS56Vrho0;R1A5S88S36S7aVrho0;R1Sb5A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue HKc ALA FUEL_ra cutpcs_ra 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := ndR tv0 bd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ra FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ra FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ra P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_realloc.

(* [comment removed for export] *)
Module MuslMalloc40Post.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "bool"; "pair"; "true"; "list"; "prod"; "app"; "None"; "false"; "fst"; "snd"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "SLit"; "valuation"; "sprop"; "rw"; "DUnknown"; "FcsrFrm0"; "cell"; "mkObj"; "mkSS"; "swf"; "SAlu"; "SPAlign"; "SPUle"; "rm"; "ss_regs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "True"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post.Outcomes"; "out1"; "out0"; "out1_base"; "out1_W"; "out1_model"; "out1_ok"; "out1_tp"; "JL_null0"; "JL_null1"; "JL_ok"; "out0_W"; "out0_model"; "out0_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "region_free"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "NA"; "NG"; "post_sub"; "P_null0"; "P_null1"; "P_ok"; "KxM"; "NPOST_M"; "objs_M'"; "post_regs_M"; "rm_kept_outside"; "F_area"; "NP"; "O_area"; "Posts_M"; "m40_hyps"; "F_grp"; "O_grp"; "O_mctx'"; "dead_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "ax_S"; "axst"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "axM"; "facts_M"; "Pre_M"; "malloc_ret_null"; "D_M"; "O_auxp"; "O_auxv"; "O_errno"; "O_flg"; "O_nlk"; "O_pgsz"; "O_rand"; "O_real"; "O_ssp"; "O_stk"; "O_vml"; "malloc_ret_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes"; "brk0w"; "n8w"; "mf_exp"; "mf_res"; "mg"; "mg_dead"; "mg_ok"; "mgrant"; "n3w"; "pgw"; "tp20"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States"; "RET0a"; "RET0b"; "RET0f"; "RET0g"; "RETPf"; "RETPg"; "vBRK"; "vRES"; "vGRPf"; "vGRPg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "lt"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import
  Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA MmapFixedA MmapBrkA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NP : positive := 130.
Definition NA : positive := 162.
Definition NG : positive := 163.
Definition NPOST_M : positive := 170.

Definition post_reg_M (r10 : sv) (r : nat) : sv := ltac2:(tb__ "0|1|
S0SeLr;Vr;S11Z0A1S0S0SeLn;R1S10PbA1S0S0SeLn0;R1S10PaA1S0S0SeLn1;R1S11Z10800A1S0S0SeLn2;R1S11Z6245b8A1S0S0SeLn3;R1S10S8dS4bS8eVr;A1A2A1M0S0S0SeLn4;R1G0S0S0SeLn5;R1G0S0S0SeLn6;R1S10P1cA1S0S0SeLn7;R1S10P1dA1S0S0SeLn8;R1Vr10;S0S0SeLn9;R1G0S0S0SeLn10;R1G0S0S0SeLn11;R1G0S0S0SeLn12;R1G0S0S0SeLn13;R1G0S0S0SeLn14;R1G0S0S0SeLn15;R1G0S0S0SeLn16;R1S10P26A1S0S0SeLn17;R1S10P27A1S0S0SeLn18;R1S10P28A1S0S0SeLn19;R1S10P29A1S0S0SeLn20;R1S10P2aA1S0S0SeLn21;R1S10P2bA1S0S0SeLn22;R1S10P2cA1S0S0SeLn23;R1S10P2dA1S0S0SeLn24;R1S10P2eA1S0S0SeLn25;R1S10P2fA1S0G0Ln26;X0x2Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition post_regs_M (r10 : sv) : list sv := map (post_reg_M r10) (seq 0 32).
Definition dead_regs : list nat := ltac2:(tb__ "0|0|
S1S0U5S1S0U6S1S0U7S1S0UbS1S0UcS1S0UdS1S0UeS1S0UfS1S0U10S1S0U11S1S0U1cS1S0U1dS1S0U1eS1S0U1fS2S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_mctx' : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11Z6448c0A1S11Z644c68A1S2S17A1S15A5").
Definition objs_M' : list sobj := ltac2:(tb__ "0|0|
S1SfS6eS1SfS51S1SfS69S1SfS65S1SfS6aS1SfS6dS1SfS67S1SfS6fS1SfS66S1SfS6bS1SfS68S1SfS6cS1SfS92S1SfS93S2SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_area : sobj := ltac2:(tb__ "0|1|
S18S1bS73S10S3fA1S11Z1000A1M0A3S11Z0A1G0S2S17A1S15A5").
Definition O_grp : sobj := ltac2:(tb__ "0|0|
S18S10S40A1S11Z0A1S11Z1000A1S2S17A1S15A5").

Definition F_area : list sprop := ltac2:(tb__ "0|0|
S1S13S1cS3fZcA2S1S13S1dS10S3fA1S11S55Z7fffff800000Z2000A2A1A2S2S13A1A3A3").
Definition F_grp : list sprop := ltac2:(tb__ "0|0|
S1S13S1cS40ZcA2S1S13S1dS10S40A1S11S55Z7fffff800000Z1000A2A1A2S2S13A1A3A3").

Definition P_null0 : axst := ltac2:(tb__ "0|0|
S60S19S63S48S11Z0A1A1S5cS16S9SeA1S47S61S46SaA9A1").
Definition P_null1 : axst := ltac2:(tb__ "0|0|
S60S19S63S48S11Z0A1A1S5cS16S9SeA1S8SfS47S1SfS4cS2SfA1A3A3S8S13S4aS61A3S46SaA9A1").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S60S19S70S48S1bS73S10S40A1S11Z40A1A3A1S5cS16S9SeA1S8SfS47S1SfS4cS1SfS50S2SfA1A3A3A3S8S13S4fS8S13S4aS61A3A3S46SaA9A1").

Lemma posts_wf : ltac2:(tb__ "0|0|
S20S21S3S5aS42A1S5A3S20S21S3S5aS43A1S5A3S20S21S3S5aS44A1S5A3S20S21S3S1aS58S42A1A1S5A3S20S21S3S1aS58S43A1A1S5A3S21S3S1aS58S44A1A1S5A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition post_sub (L : axst) (extra : wsub) : wsub := ltac2:(tb__ "0|1|
S8S7S26SeA2M0S90S0G0S0S4S26SeS8dS4bS8eR1A1A2S91SeR1S1fS58VL;A1A1S11Z0A1A4A4Lr;S52A4Vextra;A3").

Lemma ent_RET0a : ltac2:(tb__ "0|0|
S21S3S57S7fS42S41S7fS2S7S26SeA2A1A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_RET0b : ltac2:(tb__ "0|0|
S21S3S57S80S42S41S80S2S7S26SeA2A1A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_RET0g : ltac2:(tb__ "0|1|
S21S3S57S82S43S41S82S1S7S26SeA2M0S4S26SeS3fS85A4S2G0A1A3A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_RET0f : ltac2:(tb__ "0|1|
S21S3S57S81S43S41S81S1S7S26SeA2M0S4S26SeS3fS86A4S2G0A1A3A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_RETPg : ltac2:(tb__ "0|1|
S21S3S57S84S44S41S84S1S7S26SeA2M0S4S26SeS3fS85A4S1G0S4S26SeS40S88A4S2G0A1A3A3A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_RETPf : ltac2:(tb__ "0|1|
S21S3S57S83S44S41S83S1S7S26SeA2M0S4S26SeS3fS86A4S1G0S4S26SeS40S87A4S2G0A1A3A3A2A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition rm_kept_outside (lo hi : Z) (rho0 rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S27Q40M0A1S24S20S54Vlo;S28G0R1A2M1A2S56G1Vhi;A2A2A1S21SdS27Q8A1A1S1eVrho';R2A2S1eVrho0;R2A2A3F_;Fx;").

Section Outcomes.
Variables (m : Model) (B : Z).
Let brk0 : Z := bv_unsigned (brk0w m).

Inductive out0 := O0_refused | O0_reserved (a : word).
Definition out0_ok (o : out0) : Prop := ltac2:(tb__ "0|1|
S2bOLo;Vo;S23S27Q40M0A1S71S29G0Z0A2Vm;S75R1A4La;X2bx2").
Definition out0_model (o : out0) : Model := ltac2:(tb__ "0|0|
S2bS37Lo;Vo;Vm;S27Q40A1S77Vm;R1A2La;X2bx2").
Definition out0_W (o : out0) : Z * Z := ltac2:(tb__ "0|3|
S2bS7S25S25A2Lo;Vo;S4S25S25Z0M0G0A4S27Q40M1A1S4S25S25S28G1R1A2M2S53G2Z2000A2A4La;X2bx2").

Definition JL_null0 : jpostA := ltac2:(tb__ "0|2|
S12S6S27Q40A1A1M0S12G0S6S38A1S37S20S21G0R3R5A3S20S72S5bR6R4A3S22S2bS2bS20S36R1A1S20S49SbS25S25S34R1A1M1A3ScS25S25G1A3R7R5A4S5dS35R1A1S53VB;Z3000A2R5R4R3R2A6A2A2Lo;A2A2A2Lmd';Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Inductive out1 := O1_kept | O1_ok | O1_dead | O1_fail (a : word).
Definition out1_ok (o : out1) : Prop := ltac2:(tb__ "0|4|
S2aOLo;Vo;S20S54S53Vbrk0;Z2000A2S39S3aVm;A1M0A1A2S21S3S3bS8S7S27Q40M1A1M2G2A2S3dG0A1S3cG0A1A3S74Vm;A1S7cA3S5A3A2M3G3G3G2S71S29G1Z0A2Vm;S75R1A4La;X2ax4").
Definition out1_model (o : out1) : Model := ltac2:(tb__ "0|0|
S2aS37Lo;Vo;S78Vm;A1S7aVm;A1S79Vm;A1S27Q40A1S76Vm;R1A2La;X2ax4").
Definition out1_base (o : out1) : word := ltac2:(tb__ "0|2|
S2aS27Q40A1M0Lo;Vo;S74Vm;A1M1G1G1G0R1La;X2ax4").
Definition out1_W (o : out1) : Z * Z := ltac2:(tb__ "0|1|
S4S25S25S28Q40S2cVo;A1A2M0S53G0Z2000A2A4").
Definition out1_tp (o : out1) (tp0 : list word) : list word := ltac2:(tb__ "0|1|
S2aS6S27Q40A1M0A1Lo;Vo;Vtp0;Vtp0;S7eVm;Vtp0;A2G0Vtp0;La;X2ax4").

Definition JL_null1 : jpostA := ltac2:(tb__ "0|3|
S12S6S27Q40A1M0A1M1S12G1S6S38A1S37S20S72S5bR6R4A3S22S2aS2aS20S2fR1A1S20S21G1R4S30R1R6A2A3S20S21G0S14R5S3fA2S2cR1A1A3S20S49SbS25S25S2dR1A1M2A3ScS25S25G2A3R7R5A4S5dS2eR1A1S53VB;Z3000A2R5R4R3R2A6A2A2A2A2Lo;A2A2Lmd';Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition JL_ok : jpostA := ltac2:(tb__ "0|5|
S12S6S27Q40M0A1M1A1M2S12G2S6S38A1S37S20S72S5bR6R4A3S22S2aS2aS22G1G1S20S2fR2A1S20S71S29G0Z0A2S2eR2A1M3S7dR1A4S20S21G2R5S30R2R7A2A3S20S21G1S14R6S3fA2S2cR2A1A3S20S21G1S14R6S40A2R1A3S20S49SbS25S25S2dR2A1M4A3ScS25S25G4A3R8R6A4S5dS7bG3R1A2S53VB;Z3000A2R6R5R4R3A6A2A2A2A2A2A2Lg;A2Lo;A2A2Lmd';Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition Posts_M : list (axst * jpostA) := ltac2:(tb__ "0|1|
S1S7S59S5eA2M0S4S59S5eS42S31A4S1G0S4S59S5eS43S32A4S1G0S4S59S5eS44S33A4S2G0A1A3A3A3").
End Outcomes.

Record m40_hyps (m : Model) (B : Z) : Prop := mkM40 {
  m40_res : vm_reserved (m_vmmaps m) = segments_reserved segsA;
  m40_sb : vm_start_brk (m_vmmaps m) = vm_brk (m_vmmaps m);
  m40_al : bv_unsigned (brk0w m) mod 4096 = 0;
  m40_lo : 0x646000 <= bv_unsigned (brk0w m);
  m40_hi : bv_unsigned (brk0w m) <= 0x80646000;
  m40_B : B + 12288 <= vm_limit (m_vmmaps m);
  m40_top : init_sp_ok (m_vmmaps m);
  m40_band : band_covered (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) SHADOW_BAND_LO SHADOW_BAND_HI;
  m40_lz : forall r, In r (m_vm_lazy m) -> 0 < bv_unsigned (snd r);
  m40_lim : lazy_in_maps m }.

Definition KxM (m : Model) (B : Z) : jpredA := ltac2:(tb__ "0|1|
S12S6S27Q40M0A1A1S6S38A1S37S20S5dVm;VB;R4R3R2R1A6S54S53S39S3aVm;A1A1S64A2S28G0S14R4PaA2A2A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma stableA_KxM : ltac2:(tb__ "0|0|
S26S37S25S8fPaR3A2S8cS3eR4S45R3R2A2A3F_;FB;Fm;Fn;").
Proof.
  intros n m B Hn rho rho' tp tr md md' Hag Hme [HK HS]. split.
  - exact (stableA_KxA segsA n m B rho rho' tp tr md md' Hag Hme HK).
  - rewrite <- (proj1 Hag 10%positive Hn). exact HS.
Qed.

Definition musl_malloc40_sum_stmt : Prop := ltac2:(tb__ "0|3|
S96OF_;S37S25S8aS12S6S27Q40A1A1M0S6S38A1M1S37R5R4R3R2R1A4S21G1R3S2S38A1A3F_;Fmd;Ftr;Ftp;Frho;M2S8bS3eR5R2A3F_;FJ;S8aG2S97S3eR6R2A3F_;FJ;S4eR4R3A2S12G0S95S3eR8S89S3eS45R7R6A2S62R2R1A5S5fS3eS5bR2R1S4dR7R6A2A5A4Ftp;Frho;F_;F_;F_;FB;Fm;Fok;").

Definition musl_malloc40_sum_ex_stmt : Prop := ltac2:(tb__ "0|0|
S37S25S4eR2R1A2S12S6S27Q40A1A1S94S3eS89S3eS45R5R4A2S62R2R1A5S5fS3eS5bR2R1S4dR5R4A2A5A3Ftp;Frho;F_;FB;Fm;").
End MuslMalloc40Post.

(* [comment removed for export] *)
Module DrvFwIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "andb"; "bool"; "false"; "prod"; "pair"; "true"; "None"; "fst"; "option"; "snd"; "length"; "list"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "cell"; "mkObj"; "sprop"; "DImage"; "FcsrFrm0"; "SPUle"; "mkSS"; "swf"; "DUnknown"; "SPAlign"; "mkCell"; "ob_base"; "ob_hi"; "ob_lo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "pow"; "div"; "mul"; "opp"; "sub"; "eqb"; "ltb"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "FERR"; "fc"; "EBUF"; "P_fw"; "O_fwstk"; "O_realfw"; "facts_fw"; "fregs_fw"; "fw_msgs"; "D_FW"; "MSGB"; "NPOST_FW"; "O_ferr0"; "O_ferr1"; "Pre_fw"; "fw_entry"; "fw_ret"; "obj_farW"; "objs_fw"; "objs_fw'"; "post_regs_fw"; "reg_fw"; "regs_fw"; "xblk"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "eqb"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "SHB"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "O_rtc3w"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axwf"; "leafA"; "mkAX"; "mkLeafA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "image_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition fw_entry : Z := 0x4d13c.
Definition fw_ret : Z := 0x4f194.
Definition FERR : Z := 0xec260.
Definition EBUF : Z := 0x644cc0.
Definition D_FW : Z := 2400.

Definition fw_msgs : list (Z * Z) := ltac2:(tb__ "0|2|
S1S6S22S22A2M0S7S22S22Z21441Z1fM1A4S1G0S7S22S22Z1609eG1A4S1G0S7S22S22Z14d77Z13A4S2G0A1A3A3A3").

Definition MSGB (msg len : Z) : list byte := ltac2:(tb__ "0|2|
SbSeS5dQ8A1M0A1M1A1G1Lx;S61S53Vmsg;S2fVlen;A1A3G1R1Lbs;S2G0A1Xbx2").

Definition xblk (msg len : Z) : sv * sv := ltac2:(tb__ "0|1|
S29S28Vmsg;Z40M0A2G0A2S22S7S10S10S11R1A1S11S2bS29S28S26S26Vmsg;Vlen;A2Z3fA2G0A2G0A2R1A2A1A4Tb;").

Definition O_fwstk : sobj := ltac2:(tb__ "0|0|
S15S12PaA1S11S2aS39A1A1S11Z0A1S2S14A1S1cA5").
Definition O_ferr0 : sobj := ltac2:(tb__ "0|0|
S15S11Z0A1S11S30A1S11S26S30Ze8A2A1S2S14A1S17A5").
Definition fc (off w v : Z) : cell := ltac2:(tb__ "0|0|
S1eS11S26S30Voff;A2A1Vw;S11Vv;A1A3").

Definition O_ferr1 : sobj := ltac2:(tb__ "0|2|
S15S11Z0M0A1S11S30A1S11S26S30Ze8A2A1S1S14S31Z38Z8M1S32A3S1S14S31Z28G1S32A3S1S14S31Z20G1S32A3S1S14S31Z10G1G0A3S1S14S31G1G1G0A3S1S14S31Z88Z4S2bS27Z2Z40A2Z1A2A3S2S14A1A3A3A3A3A3A3S17A5").
Definition O_realfw : sobj := ltac2:(tb__ "0|0|
S15S11Z0A1S11Ze99c0A1S11Ze99c8A1S2S14A1S17A5").
Definition objs_fw : list sobj := ltac2:(tb__ "0|0|
S1S13S34S1S13S3cS1S13S54S1S13S55S1S13S35S1S13S50S1S13S51S2S13A1A3A3A3A3A3A3A3").
Definition objs_fw' : list sobj := ltac2:(tb__ "0|0|
S1S13S34S1S13S3dS1S13S54S1S13S55S1S13S35S1S13S50S1S13S51S2S13A1A3A3A3A3A3A3A3").
Definition facts_fw : list sprop := ltac2:(tb__ "0|2|
S1S16S1dPaM0Z4A2S1S16S19S11Z7fff7ff01000A1S12G0A1M1A2S1S16S19G1S11S27Z2Z2fA2A1A2S2S16A1A3A3A3").

Definition obj_farW (lo0 hi0 : Z) (o : sobj) : bool := ltac2:(tb__ "0|e|
S10S4Lx;M0S1fVo;A1S22G0S21Vo;A1M1S22G0S20Vo;A1M2S22S3S3S3S3S2cR3Z0M3A2S25G3R2A2A2S25R2R1A2M4A2S2dR1S27Z2M5Z3eA2A2A2SfS25R1Vlo0;A2S25Vhi0;R2A2A2A2Lh;S23S5Li;M6S5eS10S10S5Lb;La;M7Lop;M8G8S5fG7Lop;M9G9S4S24S10S5La;Lw;Lsgn;MaS23S10S22S5Lk;Li;MbLl0;McX10x8Ll;G6G8G8G9G9GaS23GbLl;MdX10x8Lbz;S23G0G1S22G0G2S22S3S3S3S4cR3PaA2S25S2aS27G5Z28A2A1R2A2A2G4A2S25R1G3A2A2Lh;G6G8G8G9G9GaGcX10x8Ll;G6G8G8G9G9GaGdX10x8Lv;G8G8G9G9GaGdX10x8").
Definition objs_farW (lo0 hi0 : Z) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S3S3S25Z0Vlo0;A2S25Vhi0;S27Z2Z20A2A2A2S5cS13S41Vlo0;Vhi0;A2Vobjs;A3A2").

Definition reg_fw (msg len : Z) (r : nat) : sv := ltac2:(tb__ "0|1|
S0S10Lr;Vr;S11Z0A1S0S0S10Ln;R1S12PbA1S0S0S10Ln0;R1S12PaA1S0S0S10Ln1;R1S11Z10800A1S0S0S10Ln2;R1S11Z6245b8A1S0S0S10Ln3;R1S12S4aS4dU3cVr;A2A1A1M0S0S0S10Ln4;R1G0S0S0S10Ln5;R1G0S0S0S10Ln6;R1G0S0S0S10Ln7;R1G0S0S0S10Ln8;R1S11Vmsg;A1S0S0S10Ln9;R1S11Vlen;A1S0S0S10Ln10;R1S11Z1A1S0S0S10Ln11;R1S11S30A1S0G0Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition regs_fw (msg len : Z) : list sv := ltac2:(tb__ "0|0|
S4eS0S10S45Vmsg;Vlen;A2S4fU0U20A2A4").
Definition fregs_fw : list sv := ltac2:(tb__ "0|0|
S4eS0S10S0S12S4aS4dU14R1A2A1A1Lr;S4fU0U20A2A4").
Definition NPOST_FW : positive := 132.
Definition post_reg_fw (r : nat) : sv := ltac2:(tb__ "0|1|
S0S10Lr;Vr;S11Z0A1S0S0S10Ln;R1S12PbA1S0S0S10Ln0;R1S12PaA1S0S0S10Ln1;R1S11Z10800A1S0S0S10Ln2;R1S11Z6245b8A1S0S0S10Ln3;R1S12S4bP64S4aVr;A1A2A1M0S0S0S10Ln4;R1G0S0S0S10Ln5;R1G0S0S0S10Ln6;R1S12P44A1S0S0S10Ln7;R1S12P45A1S0S0S10Ln8;R1S11Z1A1S0S0S10Ln9;R1G0S0S0S10Ln10;R1G0S0S0S10Ln11;R1G0S0S0S10Ln12;R1G0S0S0S10Ln13;R1G0S0S0S10Ln14;R1G0S0S0S10Ln15;R1G0S0S0S10Ln16;R1S12P4eA1S0S0S10Ln17;R1S12P4fA1S0S0S10Ln18;R1S12P50A1S0S0S10Ln19;R1S12P51A1S0S0S10Ln20;R1S12P52A1S0S0S10Ln21;R1S12P53A1S0S0S10Ln22;R1S12P54A1S0S0S10Ln23;R1S12P55A1S0S0S10Ln24;R1S12P56A1S0S0S10Ln25;R1S12P57A1S0G0Ln26;X0x2Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition post_regs_fw : list sv := map post_reg_fw (seq 0 32).

Definition Pre_fw (msg len : Z) : axst := ltac2:(tb__ "0|1|
S59S1aS3fS46Vmsg;Vlen;A2S37S18S9S10A1S42S36S62S5A9S1S6S10S10A2M0S47Vmsg;Vlen;A2S2G0A1A3S11S52A1A3").
Definition P_fw : axst := ltac2:(tb__ "0|0|
S59S1aS40S44S37S18S9S10A1S43S36S3bS5A9S2S6S10S10A2A1S11S52A1A3").
Definition Posts_fw : list leafA := ltac2:(tb__ "0|0|
S1S58S5aS33S60A2S2S58A1A3").

Lemma fw_wf : ltac2:(tb__ "0|2|
S6S22S22A2M0S5bG0R1S38A3S49S48S4S57S3eSaS22S22R2A3ScS22S22R2A3A2M1A1S8A3S48S4S1bS56G1A1A1S8A3A2F_;Fml;").
Proof. intros ml H. repeat (destruct H as [<-|H]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct H. Qed.
Lemma P_fw_wf : ltac2:(tb__ "0|0|
S49S48S4S57S33A1S8A3S48S4S1bS56S33A1A1S8A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma MSGB_len : ltac2:(tb__ "0|2|
S6S22S22A2M0S5bG0R1S38A3S48S22S2eSdS5dQ8A1S3aSaS22S22R2A3ScS22S22R2A3M1A2A2A1G1A3F_;Fml;").
Proof. intros ml H. repeat (destruct H as [<-|H]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]). destruct H. Qed.
End DrvFwIface.

(* [comment removed for export] *)
Module DrvExitIface.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sobj"; "mkObj"; "sv"; "DUnknown"; "DImage"; "SVar"; "sprop"; "mkCell"; "SPUle"; "swf"; "FcsrFrm0"; "SPAlign"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "bool"; "pair"; "true"; "prod"; "list"; "None"; "app"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "cz"; "ATX"; "FERR"; "vSPx"; "TRI"; "vTID"; "CALL_THUNK"; "COV_HANDLER"; "Pre_exitP_S"; "AEF_GUARD"; "D_X"; "O_afl2b"; "O_afl2p"; "O_atx0"; "O_atx1"; "O_cfl2"; "O_cov"; "O_dso"; "O_dtf"; "O_ferr"; "O_fin"; "O_fina"; "O_glx"; "O_nlkx"; "O_ofile"; "O_ofl"; "O_osbuf"; "O_pgAx"; "O_pgBx"; "O_regf"; "O_tid"; "O_trix"; "O_uerr"; "O_uout"; "O_xlk"; "O_xstk"; "Pre_exit"; "Pre_exit0"; "Pre_exit0_S"; "Pre_exitP"; "Pre_exit_S"; "atx_cells0"; "axX"; "exit_entry"; "facts_exit"; "fregs_X"; "objs_exitP"; "regs_X"; "supportedP"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "eqb"; "sub"; "opp"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axwf"; "mkAX"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "O_file0"; "O_file_after"; "O_realm"; "O_rtc3w"; "O_sbuf0"; "O_sbuf_after"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "O_afl1"; "O_aglob"; "O_ph"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition exit_entry : Z := 0xd453c.
Definition exit_ecall : Z := 0xd4314.
Definition wl_ecallA  : Z := 0xd9ad4.
Definition FERR : Z := 0xec260.
Definition D_X : Z := 1024.

Definition vSPx : sv := SVar 10.
Definition vTID : sv := SVar 16.

Definition cz (a : Z) (w : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S9S0Va;A1Vw;Vv;A3").
Definition O_xstk : sobj := ltac2:(tb__ "0|0|
S3S1eS0S50S25A1A1S0Z0A1S11S1A1S5A5").

Definition O_pgAx : sobj := ltac2:(tb__ "0|0|
S3S0Z7fffc570A1S0Z0A1S0Z1e0A1S11S1A1S5A5").
Definition O_pgBx : sobj := ltac2:(tb__ "0|0|
S3S0Z800158a8A1S0Z0A1S0Z300A1S11S1A1S5A5").
Definition O_ferr : sobj := ltac2:(tb__ "0|3|
S3S0Z0A1S0S1dA1S0S4cS1dZe8A2A1SfS1S1bS4cS1dZ28A2Z8M0S7P11A1M1A3SfS1S1bS4cS1dZ38A2G0G1A3SfS1S1bS4cS1dG0A2G0S7P12A1M2A3SfS1S1bS4cS1dZ10A2G0G2A3SfS1S1bS4cS1dZ8cA2Z4S0S4fS4dZ2Z20A2Z1A2A1A3S11S1A1A3A3A3A3A3S5A5").
Definition O_uerr : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zec348A1S0Zec350A1S11S1A1S6A5").
Definition O_uout : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zec438A1S0Zec440A1S11S1A1S6A5").
Definition O_fin  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zec440A1S0Zec530A1S11S1A1S6A5").
Definition O_ofl  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z644ca8A1S0Z644cb8A1S11S1A1S6A5").
Definition O_tid  : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Z624510M0A1S0Z624514A1SfS1S1bG0Z4S20A3S11S1A1A3S5A5").

Definition ATX : Z := 0x644608.
Definition CALL_THUNK : Z := 0xd44e8.
Definition COV_HANDLER : Z := 0x7bdf0.
Definition AEF_GUARD : Z := 0x8c7b8.
Definition atx_cells0 : list cell := ltac2:(tb__ "0|5|
SfS1S1bS4cS1cZ4M0A2G0S0Z0A1M1A3SfS1S1bS4cS1cZ8M2A2G0S0Z1M3A1A3SfS1S1bS4cS1cZ10A2G2S0S4cS1cZ18A2M4A1A3SfS1S1bG4G2G1A3SfS1S1bS4cS1cZ20A2G2S0S21A1A3SfS1S1bS4cS1cZ120A2G2S0S22A1A3SfS1S1bS1cG3G1A3S11S1A1A3A3A3A3A3A3A3").
Definition O_atx0 : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0S1cA1S0S4cS1cZ220A2A1S44S5A5").
Definition O_atx1 : sobj := ltac2:(tb__ "0|5|
S3S0Z0A1M0S0S1cA1S0S4cS1cZ220A2A1SfS1S1bS4cS1cZ4M1A2G1G0A3SfS1S1bS4cS1cZ8M2A2G1S0Z2A1A3SfS1S1bS4cS1cZ10A2G2S0S4cS1cZ18A2M3A1A3SfS1S1bG3G2G0A3SfS1S1bS4cS1cZ20A2G2S0S21A1M4A3SfS1S1bS4cS1cZ120A2G2S0S22A1A3SfS1S1bS1cZ1G0A3SfS1S1bS4cS1cZ28A2G2G4A3SfS1S1bS4cS1cZ128A2G2S0S24A1A3S11S1A1A3A3A3A3A3A3A3A3A3S5A5").

Definition TRI : Z := 0x623a50.
Definition O_trix : sobj := ltac2:(tb__ "0|3|
S3S0Z0A1M0S0S1fA1M1S0S4cS1fZ14A2A1SfS1S9G1Z1M2S0G2A1A3SfS1S9S0S4cS1fZ4A2A1G2G0A3S11S1A1A3A3S6A5").
Definition O_xlk  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z644828A1S0Z64482cA1S11S1A1S6A5").
Definition O_nlkx : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z64484bA1S0Z64484cA1S11S1A1S6A5").
Definition O_regf : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Zedd40M0A1S0Zedd48A1SfS1S1bG0Z8S0Z1A1A3S11S1A1A3S5A5").
Definition O_dtf  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zedd90A1S0Zedd91A1S11S1A1S6A5").
Definition O_dso  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze9978A1S0Ze9980A1S11S1A1S6A5").
Definition O_fina : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze47f8A1S0Ze4808A1S11S1A1S6A5").
Definition O_glx  : sobj := ltac2:(tb__ "0|2|
S3S0Z0A1M0S0Zeec70A1S0Zeecc0A1SfS1S1bZeec78Z8M1S0Z5fA1A3SfS1S1bZeec80G1S7PcA1A3SfS1S1bZeec88G1S7PdA1A3SfS1S1bZeecb0G1G0A3S11S1A1A3A3A3A3S5A5").
Definition O_cfl2 : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Z182fa0M0A1S0Z182fa8A1SfS1S1bG0Z8S0ZffffffffffffffffA1A3S11S1A1A3S5A5").
Definition O_cov  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z1832a0A1S0Z1832a1A1S11S1A1S6A5").

Definition O_ofile (n : Z) : sobj := ltac2:(tb__ "0|0|
S12S2L_;S4eVn;Z0A2S5dS5eVn;A1X12x2").
Definition O_osbuf (n : Z) : sobj := ltac2:(tb__ "0|0|
S12S2L_;S4eVn;Z0A2S61S62Vn;A1X12x2").

Definition O_afl2p : sobj := ltac2:(tb__ "0|2|
S3S0Z0A1S0Zeec4dA1M0S0Zeec4eA1SfS1S9G0Z1M1S0G1A1A3S11S1A1A3S5A5").
Definition O_afl2b : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zeec4eA1S0Zeec70A1SfS1S9S0Zeec5cA1Z4S0Z2A1A3S11S1A1A3S5A5").
Definition objs_exitP (ph : bool) (n : Z) : list sobj := ltac2:(tb__ "0|1|
S18S2SfS2S3eSfS2S36SfS2S37SfS2S33Vn;A1SfS2S35Vn;A1SfS2S2eSfS2S3bSfS2S3cSfS2S2fSfS2S34SfS2S39SfS2S63SfS2S12S2Lph;Vph;S29S28X12x2SfS2S3dSfS2S32SfS2S38SfS2S2dSfS2S2cSfS2S30SfS2S64SfS2S26SfS2S31SfS2S65SfS2S66SfS2S60SfS2S2aSfS2S2bSfS2S5fSfS2S5aSfS2S5bSfS2S27S11S2A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S12S16S2A1Lph;Vph;SfS2S3aG0A3G0X12x2A3").
Definition objs_exit (n : Z) : list sobj := objs_exitP true n.
Definition objs_exit0 (n : Z) : list sobj := objs_exitP false n.

Definition facts_exit : list sprop := ltac2:(tb__ "0|1|
SfS8SdPaZ4A2SfS8SaS0Z7fff7ff01000A1S1eA2SfS8SaS1eS0S4fS4dZ2M0Z2fA2Ze0A2A1A2SfS8SaS0Z1A1S20A2SfS8SaS20S0S4dG0Z16A2A1A2S11S8A1A3A3A3A3A3").

Definition reg_X (c : Z) (r : nat) : sv := ltac2:(tb__ "0|1|
S10S4Lr;Vr;S0Z0A1S10S10S4Ln;R1S7S57S56U3cVr;A2A1A1M0S10S10S4Ln0;R1S1eS10S10S4Ln1;R1S0Z10800A1S10S10S4Ln2;R1S0Z6245b8A1S10S10S4Ln3;R1G0S10S10S4Ln4;R1G0S10S10S4Ln5;R1G0S10S10S4Ln6;R1G0S10S10S4Ln7;R1G0S10S10S4Ln8;R1S0Vc;A1S10G0Ln9;X10x2Ln8;X10x2Ln7;X10x2Ln6;X10x2Ln5;X10x2Ln4;X10x2Ln3;X10x2Ln2;X10x2Ln1;X10x2Ln0;X10x2Ln;X10x2").
Definition regs_X (c : Z) : list sv := map (reg_X c) (seq 0 32).
Definition fregs_X : list sv := ltac2:(tb__ "0|0|
S58S10S4S10S7S57S56U14R1A2A1A1Lr;S59U0U20A2A4").

Definition axX (S : sstate) : axst := ltac2:(tb__ "0|0|
S54VS;S11S15S4S4A2A1S0S5cA1A3").
Definition Pre_exitP_S (ph : bool) (n c : Z) : sstate := ltac2:(tb__ "0|0|
SeS46S4aVc;A1S48ScS17S4A1S49Vph;Vn;A2S47S67S19A9").
Definition Pre_exitP (ph : bool) (n c : Z) : axst := ltac2:(tb__ "0|0|
S45S23Vph;Vn;Vc;A3A1").
Definition Pre_exit_S (n c : Z) : sstate := Pre_exitP_S true n c.
Definition Pre_exit (n c : Z) : axst := Pre_exitP true n c.
Definition Pre_exit0_S (n c : Z) : sstate := Pre_exitP_S false n c.
Definition Pre_exit0 (n c : Z) : axst := Pre_exitP false n c.
Definition supportedP (ph : bool) : list (Z * Z) := ltac2:(tb__ "0|5|
S12S16S15S1aS1aA2M0A1Lph;Vph;SfG0S13S1aS1aZ0M1G1A4SfG0S13S1aS1aG1Z2M2A4M3SfG0S13S1aS1aZ1G1A4SfG0S13S1aS1aG2G1A4SfG0S13S1aS1aZ3G1A4SfG0S13S1aS1aZ4G1A4S11G0A1M4A3A3A3A3A3A3SfG0G3G4A3X12x2").

Lemma Pre_exitP_wf : ltac2:(tb__ "0|0|
S12S1aS1aS55S15S1aS1aA2S13S1aS1aR2R1A4S4bR3A1A3S52S51S12SbS23R4R3R2A3A1S14A3S51S12S53S42R4R3R2A3A1S14A3A2F_;Fc;Fn;Fph;").
Proof.
  intros [|] n c H; repeat (destruct H as [H|H]; [injection H as <- <-; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]); destruct H.
Qed.
Lemma Pre_exit_wf : ltac2:(tb__ "0|3|
S1aS1aS55S15S1aS1aA2M0S13S1aS1aR2R1A4SfG0S13S1aS1aZ0M1G1A4SfG0S13S1aS1aG1Z2M2A4SfG0S13S1aS1aZ1G1A4SfG0S13S1aS1aG2G1A4SfG0S13S1aS1aZ3G1A4SfG0S13S1aS1aZ4G1A4S11G0A1A3A3A3A3A3A3A3S52S51S12SbS43R3R2A2A1S14A3S51S12S53S3fR3R2A2A1S14A3A2F_;Fc;Fn;").
Proof. intros n c H. exact (Pre_exitP_wf true n c H). Qed.
Lemma Pre_exit0_wf : ltac2:(tb__ "0|1|
S1aS1aS55S15S1aS1aA2M0S13S1aS1aR2R1A4SfG0S13S1aS1aZ0Z2A4S11G0A1A3A3S52S51S12SbS41R3R2A2A1S14A3S51S12S53S40R3R2A2A1S14A3A2F_;Fc;Fn;").
Proof. intros n c H. exact (Pre_exitP_wf false n c H). Qed.

Fixpoint zn_bytes (k : nat) : list byte :=
  match k with O => [] | S k' => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zn_bytes k' end.
Definition PEND (n : Z) : list byte := zn_bytes (Z.to_nat (n - 1)).
End DrvExitIface.

