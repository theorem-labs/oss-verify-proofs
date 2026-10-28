(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BStoreOk BShapeAlg BReach BegsEquivM BainEqv BeapCeil BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 BXXRep DvB_FuzzStmt RtB_Iface BsDrvHeap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
Import BPropExec.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Fz.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variable P : fuzz_params.
  Hypothesis FZ : fuzz_stmt H P.
  Context {fx : DFP}.

  Let rom := seg_rom asegs.

  Lemma afuzz_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LB : list block) (D N lo B shi : Z) (ds : list byte) (errv : word) (ra : Z) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 P_FUZZ_ENTRY) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    FPSteps.frm_zero dfp_csr ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 D -> getr regs 11 = Z_to_bv 64 N ->
    bytes_at asegs mem D ds -> Z.of_nat (length ds) = N -> N < 2 ^ 26 -> D mod 16 = 0 ->
    (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = AFUZZ_EMPTY) ->
    as_RHEAP H s LB mem ->
    lb_small LB + fz_small P <= RT_SMALL_MAX -> Z.of_nat (length LB) + fz_cnt P <= RT_CNT_MAX -> nlarge LB + fz_large P <= RT_LARGE_MAX ->
    as_rauxv_ok H mem B -> bv_unsigned (getr regs 2) <= B -> B < 2 ^ 64 ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AFUZZ_STACK ->
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem ->
    fz_inv P mem -> ACONST mem ->
    (1 <= N -> addressable mem D N) ->
    as_RFS H [] mem -> stack0 mem lo shi -> bv_unsigned (getr regs 2) <= shi ->
    (bv_unsigned (getr regs 8) <= aceil \/ bv_unsigned (getr regs 8) mod 8 <> 0) ->
    pf_ok (as_TR H) (fz_pf P) ra [] -> fz_tr_ok P H ->
    fz_cost P N <= as_AL H s ->
    (forall (fx' : DFP) (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H)
            (LB' : list block) (XS : list (Z * Z)) (errv' : word),
        FPSteps.frm_zero (@dfp_csr fx') ->
        as_VIS H s' msF' = @mkst fx' regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> as_rauxv_ok H mem' B ->
        as_RHEAP H s' LB' mem' -> Permutation LB' LB ->
        Forall (fs_scratch H []) XS -> xpres H LB (bv_unsigned (getr regs 2)) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) mem mem' ->
        as_RFS H [] mem' -> ACONST mem' -> stack0 mem' lo shi ->
        as_AL H s' >= as_AL H s - fz_cost P N ->
        fz_inv P mem' ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LB D N lo B shi ds errv ra K HV HA HFRM Hra Hra64 Hra2 Htp Ha0 Ha1 Hds Hlen HN HD16 HinLB Hempty HRH HLIVE HCNT HLRG
           HAU HB HB64 Hsp16 HSTK HLO HLO2 HERR HINV HLAT HAC HADDR HRFS HST0 Hshi Hs0 HPF HTR HAL HK.
    apply (drv_norm H DL s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0, Ha1 in HVn.
    apply (adl_sr H DL (fuzz_post H P (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) dfp_regs dfp_csr s LB [] N lo B shi mem mo)).
    { apply (FZ (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (Z_to_bv 64 D) (Z_to_bv 64 N) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)
                dfp_regs dfp_csr msFn mem mo s LB [] [] D N lo B shi ds errv);
        try assumption; try reflexivity;
        first [ rewrite <- Htp; exact HERR
              | rewrite unsigned_lit by lia; first [exact Hra2 | exact HPF]
              | unfold AFS_MAXLIVE_BP; cbn; lia
              | apply (ah_chain_nil H HH); exact Hs0
              | intros fp' ra' []
              | idtac ]. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' & XS & F' & fc' &
               Hms & HFRM' & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HRH' & HPERM & HSCR & HX & HRFS' & HAC' & HST0' & HALW & HFI').
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (@mkst (mkDFP F fc) R pc m ro) in Hms.
    eapply (HK (mkDFP F' fc') _ m' msF' mo' s' LB' XS errv' HFRM' Hms HKR' HMP); try exact HINV'; try exact HSTK'; try exact HAU'; try exact HRH';
      try exact HPERM; try exact HSCR; try exact HX; try exact HRFS'; try exact HAC'; try exact HST0'; try exact HALW; try exact HFI'.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.
End Fz.
