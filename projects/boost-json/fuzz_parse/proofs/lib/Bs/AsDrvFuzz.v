(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0
  CXXRep Fuzz_stmt AsDrvHeap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~03asr0casan_rt_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~l0h0asan_driver_laws79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt~~~~~~q69fuzz_stmt" s.   (* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Fz.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jd$0").
  Hypothesis HH : ltac2:(zQ "10!k2@2$0?5HCEIL?1H").
  Hypothesis DL : ltac2:(zQ "10!p2@1$0?1H").
  Hypothesis FZ : ltac2:(zQ "10!u5@2$0?5HCEIL?1H").

  Let rom := seg_rom asegs.

  Lemma afuzz_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LB : list block) (D N lo B shi : Z) (ds : list byte) (errv : word) (ra : Z) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 P_FUZZ_ENTRY) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 D -> getr regs 11 = Z_to_bv 64 N ->
    bytes_at asegs mem D ds -> Z.of_nat (length ds) = N -> N < 2 ^ 26 -> D mod 16 = 0 ->
    (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = AFUZZ_EMPTY) ->
    as_RHEAP H s LB mem ->
    lb_bytes LB + AFUZZ_LIVE <= as_LIVE_MAX H -> Z.of_nat (length LB) + AFUZZ_CNT <= as_LIVE_CNT_MAX H ->
    (forall c, 1 <= c <= 30 -> class_bytes LB c <= AFUZZ_CLS) ->
    as_rauxv_ok H mem B -> bv_unsigned (getr regs 2) <= B -> B < 2 ^ 64 ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AFUZZ_STACK ->
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem ->
    bj_statics mem -> ACONST mem ->
    (1 <= N -> addressable mem D N) ->
    as_RFS H [] mem -> stack0 mem lo shi -> bv_unsigned (getr regs 2) <= shi ->
    (bv_unsigned (getr regs 8) <= aceil \/ bv_unsigned (getr regs 8) mod 8 <> 0) ->       (* [comment removed for export] *)
    pf_ok (as_TR H) PF_FUZZ ra [] -> fuzz_tr_ok H ->
    fuzz_cost H N <= as_AL H s ->
    FP.frm0 (@fp_csr fx) ->                                                            (* [comment removed for export] *)
    (forall (fx' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H)
            (LB' : list block) (XS : list (Z * Z)) (errv' : word),
        as_VIS H s' msF' = @mkst fx' regs' (Z_to_bv 64 ra) mem' rom -> FP.frm0 (@fp_csr fx') ->       (* [comment removed for export] *)
        as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> as_rauxv_ok H mem' B ->
        as_RHEAP H s' LB' mem' -> Permutation LB' LB ->
        Forall (fs_scratch H []) XS -> xpres H LB (bv_unsigned (getr regs 2)) XS mem mem' ->
        as_RFS H [] mem' -> ACONST mem' -> bj_statics mem' -> stack0 mem' lo shi ->
        as_AL H s' >= as_AL H s - fuzz_cost H N ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LB D N lo B shi ds errv ra K HV HA Hra Hra64 Hra2 Htp Ha0 Ha1 Hds Hlen HN HD16 HinLB Hempty HRH HLIVE HCNT HCLS
           HAU HB HB64 Hsp16 HSTK HLO HLO2 HERR HINV HLAT HAC HADDR HRFS HST0 Hshi Hs0 HPF HTR HAL HFRM HK.
    apply (drv_norm H DL s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0, Ha1 in HVn.
    apply (adl_sr H DL (fuzz_post H (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr s LB [] N lo B shi mem mo)).
    { apply (FZ (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (Z_to_bv 64 D) (Z_to_bv 64 N) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)
                fp_regs fp_csr msFn mem mo s LB [] [] D N lo B shi ds errv);
        try assumption; try reflexivity; try exact HFRM;
        first [ rewrite <- Htp; exact HERR
              | rewrite unsigned_lit by lia; first [exact Hra2 | exact HPF]
              | unfold AFS_MAXLIVE; cbn; lia
              | apply (ah_chain_nil H HH); exact Hs0
              | intros fp' ra' []
              | idtac ]. }
    (intros c' nd_i1; ndestruct nd_i1 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' & XS & F' & fc' &
               Hms & HFRM' & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HRH' & HPERM & HSCR & HX & HRFS' & HAC' & HLAT' & HST0' & HALW)).
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (@mkst (mkFP F fc) R pc m ro) in Hms.   (* [comment removed for export] *)
    eapply (HK (mkFP F' fc') _ m' msF' mo' s' LB' XS errv' Hms HFRM' HKR' HMP); try exact HINV'; try exact HSTK'; try exact HAU'; try exact HRH';
      try exact HPERM; try exact HSCR; try exact HX; try exact HRFS'; try exact HAC'; try exact HLAT'; try exact HST0'; try exact HALW.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.
End Fz.
