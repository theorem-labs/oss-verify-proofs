(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsDrvHeap.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Fz.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable L : alib.
  Hypothesis DL : asan_driver_laws H.
  Hypothesis FZ : fuzz_stmt H L.

  Let rom := seg_rom asegs.

  Lemma afuzz_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LIB LBc : list block) (st : al_st L) (D N lo B shi : Z) (ds : list byte) (errv : word) (ra : Z) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 P_FUZZ_ENTRY) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 D -> getr regs 11 = Z_to_bv 64 N ->
    bytes_at asegs mem D ds -> Z.of_nat (length ds) = N -> N < 2 ^ 26 -> D mod 16 = 0 ->
    (1 <= N -> exists pD, In (pD, D, N) LBc) -> (N = 0 -> D = AFUZZ_EMPTY) ->
    as_RHEAP H s (LIB ++ LBc) mem -> al_LIBST L st LIB mem ->
    lb_bytes (LIB ++ LBc) + afuzz_live L st <= as_LIVE_MAX H -> Z.of_nat (length (LIB ++ LBc)) + afuzz_cnt L st <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H mem B -> aauxv_ok mem B -> bv_unsigned (getr regs 2) <= B -> B < 2 ^ 64 ->    (* [comment removed for export] *)
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AFUZZ_STACK ->
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem -> arelro_lib mem ->
    ACONST mem ->
    (1 <= N -> addressable mem D N) ->
    as_RFS H [] mem -> stack0 mem lo shi -> bv_unsigned (getr regs 2) <= shi ->
    (bv_unsigned (getr regs 8) <= aceil \/ bv_unsigned (getr regs 8) mod 8 <> 0) ->       (* [comment removed for export] *)
    pf_ok (as_TR H) (al_PF L) ra [] -> al_tr_ok L H -> (al_frames L <= AFS_MAXLIVE)%nat ->
    fuzz_cost H L N <= as_AL H s ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H)
            (LIB' LBc' : list block) (st' : al_st L) (XS : list (Z * Z)) (errv' : word),
        as_VIS H s' msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        mem_inv asegs mem' -> arelro_lib mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> as_rauxv_ok H mem' B ->
        as_RHEAP H s' (LIB' ++ LBc') mem' -> Permutation LBc' LBc ->
        al_LIBST L st' LIB' mem' -> al_is_fresh L st' = false ->
        Z.of_nat (length LIB') <= ALIB_CNT_MAX -> lb_bytes LIB' <= ALIB_BYTES_MAX -> (al_is_fresh L st = false -> LIB' = LIB) ->
        Forall (fs_scratch H []) XS -> xpres H LBc (bv_unsigned (getr regs 2)) (AERRNO_X ++ al_LIBX L ++ XS) mem mem' ->
        as_RFS H [] mem' -> ACONST mem' -> stack0 mem' lo shi ->
        as_AL H s' >= as_AL H s - fuzz_cost H L N ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LIB LBc st D N lo B shi ds errv ra K HV HA Hra Hra64 Hra2 Htp Ha0 Ha1 Hds Hlen HN HD16 HinLB Hempty HRH HLST HLIVE HCNT
           HAU HAUXV HB HB64 Hsp16 HSTK HLO HLO2 HERR HINV HREL HAC HADDR HRFS HST0 Hshi Hs0 HPF HTR HFR HAL HK.
    apply (drv_norm H DL s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0, Ha1 in HVn.
    apply (adl_sr H DL (fuzz_post H L (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) s LIB LBc st [] N lo B shi mem mo)).
    { apply (FZ (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (Z_to_bv 64 D) (Z_to_bv 64 N) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)
                bvmap_empty (Z_to_bv 32 0) msFn mem mo s LIB LBc st [] [] D N lo B shi ds errv);
        try assumption; try reflexivity;
        first [ rewrite <- Htp; exact HERR
              | rewrite unsigned_lit by lia; first [exact Hra2 | exact HPF]
              | cbn [length]; lia
              | apply (ah_chain_nil H HH); exact Hs0
              | intros fp' ra' []
              | idtac ]. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LIB' & LBc' & st' & XS &
               Hms & HKR' & HMP & HINV' & HREL' & HSTK' & HERR' & HAU' & HRH' & HPERM & HLST' & HNF & HLC & HLB & HKEEP & HSCR & HX &
               HRFS' & HAC' & HST0' & HALW).
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
    eapply (HK _ m' msF' mo' s' LIB' LBc' st' XS errv' Hms HKR' HMP); try exact HINV'; try exact HREL'; try exact HSTK'; try exact HAU';
      try exact HRH'; try exact HPERM; try exact HLST'; try exact HNF; try exact HLC; try exact HLB; try exact HKEEP; try exact HSCR; try exact HX;
      try exact HRFS'; try exact HAC'; try exact HST0'; try exact HALW.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.
End Fz.
