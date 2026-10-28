(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section Heap.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Definition aheap_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lzok_same_mem : forall L S Zr ms ms' mo,
    lzok asegs L S Zr (mkCfg ms mo) -> ms_mem ms' = ms_mem ms -> lzok asegs L S Zr (mkCfg ms' mo).
  Proof.
    intros L S Zr ms ms' mo OK Hm. destruct OK as [R1 R2 R3 R4 R5 R6 R7]. split; try assumption.
    unfold hidden_zero_on in *. cbn [cfg_ms] in *. intros a Ha Hz. rewrite Hm. apply R4; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition renorm (msF : machine_state) (regs : bvmap 5 word) : machine_state :=
    {| ms_regs := mkR_of regs; ms_fregs := ms_fregs msF; ms_pc_val := ms_pc_val msF; ms_svc_pending := ms_svc_pending msF;
       ms_resv := ms_resv msF; ms_fcsr := ms_fcsr msF; ms_mem := ms_mem msF; ms_rom := ms_rom msF |}.

  Lemma vis_norm : forall s L S msF mo regs pc mem,
    (forall msF0, as_VIS H s msF0 = restrict L S msF0) ->
    as_VIS H s msF = mkst regs pc mem rom ->
    cfg_eqv (mkCfg msF mo) (mkCfg (renorm msF regs) mo)
    /\ as_VIS H s (renorm msF regs) = MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem rom
    /\ ms_mem (renorm msF regs) = ms_mem msF.
  Proof.
    intros s L S msF mo regs pc mem HVIS HV. rewrite HVIS in HV.
    unfold restrict, restrict_by, with_mem in HV.
    pose proof (f_equal ms_regs HV) as E1. pose proof (f_equal ms_fregs HV) as E2. pose proof (f_equal ms_pc_val HV) as E3.
    pose proof (f_equal ms_svc_pending HV) as E4. pose proof (f_equal ms_resv HV) as E5. pose proof (f_equal ms_fcsr HV) as E6.
    pose proof (f_equal ms_mem HV) as E7. pose proof (f_equal ms_rom HV) as E8. cbn in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [|split; [|reflexivity]].
    - split; [|reflexivity]. unfold renorm. repeat split; cbn; try reflexivity; try (rewrite E1; apply mkR_of_eqv); try apply fregs_eqv_refl.
    - rewrite HVIS. unfold restrict, restrict_by, with_mem, renorm, MS. cbn. rewrite E2, E3, E4, E5, E6, E7, E8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma drv_norm : forall s msF mo regs pc mem K,
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall msFn, as_VIS H s msFn = MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem rom ->
       as_AKREL H s (mkCfg msFn mo) -> realizes asegs (mkCfg msFn mo) K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs pc mem K HV HA HK.
    destruct (adl_lazy H DL s) as (L & S & Zr & HVIS & HLZ & HTR).
    destruct (vis_norm s L S msF mo regs pc mem HVIS HV) as (EQ & HVn & Hmem).
    apply (realizes_eqv asegs (mkCfg (renorm msF regs) mo)); [| apply cfg_eqv_sym; exact EQ].
    apply HK; [exact HVn|].
    apply (HTR msF mo (renorm msF regs) mo HA); [| reflexivity | reflexivity].
    apply (lzok_same_mem L S Zr msF); [apply HLZ; exact HA | exact Hmem].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aevt_call : forall (P : machine_state -> Prop) s msF mo regs pc mem K,
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    evt asegs P (MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem rom) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros P s msF mo regs pc mem K HV HA HE HK.
    apply (drv_norm s msF mo regs pc mem K HV HA). intros msFn HVn HAn.
    apply (adl_sr H DL (fun c' => exists msF' mo', c' = mkCfg msF' mo' /\ as_AKREL H s (mkCfg msF' mo') /\ as_MPRES H mo mo' /\ P (as_VIS H s msF'))).
    - apply (ah_lift H HH P _ s msFn _ mo HAn HVn HE).
      intros msF' mo' HA' HMP HP. apply (ah_done H HH). exists msF', mo'. auto.
    - intros c' (msF' & mo' & -> & HA' & HMP & HP). apply HK; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma amalloc_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LB : list block) (n lo B : Z) (errv : word) (ra : Z) (CH : list (Z * Z)) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 AMALLOC_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 28 ->      (* [comment removed for export] *)
    as_RHEAP H s LB mem -> as_alloc_ok H s LB n -> as_Cm H n <= as_AL H s ->
    as_rauxv_ok H mem B -> bv_unsigned (getr regs 2) <= B ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AMALLOC_STACK ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->      (* [comment removed for export] *)
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem -> ACONST mem ->
    as_chain H mem (bv_unsigned (getr regs 8)) CH -> trace_ok (as_TR H) APC0_MALLOC (ra :: map snd CH) ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (A : Z) (p : bptr) (s' : as_St H)
            (errv' : word) (junk : list byte),
        as_VIS H s' msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 A ->
        mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> as_rauxv_ok H mem' B ->
        apres H LB (bv_unsigned (getr regs 2)) mem mem' ->
        ablock_range H A n -> as_RHEAP H s' ((p, A, n) :: LB) mem' ->
        rw_cells asegs mem' A [CB (Z.to_nat n) junk] -> addressable mem' A n -> ACONST mem' ->
        as_AL H s' >= as_AL H s - as_Cm H n ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LB n lo B errv ra CH K HV HA Hra Hra64 Hra2 Htp Ha0 Hn HRH HAL HCM HAU HB HSTK HLO HLO2 HSP16 HERR HINV HAC HCH HTRC HK.
    apply (drv_norm s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0 in HVn.
    apply (adl_sr H DL (malloc_post H (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) s LB n lo B mem mo)).
    { apply (ah_malloc H HH (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                    (getr regs 8) (getr regs 9) (Z_to_bv 64 n) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                    (getr regs 29) (getr regs 30) (getr regs 31)
                    bvmap_empty (Z_to_bv 32 0) msFn mem s LB n lo B errv mo CH);
        try assumption; try reflexivity.
      - rewrite <- Htp. exact HERR.
      - rewrite unsigned_lit by lia. exact HTRC. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & p & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HBR & HRH' & HBLK & HADDR & HAC' & HALW).
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
    eapply (HK _ m' msF' mo' A p s' errv' junk Hms HKR' HMP); try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HBR; try exact HRH'; try exact HBLK; try exact HADDR; try exact HAC'; try exact HALW.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  Lemma afree_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (ra : Z) (CH : list (Z * Z)) (bs sbs : list byte) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 AFREE_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 A ->
    as_RHEAP H s LB mem -> In (p, A, n) LB -> as_Cf H n <= as_AL H s ->
    rw_cells asegs mem A [CB (Z.to_nat n) bs] -> SHAD mem A sbs -> Z.of_nat (length sbs) = nsh n ->
    as_rauxv_ok H mem B -> bv_unsigned (getr regs 2) <= B ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AFREE_STACK ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->      (* [comment removed for export] *)
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem -> ACONST mem ->
    as_chain H mem (bv_unsigned (getr regs 8)) CH -> trace_ok (as_TR H) APC0_FREE (ra :: map snd CH) ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H),
        as_VIS H s' msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv] -> as_rauxv_ok H mem' B ->
        apres H (as_lb_remove H p LB) (bv_unsigned (getr regs 2)) mem mem' ->
        as_RHEAP H s' (as_lb_remove H p LB) mem' -> ACONST mem' ->
        as_AL H s' >= as_AL H s - as_Cf H n ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LB p A n lo B errv ra CH bs sbs K HV HA Hra Hra64 Hra2 Htp Ha0 HRH HIN HCF HBS HSH HSHL HAU HB HSTK HLO HLO2 HSP16
           HERR HINV HAC HCH HTRC HK.
    apply (drv_norm s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0 in HVn.
    apply (adl_sr H DL (free_post H (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) s LB p n lo B errv mem mo)).
    { apply (ah_free H HH (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                    (getr regs 8) (getr regs 9) (Z_to_bv 64 A) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                    (getr regs 29) (getr regs 30) (getr regs 31)
                    bvmap_empty (Z_to_bv 32 0) msFn mem s LB p A n lo B errv mo CH bs sbs);
        try assumption; try reflexivity.
      - rewrite <- Htp. exact HERR.
      - rewrite unsigned_lit by lia. exact HTRC. }
    intros c' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HRH' & HAC' & HALW).
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
    eapply (HK _ m' msF' mo' s' Hms HKR' HMP); try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HRH'; try exact HAC'; try exact HALW.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  Lemma afree_null_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model)
      (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (ra : Z) (CH : list (Z * Z)) (K : TSet),
    as_VIS H s msF = mkst regs (Z_to_bv 64 AFREE_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 0 ->
    as_RHEAP H s LB mem -> as_Cf H 0 <= as_AL H s ->
    as_rauxv_ok H mem B -> bv_unsigned (getr regs 2) <= B ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AFREE_STACK ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->      (* [comment removed for export] *)
    rw_cells asegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv asegs mem -> ACONST mem ->
    as_chain H mem (bv_unsigned (getr regs 8)) CH ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H),
        as_VIS H s' msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
        (forall r, In r aheap_kept -> getr regs' r = getr regs r) ->
        mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells asegs mem' (errno_addr (getr regs 4)) [C4 errv] -> as_rauxv_ok H mem' B ->
        apres H LB (bv_unsigned (getr regs 2)) mem mem' ->
        as_RHEAP H s' LB mem' -> ACONST mem' ->
        as_AL H s' >= as_AL H s - as_Cf H 0 ->
        realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros regs mem msF mo s LB lo B errv ra CH K HV HA Hra Hra64 Hra2 Htp Ha0 HRH HCF HAU HB HSTK HLO HLO2 HSP16 HERR HINV HAC HCH HK.
    apply (drv_norm s msF mo regs _ mem K HV HA). intros msFn HVn HAn.
    rewrite mkR_of_getr in HVn. rewrite Hra, Htp, Ha0 in HVn.
    apply (adl_sr H DL (free_null_post H (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
                         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                         (getr regs 25) (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) s LB lo B errv mem mo)).
    { apply (ah_free_null H HH (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 5) (getr regs 6) (getr regs 7)
                    (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                    (getr regs 29) (getr regs 30) (getr regs 31)
                    bvmap_empty (Z_to_bv 32 0) msFn mem s LB lo B errv mo CH);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    intros c' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HRH' & HAC' & HALW).
    destruct c' as [msF' mo']. cbn [cfg_ms cfg_model] in *.
    rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
    eapply (HK _ m' msF' mo' s' Hms HKR' HMP); try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HRH'; try exact HAC'; try exact HALW.
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite Htp. exact HERR'.
  Qed.
End Heap.
