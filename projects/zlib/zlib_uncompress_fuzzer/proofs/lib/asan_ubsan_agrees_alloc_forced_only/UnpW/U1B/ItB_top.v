(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItableModel InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BIface U2BGlue ItB_base ItB_ldefs ItB_body ItB_pro ItB_epi U2BIface_fit2_draft ItB_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma it_ret_cases : forall ty lf lo codes nx bits cf wf,
  let r := resA ty lf lo codes nx bits cf wf in it_ret r = 0 \/ it_ret r = 1 \/ it_ret r = -1.
Proof.
  intros. subst r. rewrite res_phases.
  destruct (_ =? 0); [left; reflexivity|].
  destruct (itm_reject _ _ _); [right; right; reflexivity|].
  destruct (it_not_enough _ _); [right; left; reflexivity|].
  destruct (it_loop _ _ _); [left| right; left]; reflexivity.
Qed.

Section Top.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Notation FB2 F := (mkABlock (ABFake 2) F 256).

(* [comment removed for export] *)
Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Hypothesis SM2 : SM2_stmt AI fflag rng_fs.

Section Core.
  Variables (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (st : astate) (LB : list ablock) (ps : AsanCtrl.aptr) (S lo : Z).
  Variables (ty : codetype) (lf cf wf : Z -> Z) (lens_ofs codes nx bits : Z) (PB PO : Z) (pre mid : list cell) (obw : word).
  Notation SP := (bv_unsigned sp).
  Notation RES := (resA ty lf lens_ofs codes nx bits cf wf).
  Notation WR := [(S + 136, S + 144); (S + 160, S + 168); (S + 808, S + 7160)].

  Definition it_core_post (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (it_ret RES)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo SP
      /\ AHEAP AI L RNG st LB m'
      /\ client_agree AI LB SP WR m m'
      /\ rw_cells bsegs m' S pre /\ rw_cells bsegs m' PB [C4 (Z_to_bv 64 (it_bits RES))] /\ rw_cells bsegs m' PO [C4 obw]
      /\ rw_cells bsegs m' (S + 144) mid /\ rw_cells bsegs m' (S + 160) [C8 (Z_to_bv 64 (S + 1384 + 4 * it_table RES))]
      /\ f16arr bsegs m' (S + 168) 320 lf
      /\ f16arr bsegs m' (S + 808) 288 (arr_get (it_work RES))
      /\ f32arr bsegs m' (S + 1384) 1444 (arr_get (it_tbl RES)).

  Hypothesis AM1 : atmost1_c2 LB.
  Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis HIN : In (HB ps S 7176) LB.
  Hypothesis TABC : itabs_client AI.
  (* [U14B] A2 2026-11-12: 1.4's inflate_state puts offset / extra / lencode / distcode (24 bytes) before lenbits
     (U2AObj.istate_cells, lenbits at S + 136), so the prefix up to lenbits is 26 cells, 136 bytes (1.3.1: 22 cells, 120);
     G's U1A cure by a worker *)
  Hypothesis PSZ : cells_size pre = 136%nat.
  Hypothesis MSZ : cells_size mid = 16%nat.
  Hypothesis PBC : (PB = S + 136 /\ PO = S + 140) \/ (PB = S + 140 /\ PO = S + 136).
  Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - ITABLE_STACK.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT0 : SP + 16 < al_top L.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RSTK0 : rng RNG lo (al_top L - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RFS : rng_fs L RNG.

  (* [comment removed for export] *)
  Ltac csz :=
    repeat match goal with
           | |- context [Z.of_nat (cells_size ?cs)] =>
               let v := eval cbv in (Z.of_nat (cells_size cs)) in
               lazymatch v with Zpos _ => idtac | Z0 => idtac end;
               change (Z.of_nat (cells_size cs)) with v
           end.
  Ltac djs := cbn [disjoint_from]; rewrite ?PSZ, ?MSZ; csz; repeat split; try exact I; lia.
  (* [comment removed for export] *)
  Ltac xrw H MU WM H' :=
    lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    lazymatch type of MU with munch _ _ ?m' =>
      assert (H' : rw_cells sg m' A cs) by (eapply rw_cells_transport; [exact H| exact MU| exact WM| djs]) end end.
  Ltac xf16 H MU WM H' :=
    lazymatch type of H with f16arr ?sg _ ?A ?n ?f =>
    lazymatch type of MU with munch _ _ ?m' =>
      assert (H' : f16arr sg m' A n f) by (eapply f16arr_transport; [exact H| exact MU| exact WM| cbn [disjoint_from]; repeat split; try exact I; lia]) end end.
  Ltac xf32 H MU WM H' :=
    lazymatch type of H with f32arr ?sg _ ?A ?n ?f =>
    lazymatch type of MU with munch _ _ ?m' =>
      assert (H' : f32arr sg m' A n f) by (eapply f32arr_transport; [exact H| exact MU| exact WM| cbn [disjoint_from]; repeat split; try exact I; lia]) end end.
  Ltac xstk H MU WM H' :=
    lazymatch type of H with stk ?sg _ ?l ?h =>
    lazymatch type of MU with munch _ _ ?m' =>
      assert (H' : stk sg m' l h) by (eapply stk_transport_disjoint; [exact H| exact MU| exact WM| cbn [disjoint_from]; repeat split; try exact I; lia]) end end.

  Lemma it_top_core : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem),
    AHEAP AI L RNG st LB m -> it_tabsh m -> u2_img m ->
    rw_cells bsegs m S pre -> rw_cells bsegs m PB [C4 (Z_to_bv 64 bits)] -> rw_cells bsegs m PO [C4 obw] ->
    rw_cells bsegs m (S + 144) mid -> rw_cells bsegs m (S + 160) [C8 (Z_to_bv 64 (S + 1384 + 4 * nx))] ->
    f16arr bsegs m (S + 168) 320 lf -> f16arr bsegs m (S + 808) 288 wf -> f32arr bsegs m (S + 1384) 1444 cf ->
    stk bsegs m lo SP -> mem_inv bsegs m ->
    evtF bsegs RNG (it_core_post m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cty ty)) (Z_to_bv 64 (S + 168 + 2 * lens_ofs)) (Z_to_bv 64 codes)
                  (Z_to_bv 64 (S + 160)) (Z_to_bv 64 PB) (Z_to_bv 64 (S + 808)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 A_ITABLE) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until m. intros AH TSH UIMG SPRE SPB SPO SMID SNXT LENS WORK CDS ST MI.
    (* [comment removed for export] *)
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
    pose proof (AI_block AI _ _ _ _ _ ps S 7176 AH HIN) as (_ & (SB & _ & _ & S16) & RS & RSS0 & _).
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2^64) in RSP.
    pose proof atop_range as ATR. unfold ITABLE_STACK in LOS.
    pose (SPA := (SP - 256) - (SP - 256) mod 32).
    assert (ESPA : SPA = (SP - 256) - (SP - 256) mod 32) by reflexivity. clearbody SPA.
    assert (SPAB : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (SPT : SP + 16 < KEND) by (unfold KEND; lia).
    assert (RSTK : rng RNG lo (SP - lo)) by (eapply rng_sub'; [exact RSTK0| lia]).
    assert (LOS1 : lo <= SP - 288) by lia.
    assert (LOS2 : lo <= SP - 288 - 2208) by lia.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (RSS : rng RNG (Z.shiftr S 3 + 2147450880) 897).
    { eapply rng_sub'; [exact RSS0|]. rewrite shadE. change (shlen (7176 + 7)) with 897. lia. }
    assert (BSS : 2148285104 <= Z.shiftr S 3 + 2147450880 /\ Z.shiftr S 3 + 2147450880 + 897 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART.
    destruct ART as (_ & GOT & _ & _ & SHB & SUAR & _).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (it_pro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo SPA RNG LOS1 LOC SP16 SPT ESPA RSTK RI);
        [exact ST| exact MI| exact GOT| exact SHB| exact UIMG| exact SUAR]. }
    cbv beta. intros ms1 (m1 & v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & v96 & v104 & v112 & v128 & v136 & v144 & q11 & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU1 WM1). constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
    assert (TSH1 : it_tabsh m1) by (eapply it_tabsh_mu; [exact TSH| exact MU1| cbn [disjoint_from]; repeat split; try exact I; lia]).
    assert (PBR : S + 136 <= PB <= S + 140 /\ S + 136 <= PO <= S + 140) by lia.
    assert (PBX : bx ((PB = S + 136 /\ PO = S + 140) \/ (PB = S + 140 /\ PO = S + 136))) by exact PBC. clear PBC.
    xrw SPRE MU1 WM1 SPRE1. xrw SPB MU1 WM1 SPB1. xrw SPO MU1 WM1 SPO1. xrw SMID MU1 WM1 SMID1. xrw SNXT MU1 WM1 SNXT1.
    xf16 LENS MU1 WM1 LENS1. xf16 WORK MU1 WM1 WORK1. xf32 CDS MU1 WM1 CDS1.
    clear SPRE SPB SPO SMID SNXT LENS WORK CDS TSH GOT SHB SUAR UIMG ST.
    (* [comment removed for export] *)
    pose proof SM2 as SM2'. unfold SM2_stmt, sm_stmt in SM2'.
    eapply evtF_cut.
    { unfold ASM2. eapply SM2';
        [exact AH1| exact AM1| exact MI1| rewrite USPA; exact STL1| exact LOC| rewrite USPA; unfold SM_STACK; lia| rewrite USPA; lia
        | exact TP| exact RSTK0| exact RI| exact RFS]. }
    cbv beta. unfold sm_post. rewrite USPA.
    intros ms2 (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & j0 & j1 & j2 & junk
                & -> & MI2 & STL2 & PRES & AH2 & F256 & FB & FTOP & FF2 & FSH2 & RF & RSF).
    change (Z.to_nat (256 - 32)) with 224%nat in FF2. change (256 / 8) with 32 in RSF.
    pose proof (ablk_lin _ _ FB) as (FB1 & FB2' & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (F8 : F mod 8 = 0) by (Z.div_mod_to_equations; lia).
    destruct (AI_fake_flag _ _ _ _ _ 2 F 256 AH2 ltac:(left; reflexivity)) as (_ & RG & GB & GTOP & GBL & GCI).
    remember (fflag L 2 F) as FLG eqn:EFLG.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    assert (GF : bx (FLG + 1 <= F \/ F + 256 <= FLG)).
    { pose proof (GBL (FB2 F) ltac:(left; reflexivity)) as X. cbn [ab_addr ab_size] in X. exact X. }
    assert (GS : bx (FLG + 1 <= S \/ S + 7176 <= FLG)).
    { pose proof (GBL (HB ps S 7176) ltac:(right; exact HIN)) as X. cbn [ab_addr ab_size] in X. exact X. }
    assert (SEPFS : S + 7176 <= F \/ F + 256 <= S).
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (FB2 F) AH2 ltac:(right; exact HIN) ltac:(left; reflexivity) ltac:(discriminate)) as D.
      cbn [ab_addr ab_size] in D. lia. }
    assert (BSF : 2148285104 <= Z.shiftr F 3 + 2147450880 /\ Z.shiftr F 3 + 2147450880 + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    rewrite shadE in RSF.
    (* [comment removed for export] *)
    assert (DSS : S + 7176 <= Z.shiftr F 3 + 2147450880 \/ Z.shiftr F 3 + 2147450880 + 32 <= S)
      by (clear - SB BSF; unfold ablk, AIMG_HI, KLS in SB; lia).
    assert (DSF : F + 256 <= Z.shiftr F 3 + 2147450880 \/ Z.shiftr F 3 + 2147450880 + 32 <= F)
      by (clear - FB BSF; unfold ablk, AIMG_HI, KLS in FB; lia).
    (* [comment removed for export] *)
    assert (FRB2 : rw_cells bsegs m2 (SP + -104) (it_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply aheap_pres_rw_cells; [exact PRES| exact FRB1|]. left. left. unfold it_SAVED. csz. lia. }
    assert (FRA2 : rw_cells bsegs m2 SPA [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 (Z_to_bv 64 (S + 160)); C8 v128; C8 v136; C8 v144]).
    { eapply aheap_pres_rw_cells; [exact PRES| exact FRA1|]. left. left. csz. lia. }
    assert (STG2 : stk bsegs m2 (SPA + 152) (SP + -104)) by (eapply aheap_pres_stk; [exact PRES| exact STG1| lia| lia]).
    assert (CRB : forall A n, S <= A -> A + n <= S + 7176 -> aclient_range CI LB SPA A n).
    { intros A n X1 X2. right. left. exists (HB ps S 7176). split; [exact HIN| cbn [ab_addr ab_size]; lia]. }
    assert (SPRE2 : rw_cells bsegs m2 S pre) by (eapply aheap_pres_rw_cells; [exact PRES| exact SPRE1| apply CRB; rewrite ?PSZ; lia]).
    assert (SPB2 : rw_cells bsegs m2 PB [C4 (Z_to_bv 64 bits)]) by (eapply aheap_pres_rw_cells; [exact PRES| exact SPB1| apply CRB; csz; lia]).
    assert (SPO2 : rw_cells bsegs m2 PO [C4 obw]) by (eapply aheap_pres_rw_cells; [exact PRES| exact SPO1| apply CRB; csz; lia]).
    assert (SMID2 : rw_cells bsegs m2 (S + 144) mid) by (eapply aheap_pres_rw_cells; [exact PRES| exact SMID1| apply CRB; rewrite ?MSZ; lia]).
    assert (SNXT2 : rw_cells bsegs m2 (S + 160) [C8 (Z_to_bv 64 (S + 1384 + 4 * nx))]) by (eapply aheap_pres_rw_cells; [exact PRES| exact SNXT1| apply CRB; csz; lia]).
    assert (LENS2 : f16arr bsegs m2 (S + 168) 320 lf) by (eapply (aheap_pres_f16arr AI); [exact PRES| exact LENS1| apply CRB; lia]).
    assert (WORK2 : f16arr bsegs m2 (S + 808) 288 wf) by (eapply (aheap_pres_f16arr AI); [exact PRES| exact WORK1| apply CRB; lia]).
    assert (CDS2 : f32arr bsegs m2 (S + 1384) 1444 cf) by (eapply (aheap_pres_f32arr AI); [exact PRES| exact CDS1| apply CRB; lia]).
    assert (TSH2 : it_tabsh m2) by (eapply (it_tabsh_pres AI); [exact TABC| exact PRES| exact TSH1]).
    pose proof (AI_rtcells AI _ _ _ _ _ AH2) as ART2. unfold artcells in ART2.
    destruct ART2 as (_ & GOT2 & RIC2 & REAL2 & SHB2 & _ & INI2 & LAY2 & _).
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 617260)) with (Z_to_bv 64 617260) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply evtF_cut.
    { eapply (it_hdr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo SPA RNG LOS1 LOC SP16 SPT ESPA RSTK RI
                     F PB (S + 808) (S + 168 + 2 * lens_ofs) F256 FB FTOP LOS2 RF);
        [rewrite shadE; exact RSF| exact STL2| exact MI2| exact GOT2| exact RIC2| exact SHB2| exact INI2| exact LAY2| exact REAL2| exact FRA2| exact FF2| exact FSH2]. }
    cbv beta.
    intros ms3 (m3 & q1 & q5 & q6 & q7 & q10 & q11' & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & jb8 & jb32 & jb120 & of
                & -> & MU3 & WM3 & MI3 & STL3 & FRA3 & FH3 & CNT3 & FMID3 & OFFS3 & FTL3 & FSH3).
    assert (AH3 : AHEAP AI L RNG st (FB2 F :: LB) m3).
    { eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3).
      constructor; [cbn [fst snd]; apply acr_stack; lia|].
      constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 F 256); [left; reflexivity| lia| lia]|].
      constructor; [cbn [fst snd]; apply (acr_fake_sh AI _ 2 F 256 F 32); [left; reflexivity| exact F8| lia| lia| lia]| constructor]. }
    xrw FRB2 MU3 WM3 FRB3. xstk STG2 MU3 WM3 STG3.
    xrw SPRE2 MU3 WM3 SPRE3. xrw SPB2 MU3 WM3 SPB3. xrw SPO2 MU3 WM3 SPO3. xrw SMID2 MU3 WM3 SMID3. xrw SNXT2 MU3 WM3 SNXT3.
    xf16 LENS2 MU3 WM3 LENS3. xf16 WORK2 MU3 WM3 WORK3. xf32 CDS2 MU3 WM3 CDS3.
    assert (TSH3 : it_tabsh m3).
    { eapply it_tabsh_mu; [exact TSH2| exact MU3|]. clear - FB BSF LOC ATR SPAB. unfold ablk, AIMG_HI, KLS in FB.
      cbn [disjoint_from]. repeat split; try exact I; lia. }
    clear FRB1 FRA1 STL1 STG1 SPRE1 SPB1 SPO1 SMID1 SNXT1 LENS1 WORK1 CDS1 TSH1.
    clear FRB2 FRA2 STG2 SPRE2 SPB2 SPO2 SMID2 SNXT2 LENS2 WORK2 CDS2 TSH2 FF2 FSH2 STL2 GOT2 RIC2 REAL2 SHB2 INI2 LAY2.
    (* [comment removed for export] *)
    assert (SHS3 : shadow_bytes m3 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
    { pose proof (AI_block AI _ _ _ _ _ ps S 7176 AH3 ltac:(right; exact HIN)) as (_ & _ & _ & _ & BSH3 & _).
      change 897 with (7176 / 8). apply ablock_sh0; [exact BSH3| reflexivity| lia| lia| lia]. }
    assert (SHCO : shadow_bytes m3 (Z.shiftr F 3 + 2147450880 + 4) (Z.shiftr F 3 + 2147450880 + 8) (fun _ => 0)
                   /\ shadow_bytes m3 (Z.shiftr F 3 + 2147450880 + 12) (Z.shiftr F 3 + 2147450880 + 16) (fun _ => 0)).
    { pose proof FSH3 as K. unfold it_shcells, c1z in K. remember (Z.shiftr F 3 + 2147450880) as SHF eqn:ESHF.
      rw_split K 4%nat K0 K1. rw_split K1 4%nat K4 K2. rw_split K2 4%nat K8 K3. rw_split K3 4%nat K12 K5.
      apply c1z4_sh0 in K4; [| lia]. apply c1z4_sh0 in K12; [| lia].
      replace (SHF + 4 + 4) with (SHF + 8) in K4 by lia. replace (SHF + 12 + 4) with (SHF + 16) in K12 by lia.
      split; [exact K4| exact K12]. }
    destruct SHCO as [SHC3 SHO3].
    assert (CX : itb_ctx RNG SP SPA S F PB ATOP m3).
    { unfold itb_ctx, itb_W. split; [| split; [| split]].
      - unfold bx in PBX. repeat split; try lia.
      - split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RF|]. split; [exact RS|]. split; [exact RSS|]. split; [exact RSF|].
        split; [exact RI|]. eapply rng_sub'; [exact RISH| lia].
      - split; [exact SHS3|]. split; [exact SHC3|]. split; [exact SHO3| exact TSH3].
      - clear - BSS BSF SB FB PBR SPAB LOC LOS1 ATR. unfold ablk, AIMG_HI, KLS in SB, FB.
        cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (INV3 : itb_inv SPA S F PB m3 m3 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
                           (fun _ => 0) of lf wf cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits)).
    { unfold itb_inv, itb_W, frm19. split; [exact MI3|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [exact FRA3|]. split; [exact CNT3|]. split; [exact OFFS3|]. split; [exact LENS3|]. split; [exact WORK3|]. split; [exact CDS3|].
      split; [exact SNXT3| exact SPB3]. }
    eapply evtF_cut.
    { eapply evtF_eq; [| eapply (it_body RNG FR fc gp tp SP SPA S F PB ATOP m3 ty lf wf cf lens_ofs codes nx bits CX C m3); exact INV3].
      unfold bst. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    cbv beta. intros ms4 HR. unfold body_post, ret_pre in HR.
    destruct HR as (m4 & x1 & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x25 & x28 & x29 & x30 & x31
                    & w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & cnt & of' & -> & INV4).
    destruct INV4 as (MI4 & MU4 & WM4 & FRA4 & CNT4 & OFFS4 & LENS4 & WORK4 & CDS4 & NEXT4 & BITS4).
    unfold itb_W in MU4. unfold frm19 in FRA4.
    assert (AH4 : AHEAP AI L RNG st (FB2 F :: LB) m4).
    { assert (CRS : forall A B, S <= A -> B <= S + 7176 -> aclient_range CI (FB2 F :: LB) (ATOP + 4096) A (B - A)).
      { intros A B X1 X2. eapply (acr_block AI _ (HB ps S 7176)); [right; exact HIN| cbn [ab_addr]; lia| cbn [ab_addr ab_size]; lia]. }
      eapply (AI_frame AI _ _ _ _ m3 m4 _ AH3 MU4 WM4).
      constructor; [cbn [fst snd]; apply acr_stack; lia|].
      constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 F 256); [left; reflexivity| lia| lia]|].
      constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 F 256); [left; reflexivity| lia| lia]|].
      constructor; [cbn [fst snd]; apply CRS; lia|]. constructor; [cbn [fst snd]; apply CRS; lia|].
      constructor; [cbn [fst snd]; apply CRS; lia|]. constructor; [cbn [fst snd]; apply CRS; lia| constructor]. }
    rw_split FTL3 1%nat FT1 FFLG3. clear FT1.
    xrw FRB3 MU4 WM4 FRB4. xstk STG3 MU4 WM4 STG4. xstk STL3 MU4 WM4 STL4.
    xrw FH3 MU4 WM4 FH4. xrw FFLG3 MU4 WM4 FFLG4.
    assert (FSH4 : rw_cells bsegs m4 (Z.shiftr F 3 + 2147450880) it_shcells).
    { eapply rw_cells_transport; [exact FSH3| exact MU4| exact WM4|]. unfold it_shcells, c1z. djs. }
    xrw SPRE3 MU4 WM4 SPRE4. xrw SMID3 MU4 WM4 SMID4.
    assert (SPO4 : rw_cells bsegs m4 PO [C4 obw]).
    { eapply rw_cells_transport; [exact SPO3| exact MU4| exact WM4|]. unfold bx in PBX. djs. }
    destruct (AI_fake_flag _ _ _ _ _ 2 F 256 AH4 ltac:(left; reflexivity)) as (FLC4 & _). rewrite <- EFLG in FLC4.
    clear FRB3 STG3 STL3 FH3 FFLG3 FSH3 SPRE3 SMID3 SPO3 SPB3 SNXT3 LENS3 WORK3 CDS3 TSH3 SHS3 SHC3 SHO3 CX INV3 FRA3 CNT3 OFFS3 FMID3.
    (* [comment removed for export] *)
    eapply evtF_mono.
    { eapply evtF_eq;
        [| eapply (it_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo SPA RNG LOS1 LOC SP16 SPT ESPA RSTK RI
                          F FLG F256 FB FTOP GB GTOP GF RF);
           [rewrite shadE; exact RSF| exact RG| exact STL4| exact STG4| exact MI4| exact FRA4| exact FRB4| exact FH4| exact FFLG4| exact FLC4| exact FSH4]].
      unfold bst. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    cbv beta.
    intros ms5 (mp & m5 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31
                & -> & MUp & WMp & MIp & MU5 & WM5 & MI5 & ST5 & FLC5).
    assert (AHp : AHEAP AI L RNG st (FB2 F :: LB) mp).
    { eapply (AI_frame AI _ _ _ _ m4 mp _ AH4 MUp WMp).
      constructor; [cbn [fst snd]; apply (acr_fake_sh AI _ 2 F 256 F 32); [left; reflexivity| exact F8| lia| lia| lia]|].
      constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 F 256); [left; reflexivity| lia| lia]| constructor]. }
    assert (EQ5 : m5 = write_to_mem mp (wa FLG) [Z_to_bv 8 0]).
    { apply mem_eq_single; [lia| lia| exact MU5|]. apply byte_of_c1; [exact FLC5| lia]. }
    assert (AH5 : AHEAP AI L RNG st LB m5).
    { rewrite EQ5, EFLG. apply (AI_fake_release L RNG st LB mp 2 F 256 AHp). }
    (* [comment removed for export] *)
    assert (OUT : forall a, aclient_addr CI LB SP a -> ~ in_ranges WR a ->
                    ~ (lo <= a < SP) /\ ~ (F <= a < F + 256) /\ ~ (Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + 32) /\ a <> FLG
                    /\ ~ (S + 136 <= a < S + 144) /\ ~ (S + 160 <= a < S + 168) /\ ~ (S + 808 <= a < S + 7160)).
    { intros a HC HN.
      destruct (it_client_outside AI L RNG st LB m2 F FLG lo SP a AH2 LBH FB F8 GB GBL GCI LOC ltac:(lia) HC) as (O1 & O2 & O3 & O4).
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
      split; [intros X; apply HN; exists (S + 136, S + 144); split; [left; reflexivity| exact X]|].
      split; [intros X; apply HN; exists (S + 160, S + 168); split; [right; left; reflexivity| exact X]|].
      intros X; apply HN; exists (S + 808, S + 7160); split; [right; right; left; reflexivity| exact X]. }
    assert (AG : client_agree AI LB SP WR m m5).
    { eapply client_agree_trans; [| eapply client_agree_trans; [| eapply client_agree_trans; [| eapply client_agree_trans; [| eapply client_agree_trans]]]].
      - eapply (client_agree_munch AI LB _ _ _ m m1 MU1 WM1). intros a Ha HC HN. destruct (OUT a HC HN) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        cbn [outside]. repeat split; try exact I; lia.
      - eapply (client_agree_pres AI LB LB SP SPA); [exact PRES| lia| auto].
      - eapply (client_agree_munch AI LB _ _ _ m2 m3 MU3 WM3). intros a Ha HC HN. destruct (OUT a HC HN) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        cbn [outside]. repeat split; try exact I; lia.
      - eapply (client_agree_munch AI LB _ _ _ m3 m4 MU4 WM4). intros a Ha HC HN. destruct (OUT a HC HN) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        cbn [outside]. repeat split; try exact I; lia.
      - eapply (client_agree_munch AI LB _ _ _ m4 mp MUp WMp). intros a Ha HC HN. destruct (OUT a HC HN) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        cbn [outside]. repeat split; try exact I; lia.
      - eapply (client_agree_munch AI LB _ _ _ mp m5 MU5 WM5). intros a Ha HC HN. destruct (OUT a HC HN) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        cbn [outside]. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    xrw SPRE4 MUp WMp SPREp. xrw BITS4 MUp WMp BITSp. xrw SPO4 MUp WMp SPOp. xrw SMID4 MUp WMp SMIDp. xrw NEXT4 MUp WMp NEXTp.
    xf16 LENS4 MUp WMp LENSp. xf16 WORK4 MUp WMp WORKp. xf32 CDS4 MUp WMp CDSp.
    unfold bx in GS.
    xrw SPREp MU5 WM5 SPRE5. xrw BITSp MU5 WM5 BITS5. xrw SPOp MU5 WM5 SPO5. xrw SMIDp MU5 WM5 SMID5. xrw NEXTp MU5 WM5 NEXT5.
    xf16 LENSp MU5 WM5 LENS5. xf16 WORKp MU5 WM5 WORK5. xf32 CDSp MU5 WM5 CDS5.
    unfold it_core_post. exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m5.
    split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact AH5|]. split; [exact AG|].
    split; [exact SPRE5|]. split; [exact BITS5|]. split; [exact SPO5|]. split; [exact SMID5|]. split; [exact NEXT5|].
    split; [exact LENS5|]. split; [exact WORK5| exact CDS5].
  Qed.
End Core.

(* [comment removed for export] *)
Theorem inflate_table_proofA : inflate_table_stmtA AI rng_fs.
Proof.
  unfold inflate_table_stmtA. intros until have.
  intros AH AM1 LBH HIN TABC TSH UIMG SSC EBITS LENS WORK CDS C A0 A1 A2 A3 A4 A5 ST LOC LOS SP16 SPT MI TP RSTK RI RISH RFS.
  subst a0 a1 a2 a3 a4 a5.
  unfold istate_cells in SSC.
  rw_split SSC 26%nat SPRE R1. rw_split R1 1%nat SLB R2. rw_split R2 1%nat SDB R3. rw_split R3 4%nat SMID SNXT.   (* [U14B] A2: 26 cells to lenbits at 1.4 *)
  pose proof (it_ret_cases ty lf lens_ofs codes nx bits cf wf) as RC. cbv zeta in RC.
  destruct isd.
  - subst distbits.
    lazymatch type of SPRE with rw_cells _ _ _ ?pre => lazymatch type of SMID with rw_cells _ _ _ ?mid =>
      pose proof (it_top_core L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB ps S lo ty lf cf wf lens_ofs codes nx bits
                    (S + 140) (S + 136) pre mid lenbits AM1 LBH HIN TABC eq_refl eq_refl (or_intror (conj eq_refl eq_refl)) C LOC LOS SP16 SPT TP RSTK RI RISH RFS
                    t0 t1 t2 a6 a7 t3 t4 t5 t6 m AH TSH UIMG SPRE SDB SLB SMID SNXT LENS WORK CDS ST MI) as CORE end end.
    eapply evtF_mono; [exact CORE|]. cbv beta. unfold it_core_post, itable_post. cbv zeta.
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AH' & AG
                & SPRE' & SPB' & SPO' & SMID' & SNXT' & LENS' & WORK' & CDS').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AH'|]. split; [exact AG|].
    split; [| split; [exact LENS'| split; [exact WORK'| split; [exact CDS'| exact RC]]]].
    rw_join SPRE' SPO' J1. rw_join J1 SPB' J2. rw_join J2 SMID' J3. rw_join J3 SNXT' J4. exact J4.
  - subst lenbits.
    lazymatch type of SPRE with rw_cells _ _ _ ?pre => lazymatch type of SMID with rw_cells _ _ _ ?mid =>
      pose proof (it_top_core L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB ps S lo ty lf cf wf lens_ofs codes nx bits
                    (S + 136) (S + 140) pre mid distbits AM1 LBH HIN TABC eq_refl eq_refl (or_introl (conj eq_refl eq_refl)) C LOC LOS SP16 SPT TP RSTK RI RISH RFS
                    t0 t1 t2 a6 a7 t3 t4 t5 t6 m AH TSH UIMG SPRE SLB SDB SMID SNXT LENS WORK CDS ST MI) as CORE end end.
    eapply evtF_mono; [exact CORE|]. cbv beta. unfold it_core_post, itable_post. cbv zeta.
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AH' & AG
                & SPRE' & SPB' & SPO' & SMID' & SNXT' & LENS' & WORK' & CDS').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AH'|]. split; [exact AG|].
    split; [| split; [exact LENS'| split; [exact WORK'| split; [exact CDS'| exact RC]]]].
    rw_join SPRE' SPB' J1. rw_join J1 SPO' J2. rw_join J2 SMID' J3. rw_join J3 SNXT' J4. exact J4.
Qed.
End Top.
End CANSEC1.
