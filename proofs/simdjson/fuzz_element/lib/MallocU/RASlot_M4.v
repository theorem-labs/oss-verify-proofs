(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M4P ASlot_M4 F_malloc_bigw F_malloc_big.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMallocKit_A3 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W11 RASlot_W14 RASlot_W15 RASlot_W16 RASlot_W17 RASlot_W18 RASlot_W19 RASlot_M0 RASlot_M2 RASlot_M3 RASlot_M5D RASlot_M5F RASlot_M5S RF_malloc_big.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rhmm_ok : rHMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CLO'; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  pose proof (mf_ctx _ _ MF2) as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  destruct (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) as (CR & NDM & NDR & NDC).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(pose proof (Z.mul_nonneg_nonneg size c ltac:(lia) ltac:(lia)); lia)).
    assert (size * c <= 2^18 * 32) by (apply Z.mul_le_mono_nonneg; lia). destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.

  riprefixT.
  eapply evt_cut. { eapply (rmm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. intros ms' (u0 & u1' & wa3 & wa6 & wa7 & m4 & -> & -> & MU4 & WM4 & MI4 & MR4).
  fold nos stS in MR4 |- *.

  destruct (stS_shape sc st2) as (fS & ES & HS). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold rmmc_post. intros ms' (v0 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & ->).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].

  assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ERR4 : rw_cells usegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold rseqW, RCTX. cbn. lia. }
  assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold RCTX in *. lia. }
  assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. unfold rseqW, RAUXV_CELL, RCTX, RLIBC. constructor; [cbn; lia| constructor]. }
  pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).

  eapply evt_cut. { eapply rmm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.

  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).

  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). pose proof WF as (RS0 & WR0 & DJ0 & _).
  destruct ans as [e|xa].
  -
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He).
    cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0xc36cc)) with (Z_to_bv 64 0xc36cc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }

    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    riprefixT.
    eapply evt_cut. { eapply rmm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. intros ms' (s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
    assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
    { eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk usegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells usegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.

    set (stF := as_fm_st stS mm) in *.
    destruct (fm_proj stS mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
    { apply (rfailW_shape stS mm _ MSLS). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply rpres_except_trans.
      - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
      - eapply rpres_except_trans.
        + eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
            exists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold ras_post2.
    do 14 eexists. exists m7, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
        destruct (rregion_facts st2 m3 rid r MR3 Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            destruct (rmeta_chunk_facts st2 m3 q MR3 MSq2) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold RCTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold rseqW, RCTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  -
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & AOK).
    cbn [mmap_val]. unfold mm_after. fold stS.
    destruct (mmap_answer_ok (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    destruct (mmap_answer_ok_addr (live_ranges stS) nd xa ltac:(lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rmrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]. }

    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; pose proof (HS cc) as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold F_mm_syscalls.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in XC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep stN mz).
    { rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). pose proof WF6 as (RS6 & WR6 & DJ6 & _).
    assert (XI : xa + nd <= 0x10000 \/ 0x111000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv usegs mz).
    { unfold mz. apply (mem_inv_zeros usegs m6 xa nd); unfold UTOP; try lia; [exact MI6|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono usegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells usegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk usegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells usegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }

    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      destruct MSLS as (ar & arr & kk & Ha & Hk & ->). unfold aadd. cbn [fst]. intros E.
      destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0xc36cc)) with (Z_to_bv 64 0xc36cc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'.
      eapply (rmm_ret_ok_walk (CE__:=CE__) stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 ltac:(unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia) MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. intros ms' (xa3 & xa4 & m8 & -> & MU8 & WM8 & MI8 & MR8 & CTR8).
    set (stT := mm_st4 stN nd mm) in *.

    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. intros ms' (s0x & a1x & a2x & a3x & a4x & m9 & -> & MU9 & WM9 & MI9 & MR9 & TK9).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).

    assert (FR9 : rw_cells usegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in GC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold RCTX. cbn. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in GC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia. }
    assert (ST9 : stk usegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in GC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold RCTX; cbn; unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in GC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. intros ms' (a1y & a2y & -> & ST10). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.

    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(pose proof (Z.mul_nonneg_nonneg size c ltac:(lia) ltac:(lia)); lia)) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    destruct (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) as (SO & STR & S16 & SND).
    fold stF in SO, STR, S16, SND.
    pose proof (sm_proj stT sc c ai mm rid) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).

    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. destruct (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) as (r1 & H1 & K1 & B1 & L1). rewrite <- REG1 in H1.
      destruct (amr_regions _ _ _ REL q r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
    { intros a Ha. eapply (fresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }

    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      destruct (WR6 _ _ HqS) as (R0 & _ & _ & RC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
      destruct (rregion_facts st2 m3 q rq MR3 Hq) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      destruct (rmeta_chunk_facts st2 m3 mm MR3 MSL) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.

      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rtailW. rewrite GT, PT. cbn. unfold RCTX. clear - Ho R0 RC RI2 GRq DJq SC SND S16; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC; lia). rewrite GCN. cbn. unfold RCTX. clear - Ho R0 RI2 GRq; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC; lia | clear - Ho R0 DJq; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC; lia). cbn. clear - Ho R0 RC CLO' LO ASG; lia. }
      apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rseqW, RCTX. cbn. clear - Ho R0 RI2; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04| exact HFP2]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply rpres_except_trans.
      { eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
          exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold RCTX in *. lia. }
      eapply rpres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold RCTX in *. lia.
      - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
        exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold RCTX in *. lia. }
    assert (ERR9 : rw_cells usegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold RCTX. lia.
      - unfold rtailW. rewrite GT, PT, EA. cbn. unfold RCTX. lia. }
    unfold ras_post2.
    do 14 eexists. exists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
    right. split; [lia|]. exists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.
End WithCeiling0.
