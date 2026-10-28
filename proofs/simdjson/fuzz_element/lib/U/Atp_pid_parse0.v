(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs Sj_stage1 Sj_stage2_iface Sj_h_parse Atp_pid_s1z.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition parse0_R (LB : list block) (q : Z) (m : mem) (THIS IDX TAPE SBUF OC IA BUF cap ncap tcap scap : Z) (p12 p28 p50 : list byte)
    : word -> PState -> mem -> Prop :=
  fun r s' m' => RHEAP s' LB m' /\ lx_pres LB q (parse_X THIS IDX TAPE SBUF OC IA ncap tcap scap) m m'
    /\ (exists nsi' nxt' docv',
        rw_cells usegs m' THIS (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi' p12 (Z_to_bv 64 IDX) nxt' p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                             (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 BUF) (Z_to_bv 64 0) docv'))
    /\ r = Z_to_bv 64 13.

  Lemma parse0_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (ws0 : list word) (cap tcap scap : Z)
      (nsi nxt bufv lenv docv : word) (p12 p28 p50 : list byte),
    3 <= Z.of_nat (length ws0) ->
    RHEAP s LB m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (32 + SJ_S2_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    region_in LB THIS 96 -> region_in LB IDX (4 * Z.of_nat (length ws0)) ->
    ivl_disj (THIS, 96) (IDX, 4 * Z.of_nat (length ws0)) ->
    q <= DOC -> DOC + 24 <= B -> IDX mod 4 = 0 ->
    rw_cells usegs m THIS (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                        (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    u32arr usegs m IDX ws0 ->
    (forall s' ms',
        hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B
              (parse0_R LB q m THIS IDX TAPE SBUF OC IA BUF cap (Z.of_nat (length ws0)) tcap scap p12 p28 p50) s' ms' ->
        implM usegs k s' Q ms') ->
    implM usegs k s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 BUF) (Z_to_bv 64 0) (Z_to_bv 64 DOC) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DPI_PARSE) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until p50.
    intros ICAP HEAP AUX QB B63 ST CEIL GLO LO ERR MI Hq RTHIS RIDX DTI QD DB ALIDX THISC ARR HK.
    unfold SJ_DPI_PARSE, SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (region_in_range _ _ _ _ _ HEAP RTHIS ltac:(lia)) as (TH0 & THC & THS).
    pose proof (region_in_range _ _ _ _ _ HEAP RIDX ltac:(lia)) as (IX0 & IXC & IXS).
    assert (STAT : forall a, 0xd6000 <= a < 0x111000 -> ~ (THIS <= a < THIS + 96) /\ ~ (IDX <= a < IDX + 4 * Z.of_nat (length ws0)))
      by (intros a Ha; clear - Ha THS IXS; lia).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) a -> outside [(q - 32, q)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 32, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    unfold impl_cells16 in THISC.
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 7 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB q (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) m m1)
      by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    clear MU WM.

    set (mid1 := [CB 4 p28; C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 p50; C8 (Z_to_bv 64 OC); C8 (Z_to_bv 64 IA)]).
    assert (WF1 : cells_wf mid1).
    { destruct THISC as [[Hwf _] _]. cbn [cells_wf] in Hwf. subst mid1. cbn [cells_wf].
      destruct Hwf as (_ & _ & _ & _ & _ & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & _). repeat split; assumption. }
    pose proof (rw_cells_merge usegs m1 THIS [C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 nsi; CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt] mid1 [C8 bufv; C8 lenv; C8 docv] THISC) as TH1.
    pose proof (rw_cells_merge usegs m1 THIS ([C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 nsi; CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt] ++ [CB (cells_size mid1) (cells_bytes mid1); C8 bufv; C8 lenv])
                  [C8 docv] [] TH1) as TH2.
    clear TH1. cbn [app] in TH2. change (cells_size mid1) with 44%nat in TH2. change (cells_size [C8 docv]) with 8%nat in TH2.
    set (MID := cells_bytes mid1) in TH2. set (DJ8 := cells_bytes [C8 docv]) in TH2.
    set (E := mkS1Env (Z_to_bv 64 372644) (Z_to_bv 64 (q + -32)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 DOC) (Z_to_bv 64 THIS)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo THIS BUF IDX [] (length ws0) (Z_to_bv 64 SJ_DPI_VPTR) p12 MID DJ8 m1).
    assert (OK : env_okzu E).
    { unfold ivl_disj in DTI. cbn [fst snd] in DTI.
      unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_cap]; unfold U1_GTOP, U1_STACK; (rewrite ?unsigned_lit by lia); try reflexivity; try exact ALIDX.
      all: clear - GLO LO THC IXC CEIL TH0 IX0 ICAP Hq DTI; lia. }
    eapply evt_cut.
    { eapply evt_eq; [| eapply (s1z_spec E OK)]; [cbv delta [mkR E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_THIS e_BUF e_bs U1_ENTRY blen zlength length Z.of_nat]; reflexivity | ..].
      - cbn [e_m0 E]. assumption.
      - cbn [e_m0 e_lo e_sp E]. rewrite unsigned_lit by lia. exact ST.
      - cbn [e_m0 e_THIS E]. unfold parser_cells. cbn [e_vptr e_p12 e_IDX e_mid e_docj E]. exact TH2.
      - cbn [e_m0 e_IDX E]. exact ARR.
      - reflexivity. }
    intros ms' PO. unfold s1z_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & ws' & nxt' & -> & MU1 & WM1 & MI2 & ST2
                    & TH3 & NXT & ARR2 & LWS2 & FIRSTN).
    unfold s1_W_g, parser_cells in *. cbn [E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_lo e_THIS e_BUF e_IDX e_bs e_cap
                                           e_vptr e_p12 e_mid e_docj blen zlength length Z.of_nat] in *.
    rewrite (unsigned_lit (q + -32)) in MU1, ST2 by lia.

    subst MID DJ8.
    pose proof (rw_cells_unmerge m2 THIS ([C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (Sj_stage1_kit.wz 0); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] ++ [CB 44 (cells_bytes mid1); C8 (Sj_stage1_kit.wz BUF); C8 (Sj_stage1_kit.wz 0)])
                  [C8 docv] [] TH3 ltac:(cbn; auto)) as TH4.
    cbn [app] in TH4.
    pose proof (rw_cells_unmerge m2 THIS [C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (Sj_stage1_kit.wz 0); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] mid1
                  [C8 (Sj_stage1_kit.wz BUF); C8 (Sj_stage1_kit.wz 0); C8 docv] TH4 WF1) as TH5.
    subst mid1. cbn [app] in TH5. clear TH3 TH4 TH2 THISC ARR WF1 OK.
    assert (HEAP2 : RHEAP s LB m2).
    { eapply LH_frame; [exact HEAP1| exact MU1| exact WM1|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply region_in_wok; exact RTHIS|].
      constructor; [apply region_in_wok; exact RIDX| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU1| exact WM1|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres LB q (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha [HX HC]. unfold parse_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [lia| split; [lia| exact I]]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    clear HEAP1 AUX1 PRES1.
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    apply (rw_cells_agree _ _ _ _ _ AG1) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha THC IXC CEIL LO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; pose proof (STAT a ltac:(lia)); clear - Ha H CEIL LO GLO; lia].
    clear AG1 MU1 WM1.
    replace (ret_pc (Z_to_bv 64 372644)) with (Z_to_bv 64 372644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(q - 32, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    unfold Sj_stage1_kit.wz. step. if_false.
    do 4 step. release_frame FR ST2 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    ihere. to_implM.
    apply HK. unfold hpost. do 15 eexists. exists m3.
    split; [cbv delta [mkR]; reflexivity|]. split; [assumption|]. split; [exact ST2|].
    split; [exists errv; rewrite ELX; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [reflexivity|]. split; [reflexivity|].
    unfold parse0_R. split.
    { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    split; [exists (Z_to_bv 64 0), nxt', docv; unfold impl_cells16; assumption|].
    reflexivity.
  Qed.
End WithCeiling0.
