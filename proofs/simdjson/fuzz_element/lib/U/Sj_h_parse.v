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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs Sj_stage1 Sj_stage2_iface.
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

Lemma region_in_range : forall s LB m X n, RHEAP s LB m -> region_in LB X n -> 0 <= n ->
  0 < X /\ X + n <= alloc_ceiling /\ (X + n <= 0x10000 \/ 0x111000 <= X).
Proof.
  intros s LB m X n H (b & Hb & H1 & H2) Hn. pose proof (LH_block_range _ _ _ _ H Hb) as (B0 & _ & B2 & B3 & B4).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in B3. lia.
Qed.
Lemma region_in_wok : forall LB X n, region_in LB X n -> rclient_write_ok LB (X, X + n).
Proof. intros LB X n (b & Hb & H1 & H2). right; right. exists b. cbn [fst snd]. auto. Qed.
Lemma region_in_block : forall LB X n a, region_in LB X n -> X <= a < X + n -> in_block LB a.
Proof. intros LB X n a (b & Hb & H1 & H2) Ha. exists b. split; [exact Hb| lia]. Qed.

Lemma pairwise_disj_nth : forall l i j a b, pairwise_disj l -> nth_error l i = Some a -> nth_error l j = Some b -> (i < j)%nat -> ivl_disj a b.
Proof.
  induction l as [|x r IH]; intros i j a b H Hi Hj Hlt; [destruct i; discriminate|].
  destruct H as [HF HP]. destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. rewrite Forall_forall in HF. apply HF. eapply nth_error_In. exact Hj.
  - cbn [nth_error] in Hi. eapply IH; eauto. lia.
Qed.

Definition parse_model (bs : list Z) : M PState unit :=
  match SjAlloc.root_copy bs (stage1_code bs) (stage1_idx0 bs) with
  | Some c => mbind (newnt lops c) (fun r => del lops r)
  | None => mret tt
  end.

Definition parse_X (THIS IDX TAPE SBUF OC IA ncap tcap scap : Z) : list (Z * Z) :=
  [(THIS, THIS + 96); (IDX, IDX + 4 * ncap); (TAPE, TAPE + 8 * tcap); (SBUF, SBUF + scap); (OC, OC + 8192); (IA, IA + 1024)].
Definition parse_R (LB : list block) (q : Z) (m : mem) (THIS IDX TAPE SBUF OC IA BUF cap len ncap tcap scap : Z) (p12 p28 p50 : list byte)
    : word -> PState -> mem -> Prop :=
  fun a0 s' m' => bv_unsigned a0 < 64 /\ RHEAP s' LB m' /\ lx_pres LB q (parse_X THIS IDX TAPE SBUF OC IA ncap tcap scap) m m'
    /\ (exists nsi' nxt' docv',
        rw_cells usegs m' THIS (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi' p12 (Z_to_bv 64 IDX) nxt' p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                             (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 BUF) (Z_to_bv 64 len) docv'))
    /\ s2_okres TAPE SBUF tcap scap a0 m'.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.

  Lemma parse_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs : list Z) (ws0 : list word) (cap tcap scap : Z)
      (nsi nxt bufv lenv docv dcap : word) (p12 p28 p50 : list byte),
    bytes_ok bs -> blen bs <= 1048512 ->
    blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 -> blen bs + 3 <= Z.of_nat (length ws0) ->
    RHEAP s LB m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (32 + SJ_S2_STACK) -> q mod 16 = 0 ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc -> 0 <= q < 2^64 ->
    rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    region_in LB THIS 96 -> region_in LB IDX (4 * Z.of_nat (length ws0)) -> region_in LB BUF (blen bs + 64) ->
    region_in LB TAPE (8 * tcap) -> region_in LB SBUF scap -> region_in LB OC 8192 -> region_in LB IA 1024 ->
    pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length ws0)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
    q <= DOC -> DOC + 24 <= B -> IDX mod 4 = 0 -> THIS mod 8 = 0 -> DOC mod 8 = 0 -> TAPE mod 8 = 0 -> OC mod 8 = 0 ->
    rw_cells usegs m THIS (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                        (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 dcap] ->
    u32arr usegs m IDX ws0 ->
    bytes_at usegs m BUF (padded_bytes bs) ->
    wr_at usegs m TAPE (8 * tcap) -> wr_at usegs m SBUF scap ->
    (exists ocs, u32arr usegs m OC ocs /\ length ocs = 2048%nat) ->
    (exists ias, u8arr usegs m IA ias /\ length ias = 1024%nat) ->
    (forall s' ms',
        hpostF ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s lo B
               (parse_R LB q m THIS IDX TAPE SBUF OC IA BUF cap (blen bs) (Z.of_nat (length ws0)) tcap scap p12 p28 p50) s' ms' ->
        implM usegs k s' Q ms') ->
    implM usegs (mbind (parse_model bs) (fun _ => k)) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 BUF) (Z_to_bv 64 (blen bs)) (Z_to_bv 64 DOC) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DPI_PARSE) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until p50.
    intros BOK LEN TC1 TC2 SC1 SC2 ICAP HEAP AUX QB B63 ST CEIL GLO LO Q16 ERR MI FRM Hq GOT RTHIS RIDX RBUF RTAPE RSBUF ROC RIA PD QD DB ALIDX ALTHIS ALDOC ALTAPE ALOC
           THISC DOCC ARR BUFB TAPEW SBUFW OCA IAA HK.
    unfold SJ_DPI_PARSE, SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (BL0 : 0 <= blen bs) by (unfold blen; lia).

    pose proof (region_in_range _ _ _ _ _ HEAP RTHIS ltac:(lia)) as (TH0 & THC & THS).
    pose proof (region_in_range _ _ _ _ _ HEAP RIDX ltac:(lia)) as (IX0 & IXC & IXS).
    pose proof (region_in_range _ _ _ _ _ HEAP RBUF ltac:(lia)) as (BF0 & BFC & _).
    pose proof (region_in_range _ _ _ _ _ HEAP ROC ltac:(lia)) as (OC0 & OCC & _).
    pose proof (region_in_range _ _ _ _ _ HEAP RIA ltac:(lia)) as (IA0 & IAC & _).
    assert (STAT : forall a, 0xd6000 <= a < 0x111000 -> ~ (THIS <= a < THIS + 96) /\ ~ (IDX <= a < IDX + 4 * Z.of_nat (length ws0)))
      by (intros a Ha; clear - Ha THS IXS; lia).
    pose proof (padded_bytes_blen bs) as PBL.
    destruct OCA as (ocs & OCA & LOCS). destruct IAA as (ias & IAA & LIAS).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) a -> outside [(q - 32, q)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 32, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    unfold impl_cells16 in THISC. unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT.
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
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo THIS BUF IDX bs (length ws0) (Z_to_bv 64 SJ_DPI_VPTR) p12 MID DJ8 m1).
    assert (OK : env_ok_u E).
    { constructor; [| unfold E; cbn [e_BUF]; lia| unfold E; cbn [e_IDX]; lia| unfold E; cbn [e_IDX]; exact ALIDX]. pose proof (pairwise_disj_nth _ 0 1 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_IX.
      pose proof (pairwise_disj_nth _ 0 2 _ _ PD eq_refl eq_refl ltac:(lia)) as D_TH_BF.
      pose proof (pairwise_disj_nth _ 1 2 _ _ PD eq_refl eq_refl ltac:(lia)) as D_IX_BF.
      unfold ivl_disj in D_TH_IX, D_TH_BF, D_IX_BF. cbn [fst snd] in D_TH_IX, D_TH_BF, D_IX_BF.
      unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; unfold S1_LEN_MAX, U1_GTOP, U1_STACK; (rewrite ?unsigned_lit by lia); try assumption.
      all: clear - LEN GLO LO THC IXC BFC CEIL TH0 IX0 BF0 ICAP Hq D_TH_IX D_TH_BF D_IX_BF; lia. }
    destruct (stage1 bs) as [code idxs] eqn:ES.
    pose proof (stage1_code_range bs) as CR. rewrite ES in CR. cbn [fst] in CR.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (stage1_spec E OK)]; [cbv delta [mkR E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_THIS e_BUF e_bs U1_ENTRY]; reflexivity | ..].
      - cbn [e_m0 E]. assumption.
      - cbn [e_m0 e_lo e_sp E]. rewrite unsigned_lit by lia. exact ST.
      - cbn [e_m0 e_THIS E]. unfold parser_cells. cbn [e_vptr e_p12 e_IDX e_mid e_docj E]. exact TH2.
      - cbn [e_m0 e_IDX E]. exact ARR.
      - reflexivity.
      - cbn [e_m0 e_BUF e_bs E]. exact BUFB. }
    rewrite ES. cbn [fst snd].
    intros ms' PO. unfold s1_post_g in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & ws' & nxt' & -> & MU1 & WM1 & MI2 & ST2
                    & TH3 & NXT & ARR2 & LWS2 & FIRSTN & BUFB2).
    unfold s1_W_g, parser_cells in *. cbn [E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_lo e_THIS e_BUF e_IDX e_bs e_cap
                                           e_vptr e_p12 e_mid e_docj] in *.
    rewrite (unsigned_lit (q + -32)) in MU1, ST2 by lia.

    subst MID DJ8.
    pose proof (rw_cells_unmerge m2 THIS ([C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (MallocRep.wz (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] ++ [CB 44 (cells_bytes mid1); C8 (MallocRep.wz BUF); C8 (MallocRep.wz (blen bs))])
                  [C8 docv] [] TH3 ltac:(cbn; auto)) as TH4.
    cbn [app] in TH4.
    pose proof (rw_cells_unmerge m2 THIS [C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (MallocRep.wz (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] mid1
                  [C8 (MallocRep.wz BUF); C8 (MallocRep.wz (blen bs)); C8 docv] TH4 WF1) as TH5.
    subst mid1. cbn [app] in TH5. clear TH3 TH4 TH2 THISC ARR BUFB WF1 OK.
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
    apply (rw_cells_agree _ _ _ _ _ AG1) in DOCC; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha THC IXC CEIL LO QD; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in GOT; [| intros a Ha; cbn in Ha; cbn [outside]; pose proof (STAT a ltac:(lia)); clear - Ha H CEIL LO GLO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; pose proof (STAT a ltac:(lia)); clear - Ha H CEIL LO GLO; lia].
    apply (wr_at_transport usegs m1 m2 _ _) in TAPEW; [| exact WM1]. apply (wr_at_transport usegs m1 m2 _ _) in SBUFW; [| exact WM1].
    apply (u32arr_agree _ _ _ _ _ AG1) in OCA.
    2:{ pose proof (pairwise_disj_nth _ 0 5 _ _ PD eq_refl eq_refl ltac:(lia)) as D1. pose proof (pairwise_disj_nth _ 1 5 _ _ PD eq_refl eq_refl ltac:(lia)) as D2.
        unfold ivl_disj in D1, D2. cbn [fst snd] in D1, D2. intros a Ha; rewrite LOCS in Ha; cbn [outside]; clear - Ha D1 D2 OCC CEIL LO; lia. }
    apply (u8arr_agree _ _ _ _ _ AG1) in IAA.
    2:{ pose proof (pairwise_disj_nth _ 0 6 _ _ PD eq_refl eq_refl ltac:(lia)) as D1. pose proof (pairwise_disj_nth _ 1 6 _ _ PD eq_refl eq_refl ltac:(lia)) as D2.
        unfold ivl_disj in D1, D2. cbn [fst snd] in D1, D2. intros a Ha; rewrite LIAS in Ha; cbn [outside]; clear - Ha D1 D2 IAC CEIL LO; lia. }
    clear AG1 MU1 WM1.
    replace (ret_pc (Z_to_bv 64 372644)) with (Z_to_bv 64 372644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(q - 32, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    step.
    destruct (Z.eqb_spec code 0) as [C0|CN].
    -
      subst code. unfold MallocRep.wz. if_true.
      do 6 step. release_frame FR ST2 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      ihere. to_implM.
      unfold parse_model, stage1_code, stage1_idx0. rewrite ES. cbn [fst snd].
      assert (SO1 : S1OUT bs idxs).
      { exact (stage1_S1OUT bs idxs ES). }
      assert (HEAP3 : RHEAP s LB m3).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX3 : rauxv_ok m3 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES3 : lx_pres LB q (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) m m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
      clear MU WM HEAP2 AUX2 PRES2.
      eapply implM_bind.
      { eapply (S2 ra (Z_to_bv 64 q)) with (bs := bs) (idxs := idxs) (iws := ws') (B := B) (lo := lo) (cap := cap) (tcap := tcap) (scap := scap)
                   (TAPE := TAPE) (SBUF := SBUF) (OC := OC) (IA := IA) (BUF := BUF) (IDX := IDX) (THIS := THIS) (DOC := DOC);
          rewrite ?(unsigned_lit q) by lia; rewrite ?LWS2.
        all: try eassumption.
        - unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK. lia.
        - exists ocs. split; assumption.
        - exists ias. split; assumption. }
      cbv beta. intros [] s3' ms3 PO. unfold stage2t_post in PO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F' & fc' & m4 & errv4 & nxt4
                      & -> & FRM4 & HEAP4 & AUX4 & ST4 & ERR4 & MI4 & FA4 & SO4 & PRES4 & THIS4 & OKRES4).
      assert (A064 : bv_unsigned y10 < 64).
      { destruct OKRES4 as [K|[E0 _]]; [lia| rewrite E0; unfold MallocRep.wz; rewrite unsigned_lit by lia; lia]. }
      rewrite (unsigned_lit q) in ST4, PRES4 by lia.
      apply HK. unfold hpostF. do 15 eexists. exists F', fc', m4.
      split; [reflexivity|]. split; [exact FRM4|]. split; [exact MI4|]. split; [exact ST4|]. split; [exists errv4; exact ERR4|]. split; [exact AUX4|].
      split; [exact FA4|]. split; [exact SO4|].
      unfold parse_R. split; [exact A064|]. split; [exact HEAP4|]. split.
      + eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_weaken; [exact PRES4| lia| auto|].
        intros a Ha. unfold s2_X in Ha. unfold parse_X. cbn [rin_ivs fst snd] in Ha |- *. clear - Ha. tauto.
      + split; [| exact OKRES4].
        exists (MallocRep.wz (Z.of_nat (length idxs))), nxt4, (MallocRep.wz DOC). unfold s2_impl_cells, impl_cells16 in *. exact THIS4.
    -
      if_cases K; zify_cond K; [exfalso; unfold MallocRep.wz in K; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
      do 4 step. release_frame FR ST2 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      ihere. to_implM.
      unfold parse_model, stage1_code, stage1_idx0. rewrite ES. cbn [fst snd]. unfold root_copy.
      replace (code =? 0) with false by (symmetry; apply Z.eqb_neq; exact CN). cbn [andb].
      apply implM_ret_bind.
      apply HK. unfold hpostF. do 15 eexists. exists F, fc, m3.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FRM|]. split; [assumption|]. split; [exact ST2|].
      split; [exists errv; rewrite ELX; assumption|].
      split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [reflexivity|]. split; [reflexivity|].
      unfold parse_R. split; [unfold MallocRep.wz; rewrite unsigned_lit by lia; lia|]. split.
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
      split; [exists (MallocRep.wz (Z.of_nat (length idxs))), nxt', docv; unfold impl_cells16; assumption|].
      left. unfold MallocRep.wz. rewrite unsigned_lit by lia. lia.
  Qed.
End Proofs.
End WithCeiling0.
