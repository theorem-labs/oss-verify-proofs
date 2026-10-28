(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_alloc Sj_h_create Sj_h_active Sj_h_bom Sj_h_pid_front Pj_pid Sj_h_pdtor.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_iface Sj_h_parse Printf_mlib.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition PJ_LFTOI_GATE : Z := 0x3cdb4.
Definition PJ_OKARM : Z := 0x3cdc4.
Definition PJ_JOIN : Z := 0x3ce64.
Definition PJ_OKARM_STACK : Z := 65536.

Lemma mod16_off8 : forall q k, q mod 16 = 0 -> (q + 8 * k) mod 8 = 0.
Proof.
  intros q k H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. destruct H as [c Hc]. exists (2 * c + k). lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rw_cells_join : forall m A cs1 A' cs2, rw_cells usegs m A cs1 -> rw_cells usegs m A' cs2 -> A' = A + Z.of_nat (cells_size cs1) ->
  rw_cells usegs m A (cs1 ++ cs2).
Proof. intros m A cs1 A' cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_split_at : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply rw_cells_app in H. exact H. Qed.

Definition pj_okarm_X (q0 : Z) : list (Z * Z) := [LXW_SJ; (q0 - 496, q0 - 208); (q0 - 128, q0 - 40)].

Definition pj_okarm_post (q0 : Z) (gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (s : PState) (LBall : list block) (lo B : Z) (m : mem)
    (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 F' fc' m' (errv' : word),
    ms' = MS (mkR x1 (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 PJ_JOIN) fc' None m' (seg_rom usegs)
    /\ frm0 fc' /\ mem_inv usegs m' /\ stk usegs m' lo (q0 + -496) /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' LBall m' /\ lx_pres LBall (q0 + -496) (pj_okarm_X q0) m m'
    /\ sj_statics m' true
    /\ (exists bs, rw_cells usegs m' (q0 + -496) [CB 288 bs]) /\ (exists bs, rw_cells usegs m' (q0 + -128) [CB 88 bs]).

Definition pj_okarm_stmt : Prop :=
  forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
         (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall : list block) (q0 lo B : Z) (errv canary : word)
         (len TAPE SBUF cap : Z) (ptp psb : bptr) (j20 jgap jsb : list byte),
  RHEAP s LBall m -> In (ptp, TAPE, 8 * roundup64 (cap + 3)) LBall -> In (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) LBall ->
  rauxv_ok m B -> q0 <= B -> B < 2^62 ->
  stk usegs m lo (q0 + -496) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q0 - 496 - PJ_OKARM_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc -> q0 mod 16 = 0 -> 496 <= q0 ->
  lx_statics m -> sj_statics m true -> ssp_cells m canary ->
  0 <= len <= 1048512 -> cap = Z.max len 32 ->
  rw_cells usegs m (q0 + -496) [C8 (Z_to_bv 64 (q0 + -184)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20] ->
  rw_cells usegs m (q0 + -472) [CB 264 jgap] ->
  rw_cells usegs m (q0 + -128) [CB 88 jsb] ->
  rw_cells usegs m (q0 + -184) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 cap)] ->
  s2_okres TAPE SBUF (roundup64 (cap + 3)) (roundup64 (5 * (cap / 3) + 64)) (Z_to_bv 64 0) m ->
  (forall s' ms', pj_okarm_post q0 gp s4 s5 s6 s7 s8 s9 s10 s11 s LBall lo B m s' ms' -> implM usegs k s' Q ms') ->
  implM usegs (mbind (pj_chain lops PJ_FUEL len PJ_INLINE None) (fun blk => mbind (mbind (del_opt lops blk) (fun _ => pj_free_nulls lops)) (fun _ => k))) s Q
    (MS (mkR x1 (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_OKARM) fc None m (seg_rom usegs)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.
  Hypothesis OKARM : pj_okarm_stmt.

  Theorem rfuzz_one_of_parts : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM -> ->.
    unfold LX_FUZZ, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    set (q0 := bv_unsigned sp) in *.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. replace (errno_addr (Z_to_bv 64 RATP)) with 977220 in ERR by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN). clear PB.
    set (len := zlength d) in *. assert (LEN0 : 0 <= len) by (subst len; unfold zlength; lia). change (2^26) with 67108864 in DLEN.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q0 [LXW_SJ] a -> outside [(q0 - 496, q0)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q0 - 496, q0)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof LXS as (LX1 & LX2 & GOT & VT24 & VTD & PJC). clear LX1 LX2.
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI in VT24.
    unfold SJ_DPI_VPTR, SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT, SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY,
      SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL in VTD.
    unfold PjModel.fuzz_one, PjModel.fuzz_one_with, SJ_SBUF, SJ_TAPE, SJ_IMPL, SJ_IDX, SJ_OC, SJ_IA, sj_cap. fold len.
    cbn [bind ret lib_malloc lib_free lops Target.ops].
    rewrite ESP. unfold implM. iprefix.
    step. carve_frame 496%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 496 junk [] [8;8;4;4; 264; 1;7; 8; 1;3;4; 8;8;8; 8;1;7;8;8; 88; 8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. step. step. step. step. step. hstep. hstep. hstep. hstep. step. step. hstep. hstep. hstep. hstep. hstep. hstep. hstep. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    set (PARSER := q0 + -208).
    destruct (rw_cells_split_at _ _ _ 4%nat FR) as [SRETC R1]. cbn [firstn skipn cells_size csize Nat.add] in SRETC, R1.
    destruct (rw_cells_split_at _ _ _ 1%nat R1) as [GAPC R1b]. cbn [firstn skipn cells_size csize Nat.add] in GAPC, R1b.
    destruct (rw_cells_split_at _ _ _ 2%nat R1b) as [P0 R2]. cbn [firstn skipn cells_size csize Nat.add] in P0, R2.
    destruct (rw_cells_split_at _ _ _ 1%nat R2) as [PIMPL R3]. cbn [firstn skipn cells_size csize Nat.add] in PIMPL, R3.
    destruct (rw_cells_split_at _ _ _ 3%nat R3) as [P16 R4]. cbn [firstn skipn cells_size csize Nat.add] in P16, R4.
    destruct (rw_cells_split_at _ _ _ 3%nat R4) as [DOCC R5]. cbn [firstn skipn cells_size csize Nat.add] in DOCC, R5.
    destruct (rw_cells_split_at _ _ _ 5%nat R5) as [P48 R6]. cbn [firstn skipn cells_size csize Nat.add] in P48, R6.
    destruct (rw_cells_split_at _ _ _ 1%nat R6) as [SBAC RAC]. cbn [firstn skipn cells_size csize Nat.add] in SBAC, RAC.
    clear FR R1 R1b R2 R3 R4 R5 R6.
    repeat match goal with H : rw_cells _ _ ?a _ |- _ => progress (ring_simplify a in H) end.
    replace (q0 - 208) with PARSER in * by (subst PARSER; lia).
    replace (q0 - 200) with (PARSER + 8) in * by (subst PARSER; lia).
    replace (q0 - 192) with (PARSER + 16) in * by (subst PARSER; lia).
    replace (q0 - 184) with (PARSER + 24) in * by (subst PARSER; lia).
    replace (q0 - 160) with (PARSER + 48) in * by (subst PARSER; lia).
    replace (Z_to_bv 64 (q0 + -184)) with (Z_to_bv 64 (PARSER + 24)) by (f_equal; subst PARSER; lia).
    lazymatch type of P48 with rw_cells _ _ _ [_; _; CB 7 ?x; _; _] => set (j57 := x) in * end.
    lazymatch type of SRETC with rw_cells _ _ _ [_; _; _; CB 4 ?x] => set (jr20 := x) in * end.
    lazymatch type of P0 with rw_cells _ _ _ ?c => set (P0c := c) in * end.
    lazymatch type of P16 with rw_cells _ _ _ ?c => set (P16c := c) in * end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (SJS1 : sj_statics m1 init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; split; [lia| exact I]. }
    assert (PRES1 : lx_pres LB q0 [LXW_SJ] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    assert (PL1 : payload_ok m1 LB D d).
    { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
    clear MU WM.
    ihere. to_implM.
    eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := q0 + -496) (PARSER := PARSER) (D := D) (len := len) (init := init);
      [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
      | assert (ELX : LX_ERRNO = 977220) by reflexivity; rewrite ELX; exact ERR| assumption| lia| subst PARSER; lia| subst PARSER; lia| change (2^26) with 67108864; lia
      | unfold sj_ro, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_IMPL_VT24, SJ_CREATE_DPI, SJ_DPI_VPTR, dpi_vtable_cells, SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT,
          SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY, SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL; auto
      | exact SJS1| exact PIMPL| exact DOCC| unfold p48_cells; exact P48|].
    intros psb ptp pim pix poc pia st2 ms2 MID.
    unfold pj_copy_phase. cbn [bind ret lib_malloc lib_free lops Target.ops]. unfold SJ_PADMAX, SJ_COPY.
    set (cap := Z.max len 32) in *.
    set (REST := mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mret 0))))))).

    assert (TAIL : forall (ocp : option block) IMPL IDX OC IA TAPE SBUF (capw lcapv : word) sJ (mJ : mem)
              (x1 t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 t3 t4 t5 t6 : word) F' fc' (errvJ : word) bsA bsB
              (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
      frm0 fc' -> mem_inv usegs mJ -> stk usegs mJ lo (q0 + -496) -> rw_cells usegs mJ LX_ERRNO [C4 errvJ] -> rauxv_ok mJ B ->
      ps_fa sJ = ps_fa s -> ps_so sJ = ps_so s ->
      RHEAP sJ ((match ocp with Some b => [b] | None => [] end) ++ (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) mJ ->
      lx_pres LB q0 [LXW_SJ] m mJ -> sj_statics mJ true -> rw_cells usegs mJ SJ_DPI_VPTR dpi_vtable_cells ->
      rw_cells usegs mJ (q0 - 496) [CB 288 bsA] -> rw_cells usegs mJ PARSER P0c -> rw_cells usegs mJ (PARSER + 8) [C8 (Z_to_bv 64 IMPL)] ->
      rw_cells usegs mJ (PARSER + 16) P16c -> rw_cells usegs mJ (PARSER + 24) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 capw] ->
      rw_cells usegs mJ (PARSER + 48) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) ->
      rw_cells usegs mJ (q0 - 128) [CB 88 bsB] -> rw_cells usegs mJ (q0 - 40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs mJ IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
      implM usegs (match ocp with Some b => mbind (del lops (blk_id b)) (fun _ => REST) | None => REST end) sJ
        (rfuzz_one_post ra (Z_to_bv 64 q0) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR x1 (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 PJ_JOIN) fc' None mJ (seg_rom usegs))).
    { clear MID. intros ocp IMPL IDX OC IA TAPE SBUF capw lcapv sJ mJ x1 t0' t1' t2' u0 u1 a0' a1' a2' a3' a4' a5' a6' a7' u2 u3 t3' t4' t5' t6' F' fc' errvJ bsA bsB
             nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50.
      intros FRM2 MI2 ST2 ERR2 AUX2 FA2 SO2 HEAP2 PRES2 SJS2 VTD2 A288 P0J PIMPL2 P16J DOCC2 P482 B88 RACJ THISC.
      unfold PJ_JOIN.
      pose proof (munch_refl [(q0 - 496, q0)]%Z mJ) as MU. pose proof (wmono_refl usegs mJ) as WM.
      unfold implM. iprefix.

      step. step.
      change (Z_to_bv 64 (q0 + -208)) with (Z_to_bv 64 PARSER).
      ihere. to_implM. subst REST.
      eapply (pdtor_cps HF) with (B := B) (lo := lo) (ocp := ocp) (PARSER := PARSER) (IMPL := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (TAPE := TAPE) (SBUF := SBUF)
                                 (psb := psb) (ptp := ptp) (pim := pim) (pix := pix) (poc := poc) (pia := pia);
        [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| exact ERR2| exact MI2| lia| subst PARSER; lia| subst PARSER; lia
        | exact VTD2| exact PIMPL2| exact DOCC2| exact P482| exact THISC|].
      intros s3' ms3 PO3. unfold hpost in PO3.
      destruct PO3 as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3
                       & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
      unfold pdtor_R in RR. destruct RR as (HEAP3 & PRES23 & PIMPL3 & DOCC3 & P483).
      replace (ret_pc (Z_to_bv 64 249452)) with (Z_to_bv 64 249452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG.
      assert (FRCL : forall a, q0 + -496 <= a < q0 -> ~ rin_ivs (pdtor_X PARSER) a -> lx_client LB (q0 + -496) (pdtor_X PARSER) a) by (intros a Ha NX; split; [exact NX| left; lia]).
      apply (rw_cells_agree _ _ _ _ _ AG) in A288; [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pdtor_X; cbn [rin_ivs fst snd]; subst PARSER; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in P0J; [| intros a Ha; subst P0c; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pdtor_X; cbn [rin_ivs fst snd]; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in P16J; [| intros a Ha; subst P16c; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pdtor_X; cbn [rin_ivs fst snd]; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in B88; [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pdtor_X; cbn [rin_ivs fst snd]; subst PARSER; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in RACJ; [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pdtor_X; cbn [rin_ivs fst snd]; subst PARSER; lia]].
      assert (SJS3 : sj_statics m3 true).
      { eapply sj_statics_agree; [exact AG| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|].
        unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. unfold pdtor_X. cbn [rin_ivs fst snd]. subst PARSER. clear - Ha GLO LO. lia. }
      assert (PRES3 : lx_pres LB q0 [LXW_SJ] m m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB q0 _ _ _ _ _ _ PRES23); [lia| intros b0 Hb0; exact Hb0|].
        intros a Ha NX. unfold pdtor_X in Ha. cbn [rin_ivs fst snd] in Ha. split; [subst PARSER; lia|]. split; [intros IB; specialize (BLB a IB); subst PARSER; lia| subst PARSER; lia]. }

      unfold p48_cells in P483. subst P0c P16c.
      pose proof (rw_cells_join _ _ _ _ _ A288 P0J ltac:(subst PARSER; cbn [cells_size csize Nat.add]; lia)) as J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 PIMPL3 ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as J2.
      pose proof (rw_cells_join _ _ _ _ _ J2 P16J ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as J3.
      pose proof (rw_cells_join _ _ _ _ _ J3 DOCC3 ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as J4.
      pose proof (rw_cells_join _ _ _ _ _ J4 P483 ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as J5.
      pose proof (rw_cells_join _ _ _ _ _ J5 B88 ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as J6.
      pose proof (rw_cells_join _ _ _ _ _ J6 RACJ ltac:(subst PARSER; cbn [app cells_size csize Nat.add]; lia)) as FRJ.
      cbn [app] in FRJ. clear J1 J2 J3 J4 J5 J6 A288 P0J PIMPL3 P16J DOCC3 P483 B88 RACJ AG FRCL PRES2 PRES23 MU WM.
      replace (q0 - 496) with (q0 + -496) in FRJ by lia.
      pose proof (munch_refl [(q0 - 496, q0)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      apply implM_ret.

      step. step. step. step. step. step. step. release_frame FRJ ST3 q0. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      assert (PRESF : lx_pres LB q0 [LXW_SJ] m mF).
      { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESF) as AGF.
      rewrite <- ESP.
      apply evt_done. unfold rfuzz_one_post. do 15 eexists. exists F', fc', mF.
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { unfold lx_post_env. split; [| split; [exact FRM2| split; [exact PRESF| split; [congruence| congruence]]]].
        exists errv3. unfold lx_env. cbn [app].
        split. { eapply LH_frame; [exact HEAP3| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split. { eapply lx_statics_agree; [exact AGF| | exact LXS]. intros a Ha. apply lxs_addr_client; [exact Ha|].
                 pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
                 unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
        split. { exists true. eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS3]. intros a Ha.
                 unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
        split. { eapply stderr_wfile_agree; [exact AGF| | exact SEW]. intros a Ha. apply stderr_addr_client; [exact Ha|].
                 unfold stderr_addr in Ha. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
        split. { pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as EC. rewrite EC. eapply RHEAP_ssp.
                 eapply LH_frame; [exact HEAP3| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split. { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        split; [exact SPB|]. split; [clear - B63; lia|]. split; [exact ST3|]. split; [exact CEIL'|]. split; [unfold GLOBALS_TOP; lia|].
        split. { unfold errno_addr, RATP. rewrite unsigned_lit by lia. assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in *. assumption. }
        split; [reflexivity| assumption]. }
      split. { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS3]. intros a Ha.
               unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
      split; [reflexivity|]. split; [reflexivity|].
      eapply payload_ok_agree; [exact AGF| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }

    assert (FIN : forall (ocp : option block) IMPL IDX OC IA TAPE SBUF lcapv s' ms',
      hpostF (Z_to_bv 64 249268) (q0 + -496) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s lo B
        (pid_R ((match ocp with Some b => [b] | None => [] end) ++ (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB)
               LB (q0 + -496) (q0 + -496) PARSER m1 (Z_to_bv 8 0) j57 jr20
               IMPL IDX OC IA TAPE SBUF cap (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) s' ms' ->
      (match ocp with Some _ => len <= 1048512 | None => True end) ->
      implM usegs (match ocp with Some b => mbind (pj_print lops len) (fun _ => mbind (del lops (blk_id b)) (fun _ => REST)) | None => REST end) s' (rfuzz_one_post ra (Z_to_bv 64 q0) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m) ms').
    2:{ destruct (Z.leb_spec len 1048512) as [LE|GT].
        - apply implM_bind_assoc.
          eapply (implM_bind_ext usegs) with (f := fun cp => mbind (parse_model (SjAlloc.strip_bom d)) (fun _ => mbind (pj_print lops len) (fun _ => mbind (del lops cp) (fun _ => REST)))).
          { intros cp s' ms' H. apply implM_bind_assoc. eapply (implM_bind_ext usegs); [| exact H]. intros u s'' ms'' H2. apply implM_bind_assoc. exact H2. }
          eapply (pj_pid_copy_cps HM S2) with (B := B) (lo := lo) (m00 := m1) (s00 := s);
            [exact MID| exact LE| exact HEAP1| exact PL1| exact FRM| lia| clear - B63; lia| exact CEIL'| unfold GLOBALS_TOP; lia
            | unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia| replace (q0 + -496) with (q0 + (-31) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
            | lia| subst PARSER; lia| subst PARSER; lia| subst PARSER; apply (mod16_off8 q0 (-26) AL16)| exact SRETC|].
          intros pcp s' ms' (IMPL & IDX & OC & IA & TAPE & SBUF & COPY & PO).
          exact (FIN (Some (pcp, COPY, len + 64)) IMPL IDX OC IA TAPE SBUF _ s' ms' PO LE).
        - apply implM_ret_bind.
          eapply (pj_pid_big_cps) with (B := B) (lo := lo) (m00 := m1) (s00 := s) (k := REST);
            [exact MID| lia| exact HEAP1| exact FRM| lia| clear - B63; lia| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| lia| subst PARSER; lia| subst PARSER; lia| exact SRETC|].
          intros s' ms' (IMPL & IDX & OC & IA & TAPE & SBUF & PO).
          exact (FIN None IMPL IDX OC IA TAPE SBUF _ s' ms' PO I). }
    clear MID.
    intros ocp IMPL IDX OC IA TAPE SBUF lcapv s' ms' PO LE.
    unfold hpostF in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m2
                    & -> & FRM2 & MI2 & ST2 & (errv2 & ERR2) & AUX2 & FA2 & SO2 & RR).
    unfold pid_R in RR.
    destruct RR as (HEAP2 & PRES12 & (GOT2 & VT242 & VTD2) & SJS2 & PIMPL2 & DOCC2 & P482 & (r & SRET2 & OKR & RNZ)
                    & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THISC & ->) & BRTP & BRSB).
    replace (ret_pc (Z_to_bv 64 249268)) with (Z_to_bv 64 249268) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (XFR : forall a, rin_ivs (pid_front_X PARSER ++ pid_back_X (q0 + -496) PARSER) a -> ~ rin_ivs [LXW_SJ] a -> q0 + -496 <= a < q0).
    { intros a Ha NX. unfold pid_front_X, pid_back_X in Ha. cbn [app rin_ivs fst snd] in Ha, NX. subst PARSER. clear - Ha NX. lia. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES12) as AG.
    assert (FRCL : forall a, q0 + -496 <= a < q0 -> ~ rin_ivs (pid_front_X PARSER ++ pid_back_X (q0 + -496) PARSER) a ->
              lx_client LB (q0 + -496) (pid_front_X PARSER ++ pid_back_X (q0 + -496) PARSER) a) by (intros a Ha NX; split; [exact NX| left; lia]).
    subst P0c P16c.
    apply (rw_cells_agree _ _ _ _ _ AG) in P0;
      [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; subst PARSER; clear - Ha GLO LO; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in P16;
      [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; subst PARSER; clear - Ha GLO LO; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in RAC;
      [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; subst PARSER; clear - Ha GLO LO; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in GAPC;
      [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; subst PARSER; clear - Ha GLO LO; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in SBAC;
      [| intros a Ha; cbn in Ha; apply FRCL; [subst PARSER; lia| unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; subst PARSER; clear - Ha GLO LO; lia]].
    assert (PRES2 : lx_pres LB q0 [LXW_SJ] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB q0 _ _ _ _ _ _ PRES12); [lia| intros b0 Hb0; exact Hb0|].
      intros a Ha NX. pose proof (XFR a Ha NX) as R. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
    clear AG PRES1 PRES12 HEAP1 AUX1 SJS1 PL1 PIMPL DOCC P48 SRETC XFR FRCL GOT VT24 VTD.
    assert (ELX : LX_ERRNO = 977220) by reflexivity.

    destruct OKR as [KE|(E0 & OKT)].
    -
      assert (ER : bv_eqb r (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite unsigned_lit by lia; apply Z.eqb_neq; lia).
      unfold pj_res_cells in SRET2. rewrite ER in SRET2.
      rewrite <- (Z_to_bv_bv_unsigned r) in SRET2. set (rv := bv_unsigned r) in *.
      pose proof (munch_refl [(q0 - 496, q0)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      assert (GO : implM usegs (match ocp with Some b => mbind (del lops (blk_id b)) (fun _ => REST) | None => REST end) s' (rfuzz_one_post ra (Z_to_bv 64 q0) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
                     (MS (mkR (Z_to_bv 64 249268) (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) u5 u6 u7 s0 s1 u10 u11 u12 u13 u14 u15 u16 u17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u28 u29 u30 u31)
                         F' (Z_to_bv 64 249268) fc' None m2 (seg_rom usegs))).
      { unfold implM. iprefix.

        step. step. step.
        change (Z_to_bv 64 rv) with (MallocRep.wz rv). rewrite MallocRep.sx32_wz by lia. unfold MallocRep.wz.
        if_cases KU. { exfalso. revert KU. unfold_cond. rewrite !unsigned_lit by lia. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. }
        step. if_cases KG.
        2:{ exfalso. unfold bv_eqb in KG. rewrite !unsigned_lit in KG by lia. destruct (Z.eqb_spec rv 0); [lia| discriminate KG]. }
        pose proof (rw_cells_join _ _ _ _ _ SRET2 GAPC ltac:(cbn [cells_size csize Nat.add]; lia)) as JA.
        apply rw_cells_forget in JA. destruct JA as [bsA JA]. cbn [app cells_size csize Nat.add] in JA.
        ihere. to_implM.
        eapply (TAIL ocp IMPL IDX OC IA TAPE SBUF); [exact FRM2| exact MI2| exact ST2| exact ERR2| exact AUX2| exact FA2| exact SO2| exact HEAP2| exact PRES2| exact SJS2| exact VTD2
          | exact JA| exact P0| exact PIMPL2| exact P16| exact DOCC2| exact P482| exact SBAC| exact RAC| exact THISC]. }
      destruct ocp as [b|]; [| exact GO].
      apply (PjImpl.implM_pj_gate_fail usegs raw_malloc raw_free ps_so set_so_ps len (fun _ => mbind (del lops (blk_id b)) (fun _ => REST))). exact GO.
    -
      subst r. destruct ocp as [b|]; [| exfalso; exact (RNZ eq_refl eq_refl)].
      unfold pj_res_cells in SRET2.
      lazymatch type of SRET2 with context [bv_eqb ?x ?y] => change (bv_eqb x y) with true in SRET2 end. cbv iota in SRET2.
      apply (PjImpl.implM_pj_gate_ok usegs raw_malloc raw_free ps_so set_so_ps len (fun _ => mbind (del lops (blk_id b)) (fun _ => REST))).
      pose proof (munch_refl [(q0 - 496, q0)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. step. step. if_false. step. if_false.
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES2)| | exact LXS]. intros a Ha. apply lxs_addr_client; [exact Ha|].
        unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
        unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      assert (SSP2 : ssp_cells m2 canary).
      { pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as EC. rewrite EC. eapply RHEAP_ssp. exact HEAP2. }
      pose proof DOCC2 as DOCC2'. replace (PARSER + 24) with (q0 + -184) in DOCC2' by (subst PARSER; lia).
      pose proof SRET2 as SRET2'. replace (PARSER + 24) with (q0 + -184) in SRET2' by (subst PARSER; lia).
      cbn [app] in HEAP2.
      ihere. to_implM.
      eapply (OKARM _ (mbind (del lops (blk_id b)) (fun _ => REST))) with (q0 := q0) (lo := lo) (B := B) (len := len) (TAPE := TAPE) (SBUF := SBUF) (cap := cap)
                     (ptp := ptp) (psb := psb) (canary := canary);
        [exact HEAP2| do 5 right; left; reflexivity| do 6 right; left; reflexivity| exact AUX2| exact SPB| exact B63| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia
        | unfold PJ_OKARM_STACK; lia| exact ERR2| exact MI2| exact FRM2| exact AL16| lia| exact LXS2| exact SJS2| exact SSP2| lia| reflexivity
        | exact SRET2'| exact GAPC| exact SBAC| exact DOCC2'| right; split; [reflexivity| exact OKT]|].
      intros sJ msJ PJ. unfold pj_okarm_post in PJ.
      destruct PJ as (x1 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w28 & w29 & w30 & w31 & FJ & fcJ & mJ & errvJ
                      & -> & FRMJ & MIJ & STJ & ERRJ & AUXJ & FAJ & SOJ & HEAPJ & PRESJ & SJSJ & (bsA & A288) & (bsB & B88)).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESJ) as AGJ.
      assert (FRJC : forall a, q0 + -208 <= a < q0 + -128 \/ q0 + -40 <= a < q0 -> lx_client (b :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) (q0 + -496) (pj_okarm_X q0) a).
      { intros a Ha. split; [| left; lia]. unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha GLO LO. lia. }
      apply (rw_cells_agree _ _ _ _ _ AGJ) in P0; [| intros a Ha; cbn in Ha; apply FRJC; subst PARSER; lia].
      apply (rw_cells_agree _ _ _ _ _ AGJ) in PIMPL2; [| intros a Ha; cbn in Ha; apply FRJC; subst PARSER; lia].
      apply (rw_cells_agree _ _ _ _ _ AGJ) in P16; [| intros a Ha; cbn in Ha; apply FRJC; subst PARSER; lia].
      apply (rw_cells_agree _ _ _ _ _ AGJ) in DOCC2; [| intros a Ha; cbn in Ha; apply FRJC; subst PARSER; lia].
      apply (rw_cells_agree _ _ _ _ _ AGJ) in P482; [| intros a Ha; unfold p48_cells in Ha; cbn in Ha; apply FRJC; subst PARSER; lia].
      apply (rw_cells_agree _ _ _ _ _ AGJ) in RAC; [| intros a Ha; cbn in Ha; apply FRJC; lia].
      pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 4 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS). cbn [blk_addr blk_size fst snd] in IM0, IMC, IMS.
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
      apply (rw_cells_agree _ _ _ _ _ AGJ) in THISC.
      2:{ intros a Ha. unfold impl_cells16 in Ha. cbn in Ha. split.
          - unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha IM0 IMC IMS CEIL LO GLO. lia.
          - right; left. exists (pim, IMPL, 96). split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AGJ) in VTD2.
      2:{ intros a Ha. unfold dpi_vtable_cells in Ha. cbn in Ha. unfold SJ_DPI_VPTR in Ha. split.
          - unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha LO GLO. lia.
          - right; right. split; [lia|]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
      assert (PRESF : lx_pres LB q0 [LXW_SJ] m mJ).
      { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB q0 _ _ _ _ _ _ PRESJ); [lia| intros b0 Hb0; do 7 right; exact Hb0|].
        intros a Ha NX. unfold pj_okarm_X in Ha. cbn [rin_ivs fst snd] in Ha, NX. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
      eapply (TAIL (Some b) IMPL IDX OC IA TAPE SBUF); [exact FRMJ| exact MIJ| exact STJ| exact ERRJ| exact AUXJ| congruence| congruence| exact HEAPJ| exact PRESF| exact SJSJ| exact VTD2
          | exact A288| exact P0| exact PIMPL2| exact P16| exact DOCC2| exact P482| exact B88| exact RAC| exact THISC].
  Qed.
End Proofs.
End WithCeiling0.
