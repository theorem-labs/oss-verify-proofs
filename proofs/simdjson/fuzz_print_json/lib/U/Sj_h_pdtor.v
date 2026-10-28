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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_dtor Sj_h_create.
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

Definition SJ_PARSER_DTOR : Z := 0x3d018.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pdtor_X (PARSER : Z) : list (Z * Z) := [(PARSER + 8, PARSER + 16); (PARSER + 24, PARSER + 40); (PARSER + 64, PARSER + 72)].

Definition pdtor_R (LB : list block) (q PARSER : Z) (m : mem) (j57 : list byte) (cap lcapv : word) : word -> PState -> mem -> Prop :=
  fun _ s' m' =>
    RHEAP s' LB m' /\ lx_pres LB q (pdtor_X PARSER) m m'
    /\ rw_cells usegs m' (PARSER + 8) [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' (PARSER + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 cap]
    /\ rw_cells usegs m' (PARSER + 48) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 0) lcapv).

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma pdtor_tail_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra0 xra gp t0 t1 t2 s0o s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (s s00 : PState) (LB : list block) (q lo B : Z) (errv : word)
      (PARSER IMPL IDX OC IA TAPE SBUF nix ntp nsb : Z) (psb ptp pim pix poc pia : bptr) (j57 : list byte) (cap lcapv : word)
      (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    RHEAP s ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (ptp, TAPE, ntp) :: (psb, SBUF, nsb) :: LB) m ->
    rauxv_ok m B -> q <= B -> stk usegs m lo (q + -16) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (16 + 16 + RFREE_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 -> q <= PARSER -> PARSER + 80 <= B ->
    ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 ->
    lx_pres LB q (pdtor_X PARSER) m0 m ->
    rw_cells usegs m (q + -16) [C8 s0o; C8 ra0] ->
    rw_cells usegs m SJ_DPI_VPTR dpi_vtable_cells ->
    rw_cells usegs m (PARSER + 8) [C8 (Z_to_bv 64 IMPL)] ->
    rw_cells usegs m (PARSER + 24) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 cap] ->
    rw_cells usegs m (PARSER + 48) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 0) lcapv) ->
    rw_cells usegs m IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    (forall s' ms', hpost ra0 q gp s0o s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 lo B (pdtor_R LB q PARSER m0 j57 cap lcapv) s' ms' -> implM usegs k s' Q ms') ->
    implM usegs (mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => k))))))) s Q
      (MS (mkR xra (Z_to_bv 64 (q + -16)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 PARSER) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3d038) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until p50. intros HEAP AUX QB ST CEIL GLO LO ERR MI Hq QP PB FA0 SO0 PRES0 FR VTD PIMPL DOCC P48 THISC HK.
    unfold RFREE_STACK, GLOBALS_TOP, p48_cells, impl_cells16, SJ_DPI_VPTR, dpi_vtable_cells in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS). cbn [blk_addr blk_size fst snd] in *.
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(do 6 right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q (pdtor_X PARSER) a -> outside [(q - 16, q); (PARSER + 8, PARSER + 16)] a).
    { intros a Ha [HX HC]. unfold pdtor_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 16, q); (PARSER + 8, PARSER + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold implM. iprefix.

    step. step.
    assert (HEAPD : RHEAP s ((psb, SBUF, nsb) :: (ptp, TAPE, ntp) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: LB) m).
    { pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, nix); (pim, IMPL, 96)] _ _ _ HEAP) as H1. cbn [app] in H1.
      exact (RHEAP_pull _ [(ptp, TAPE, ntp); (pia, IA, 1024); (poc, OC, 8192); (pix, IDX, nix); (pim, IMPL, 96)] _ _ _ H1). }
    ihere. to_implM.
    eapply (docdtor_cps HF) with (B := B) (lo := lo) (DOC := PARSER + 24) (TAPE := TAPE) (SBUF := SBUF) (ntp := ntp) (nsb := nsb);
      [exact HEAPD| exact AUX| lia| exact ST| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia| lia| exact DOCC|].
    intros s1' ms1 PO. unfold hpost in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1
                    & -> & MI1 & ST1 & (errv1 & ERR1) & AUX1 & FA1 & SO1 & RR).
    unfold docdtor_R in RR. destruct RR as (HEAP1 & PRES01 & DOCC1).
    replace (ret_pc (Z_to_bv 64 249920)) with (Z_to_bv 64 249920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES01) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in THISC;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; left; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]].
    assert (PRES1 : lx_pres LB q (pdtor_X PARSER) m0 m1).
    { eapply lx_pres_trans; [exact PRES0|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      eapply lx_pres_weaken; [exact PRES01| lia| intros b Hb; do 4 right; exact Hb|].
      intros a Ha. unfold pdtor_X. cbn [rin_ivs fst snd] in Ha |- *. clear - Ha. lia. }
    clear AG PRES0 PRES01 MU WM HEAPD.
    pose proof (munch_refl [(q - 16, q); (PARSER + 8, PARSER + 16)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold implM. iprefix.

    step. hstep. step.
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.

    zstep. step.
    rewrite (land7_aligned IMPL) by (pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(do 3 right; left; reflexivity)) as (? & AL16 & _); cbn [blk_addr blk_size fst snd] in *; first [lia| exact AL16]).
    if_false.
    do 5 step. release_frame FR ST1 q. step.
    replace (ret_pc (Z_to_bv 64 SJ_DPI_DTOR_DEL)) with (Z_to_bv 64 SJ_DPI_DTOR_DEL) by (symmetry; apply ret_pc_even; [unfold SJ_DPI_DTOR_DEL; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HEAP2 : RHEAP s1' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: LB) m2).
    { eapply LH_frame; [exact HEAP1| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres LB q (pdtor_X PARSER) m0 m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    ihere. to_implM.
    eapply (dpidtor_cps HF) with (B := B) (lo := lo) (THIS := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (nix := nix) (noc := 8192) (nia := 1024);
      [exact HEAP2| exact AUX2| lia| exact ST1| exact CEIL'| unfold RFREE_STACK; lia| exact ERR1| assumption| lia| unfold impl_cells16; exact THISC|].
    intros s3' ms3 PO. unfold hpost in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3
                    & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & (HEAP3 & PRES23)).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG.
    apply HK. unfold hpost. do 15 eexists. exists m3.
    split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists errv3; exact ERR3|]. split; [exact AUX3|].
    split; [congruence|]. split; [congruence|].
    unfold pdtor_R, p48_cells. split; [exact HEAP3|].
    split. { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES23| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a []]. }
    split. { eapply (rw_cells_agree _ _ _ _ _ AG); [eassumption|]. intros a Ha; cbn in Ha; split; [cbn [rin_ivs]; tauto| left; lia]. }
    split. { eapply (rw_cells_agree _ _ _ _ _ AG); [eassumption|]. intros a Ha; cbn in Ha; split; [cbn [rin_ivs]; tauto| left; lia]. }
    eapply (rw_cells_agree _ _ _ _ _ AG); [eassumption|]. intros a Ha; cbn in Ha; split; [cbn [rin_ivs]; tauto| left; lia].
  Qed.

  Lemma pdtor_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (PARSER IMPL IDX OC IA TAPE SBUF nix ntp nsb : Z) (psb ptp pim pix poc pia : bptr) (j57 : list byte) (cap lcapv : word)
      (ocp : option (bptr * Z * Z))
      (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    RHEAP s ((match ocp with Some b => [b] | None => [] end) ++
             (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (ptp, TAPE, ntp) :: (psb, SBUF, nsb) :: LB) m ->
    rauxv_ok m B -> q <= B -> stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (16 + 16 + RFREE_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 -> q <= PARSER -> PARSER + 80 <= B ->
    rw_cells usegs m SJ_DPI_VPTR dpi_vtable_cells ->
    rw_cells usegs m (PARSER + 8) [C8 (Z_to_bv 64 IMPL)] ->
    rw_cells usegs m (PARSER + 24) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 cap] ->
    rw_cells usegs m (PARSER + 48) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) ->
    rw_cells usegs m IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    (forall s' ms', hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B (pdtor_R LB q PARSER m j57 cap lcapv) s' ms' -> implM usegs k s' Q ms') ->
    implM usegs (match ocp with
                 | Some b => mbind (del lops (blk_id b)) (fun _ => mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ =>
                               mbind (del lops poc) (fun _ => mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => k)))))))
                 | None => mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ =>
                               mbind (del lops poc) (fun _ => mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => k))))))
                 end) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 PARSER) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_PARSER_DTOR) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until p50. intros HEAP AUX QB ST CEIL GLO LO ERR MI Hq QP PB VTD PIMPL DOCC P48 THISC HK.
    unfold SJ_PARSER_DTOR, RFREE_STACK, GLOBALS_TOP, p48_cells in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; do 6 right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q (pdtor_X PARSER) a -> outside [(q - 16, q); (PARSER + 64, PARSER + 72)] a).
    { intros a Ha [HX HC]. unfold pdtor_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 16, q); (PARSER + 64, PARSER + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold SJ_DPI_VPTR, dpi_vtable_cells in VTD. unfold impl_cells16 in THISC.
    hide THISC. hide VTD.
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. hstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    unhide THISC. unhide VTD.
    assert (PRES1 : lx_pres LB q (pdtor_X PARSER) m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    destruct ocp as [[[pcp COPY] ncp]|]; cbn [app blk_addr blk_id fst snd] in *.
    -
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(left; reflexivity)) as (CP0 & _ & CPn & CPC & CPS). cbn [blk_addr blk_size fst snd] in *.
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CPC.
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(do 4 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS). cbn [blk_addr blk_size fst snd] in *.
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
      apply (rw_cells_agree _ _ _ _ _ AG) in THISC; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha IMC CEIL LO QP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in VTD; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha GLO LO QP; lia].
      if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
      step.
      assert (HEAP1 : RHEAP s ((pcp, COPY, ncp) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (ptp, TAPE, ntp) :: (psb, SBUF, nsb) :: LB) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (ND : List.NoDup (map blk_id ((pcp, COPY, ncp) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (ptp, TAPE, ntp) :: (psb, SBUF, nsb) :: LB)))
        by (eapply LH_nodup; exact HEAP).
      ihere. to_implM. eapply implM_bind.
      { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := COPY) (n := ncp);
          [exact HEAP1| left; reflexivity| exact AUX1| lia| exact ST| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR| exact MI| lia]. }
      cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & HEAP2).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP, HEAP2.
      replace (ret_pc (Z_to_bv 64 0x3d038)) with (Z_to_bv 64 0x3d038) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG2.
      apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in PIMPL; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in P48; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in VTD;
        [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in THISC;
        [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| cbn in Ha |- *; lia]].
      eapply (pdtor_tail_cps k Q ra) with (B := B) (lo := lo) (m0 := m) (s00 := s) (IMPL := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (TAPE := TAPE) (SBUF := SBUF);
        [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| exact ERR2| exact MI2| lia| lia| lia| exact FA2| exact SO2
        | | exact FR| exact VTD| exact PIMPL| exact DOCC| unfold p48_cells; exact P48| exact THISC| exact HK].
      eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; do 6 right; exact Hb].
    -
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS). cbn [blk_addr blk_size fst snd] in *.
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
      apply (rw_cells_agree _ _ _ _ _ AG) in THISC; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha IMC CEIL LO QP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in VTD; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha GLO LO QP; lia].
      if_true.
      ihere. to_implM.
      eapply (pdtor_tail_cps k Q ra) with (B := B) (lo := lo) (m0 := m) (s00 := s) (IMPL := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (TAPE := TAPE) (SBUF := SBUF);
        [| | lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia| lia| reflexivity| reflexivity
        | exact PRES1| exact FR| exact VTD| exact PIMPL| exact DOCC| unfold p48_cells; exact P48| exact THISC| exact HK].
      + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
  Qed.

End Proofs.
End WithCeiling0.
