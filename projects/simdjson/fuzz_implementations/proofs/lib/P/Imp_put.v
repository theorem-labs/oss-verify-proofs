(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_steps Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit Imp_oss_defs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac name_mem mx := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => rename m into mx end.

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | u8arr _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r end; fail "PROBE".

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition use_facet_postZ (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 0xe8af8) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 48, q)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo q
    /\ LOCB m'.
Lemma use_facet_ctype_specZ : forall ra q gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo P : Z),
  stk psegs m lo q -> lo <= q - 48 -> 0x10b000 <= lo ->
  LOCB m -> rw_cells psegs m P [C8 (Z_to_bv 64 0xe8bd8)] -> q <= P -> P < 2^63 -> mem_inv psegs m ->
  evt psegs (use_facet_postZ ra q gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 0xe8890) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0edc) fc None m (seg_rom psegs)).
Proof.
  intros until P. intros ST LO GLO LB LOC QP PH MI.
  assert (Q0 : 0 <= q) by (destruct ST as [? _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply (use_facet_ctype_spec ra (Z_to_bv 64 q)) with (lo := lo) (P := P); rewrite ?U; try assumption; lia.
  - intros ms' PO. unfold use_facet_post in PO. unfold use_facet_postZ. rewrite U in PO. exact PO.
Qed.

Theorem put_proof : xsputn_stmt -> put_stmt.
Proof.
  intros XSP. unfold put_stmt, OSS_PUT. intros until bs. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB VT WS GCT LB HL INV BUFC N0 BUF0 SRC ACC.
  unfold OSS_PUT_STACK, OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (ELX : LX_ERRNO = 957684) by reflexivity. rewrite ELX in ERR.
  assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
    unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (SSEP : BUF + N <= lo \/ (O + 264 <= BUF /\ BUF + N <= B)).
  { destruct SRC as [(bk & Hbk & Hlo & Hhi)|[H1 H2]]; [left| right; split; [exact H1| exact H2]].
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hbk)) as (_ & _ & _ & BC & _).
    unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  pose proof (OSNUM_cap24 len st ltac:(apply INV)) as CAP24.
  destruct INV as [[[PUTC [[hm [HMC HMR]] [j108 MODE]]] [REP NUM]] [OSV [j124 [j260 IOSC]]]].
  unfold sb_cellsI in PUTC. unfold ios_cellsI in IOSC.
  destruct VT as (V1 & V2 & V3 & V4).
  unfold OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR, OSS_XSPUTN, OSS_OVERFLOW, OSS_CLASSIC in *.
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.

  retype_at IOSC 20%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
  retype_at IOSC 1%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].

  hide REP.
  pose proof (munch_refl [(q - 192 - 64 - 80 - 64 - 16 - 8192, q); (O + 136, O + 144); (O + 256, O + 260)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  destruct (Z.eq_dec N 0) as [EN0|N1].
  -
    subst N. apply implM_pj_part_stop; [lia|].
    carve_frame 96%nat ST.
    do 22 lstep.
    if_true.
    do 2 lstep.
    if_true.
    do 5 lstep.
    if_false.
    do 17 lstep.
    if_false.
    do 3 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (q + -96).
    do 3 lstep.
    lstep.
    takeZ FR 4%nat (q + -72) F0. takeZ FR 1%nat (q + -64) LTMP.
    call (use_facet_ctype_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (q + -72));
      [exact ST| lia| lia| exists l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15; exact LBC| exact LTMP| lia| lia| assumption|].
    rename PC into ST. destruct POST as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC').
    clear LBC. unfold locb_cells in LBC'.
    glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
    do 13 lstep.
    if_true.
    do 10 lstep.
    if_false.
    do 6 lstep.
    carve_frame 96%nat ST.
    do 11 lstep.
    if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 9 lstep.
    try replace (BUF + - BUF) with 0 by lia.
    if_true.
    do 6 lstep.
    try replace (BUF + - BUF) with 0 by lia. if_true.
    do 2 lstep.
    try replace (BUF + - BUF) with 0 by lia. try replace (BUF + 0 + - BUF) with 0 by lia. if_true.
    do 14 lstep.
    release_frame FR0 ST (q + -96).
    lstep.
    if_cases K; zify_cond K; [try clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    do 2 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 2 lstep.
    if_false.
    do 3 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (q + -96).
    do 11 lstep.
    release_frame FR ST q.
    retype_at IOSC 20%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    retype_at IOSC 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    unhide REP. pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (REP9 : STRREP m9 O st).
    { unfold STRREP in REP |- *. destruct (os_blk st).
      - destruct REP as (R3 & (bsr & BLK) & RB). pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        split; [| split; [| exact RB]].
        + eapply rw_cells_agree; [exact AG| exact R3| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact BLK| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
      - destruct REP as (R1 & (bsr & R23) & ED). split; [| split; [| exact ED]].
        + eapply rw_cells_agree; [exact AG| exact R1| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact R23| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia]. }
    apply evt_done. unfold put_post. do 14 eexists. exists m9, errv, st.
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [exact ST|]. split; [rewrite ELX; exact ERR|].
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split. { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { split; [split; [split; [exact PUTC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [exact REP9| exact NUM]]|].
             split; [exact OSV| exists j124, j260; exact IOSC]. }
    split; [exists l1', l2', l3', l4', l5', l6', l7', l8', l9', l10', l11', l12', l13', l14', l15'; exact LBC'|].
    eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside].
    split; [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]|]. split; [lia|]. split; [lia| exact I].
  -
    apply implM_pj_part_seq. unfold implM. iprefix.
    carve_frame 96%nat ST.
    do 22 lstep.
    if_true.
    do 2 lstep.
    if_true.
    do 5 lstep.
    if_false.
    do 17 lstep.
    if_false.
    do 3 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (q + -96).
    do 3 lstep.
    lstep.
    takeZ FR 4%nat (q + -72) F0. takeZ FR 1%nat (q + -64) LTMP.
    call (use_facet_ctype_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (q + -72));
      [exact ST| lia| lia| exists l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15; exact LBC| exact LTMP| lia| lia| assumption|].
    rename PC into ST. destruct POST as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC').
    clear LBC. unfold locb_cells in LBC'.
    glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
    do 13 lstep.
    if_true.
    do 10 lstep.
    if_false.
    do 6 lstep.
    carve_frame 96%nat ST.
    do 11 lstep.
    if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 9 lstep.
    try replace (BUF + - BUF) with 0 by lia.
    if_true.
    do 6 lstep.
    replace (BUF + N + - BUF) with N by lia.
    replace (Z.lxor N 9223372036854775808 <? 9223372036854775808) with false
      by (symmetry; apply Z.ltb_ge; change 9223372036854775808 with (2^63); rewrite zb_lxor_pow2_small by lia; lia).
    cbn [Z.b2z]. replace (Z.land (0 + - 0) 18446744073709551615) with 0 by reflexivity. rewrite Z.land_0_l.
    if_true.
    do 2 lstep.
    try replace (BUF + N + - BUF) with N by lia.
    if_cases K; zify_cond K; [exfalso; rewrite ?signed_lit, ?unsigned_lit in K by lia; lia| try clear K].

    do 5 lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    unhide REP. pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (REP5 : STRREP m5 O st).
    { unfold STRREP in REP |- *. destruct (os_blk st).
      - destruct REP as (R3 & (bsr & BLK) & RB). pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        split; [| split; [| exact RB]].
        + eapply rw_cells_agree; [exact AG| exact R3| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact BLK| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
      - destruct REP as (R1 & (bsr & R23) & ED). split; [| split; [| exact ED]].
        + eapply rw_cells_agree; [exact AG| exact R1| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact R23| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia]. }
    clear REP AG.
    assert (HEAP5 : RHEAP s (osblocks st ++ LB0) m5).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES5 : lx_pres LB0 q [(O, O + 264)] m m5).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside].
      split; [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]|]. split; [lia|]. split; [lia| exact I]. }
    clear MU WM HEAP AUX.
    ihere. to_implM. eapply implM_bind.
    { eapply XSP with (m := m5) (s := s) (LB0 := LB0) (q := q + -192) (lo := lo) (B := B) (errv := errv) (O := O) (len := len) (st := st) (bs := bs);
        [exact HEAP5| exact AUX5| lia| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR| assumption| lia| lia
        | unfold imp_vt_rows, OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_XSPUTN, OSS_OVERFLOW, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR;
          split; [exact V1| split; [exact V2| split; [exact V3| exact V4]]]
        | exact HL
        | split; [split; [exact PUTC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [exact REP5| exact NUM]]
        | exact BUFC| lia| lia| exact SRC| exact ACC]. }
    cbv beta. intros ch s' ms' PO. unfold xsputn_post in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m6 & errv6 & st6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & FA6 & SO6 & ECH & W6 & HEAP6 & INV6 & PRES6).
    subst ch. replace (ret_pc (Z_to_bv 64 0x41cc4)) with (Z_to_bv 64 0x41cc4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR6.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES6) as AG6.
    assert (CL : forall a, (q + -192 <= a /\ (a < O + 8 \/ O + 112 <= a)) \/ (951768 <= a < 955528) \/ (864256 <= a < 878152) -> lx_client LB0 (q + -192) [(O + 8, O + 112)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia|]. destruct Ha as [Ha|Ha]; [left; lia| right; right]. split; [lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    apply (rw_cells_agree _ _ _ _ _ AG6) in FR; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FR0; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in IOSC; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in OSV; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in LBC'; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in V3; [| intros a Ha; cbn in Ha; apply CL; lia].
    clear AG6 CL V1 V2 V4 PUTC HMC MODE REP5 BUFC ERR ST HEAP5 AUX5. rename ST6 into ST.
    destruct INV6 as [[PUTC [[hm6 [HMC HMR6]] [j108' MODE]]] [REP NUM6]]. unfold sb_cellsI in PUTC. unfold OSS_SB_VPTR, OSS_CLASSIC in PUTC. hide REP.
    pose proof (munch_refl [(q - 192, q); (O + 136, O + 144)]%Z m6) as MU. pose proof (wmono_refl psegs m6) as WM.
    apply implM_pj_part_stop; [pose proof (OSNUM_cap24 len st6 NUM6); cbn [ch_cap os_ch fst snd]; lia|].
    cbn [ch_fuel ch_cap ch_blk os_ch fst snd].

    lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 14 lstep.
    release_frame FR0 ST (q + -96).
    lstep.
    if_cases K; zify_cond K; [try clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    do 2 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 2 lstep.
    if_false.
    do 3 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (q + -96).
    do 11 lstep.
    release_frame FR ST q.
    retype_at IOSC 20%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    retype_at IOSC 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    unhide REP. pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (REP9 : STRREP m9 O st6).
    { unfold STRREP in REP |- *. destruct (os_blk st6).
      - destruct REP as (R3 & (bsr & BLK) & RB). pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        split; [| split; [| exact RB]].
        + eapply rw_cells_agree; [exact AG| exact R3| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact BLK| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
      - destruct REP as (R1 & (bsr & R23) & ED). split; [| split; [| exact ED]].
        + eapply rw_cells_agree; [exact AG| exact R1| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact R23| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia]. }
    apply evt_done. unfold put_post. do 14 eexists. exists m9, errv6, st6.
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [exact ST|]. split; [rewrite ELX; exact ERR6|].
    split. { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [exact FA6|]. split; [exact SO6|]. split; [reflexivity|]. split; [exact W6|].
    split. { eapply LH_frame; [exact HEAP6| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { split; [split; [split; [exact PUTC| split; [exists hm6; split; [exact HMC| exact HMR6]| exists j108'; exact MODE]]| split; [exact REP9| exact NUM6]]|].
             split; [exact OSV| exists j124, j260; exact IOSC]. }
    split; [exists l1', l2', l3', l4', l5', l6', l7', l8', l9', l10', l11', l12', l13', l14', l15'; exact LBC'|].
    eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_trans.
    { eapply lx_pres_weaken; [exact PRES6| lia| intros b0 Hb0; exact Hb0| intros a Ha; cbn [rin_ivs fst snd] in *; lia]. }
    eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside].
    assert (BLB6 : forall a', in_block LB0 a' -> a' < alloc_ceiling).
    { intros a' (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP6 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    split; [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB6 a HC); lia| lia]|]. split; [lia| exact I].
Qed.

End WithCeiling0.
