From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objkA El_callsA El_atkmdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac pre_ok l ::= lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let b := eval vm_compute in (andb (andb (Z.leb 737124 n) (Z.ltb n 738160)) (negb (existsb (Z.eqb n) l))) in
  lazymatch b with true => idtac end end.
Notation wz z := (Z_to_bv 64 z) (only parsing).


Section AtKcEntry.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Definition atkc_x1 (i q out P RA L : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (jo : list byte) : machine_state -> Prop :=
    fun ms => exists (m1 : mem),
      munch (atkm_W q) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 (ae_lo E) (q + -128) /\ ae_lo E <= q + -128 /\
      AINV_A E m1 /\ rw_cells asegs m1 out [CB 24 jo] /\
      ( (exists (j0 j1 : list byte) (t0 t1 t2 y8 a3 a4 a5 a6 a7 y18 y19 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 : word),
           ttype (ae_T E i) <> 123 /\
           rw_cells asegs m1 (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
           ms = MS (mkR (wz 0xb409c) (wz (q + -128)) gp (wz TPV) t0 t1 t2 y8 (wz (out + 16)) (wz out) (wz 0) (wz 16) a3 a4 a5 a6 a7
                        y18 y19 (wz 2147450880) y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
                   F (wz e_asan_memset) fc None m1 (seg_rom asegs))
     \/ (rw_cells asegs m1 (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         exists (x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
           ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xs2 xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz 0xb40e4) fc None m1 (seg_rom asegs))
     \/ (rw_cells asegs m1 (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         shz m1 (ae_TAPE E) (8 * ae_n E) /\ shz m1 (ae_SBUF E) (ae_NS E) /\
         exists (d' : nat) (e c : Z) (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 x28 x29 x30 x31 : word),
           d = S d' /\ tnext (ae_T E i) = e + 1 /\ is_str (ae_T E) (ae_S E) (ae_sn E) (i + 1) /\ 0 <= i + 1 /\ i + 2 <= e /\
           e + 1 <= ae_n E - 1 /\ 0 <= L < 2^40 /\
           tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d')) (i + 1) e c /\
           ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        (wz (i + 1)) (wz 67240448) (wz 2147450880) xs5 (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E))
                        (wz 32) (wz 4294967295) x28 x29 x30 x31)
                   F (wz 0xb418c) fc None m1 (seg_rom asegs)) ).

  Lemma atkc_walk1 : forall (i j q out node P L RA : Z)
      (gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 -> AINV_A E m ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz i)] -> 0 < node -> node + 16 <= ae_hi E -> (q <= node \/ node + 16 <= q + -128) ->
    rw_cells asegs m out [CB 24 jo] -> q <= out ->
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 128 <= q -> q mod 16 = 0 -> shb_cells m ->
    0 <= L < 2^40 -> 0 <= RA < 2^64 ->
    (forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' (ae_SBUF E) (ae_NS E)) ->
    evt asegs (atkc_x1 i q out P RA L gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (lvl_entry ATKCI_FN_A (wz RA) q gp t0 t1 t2 s0 s1 out node P L a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until jo. intros EL I0 JN AI NODE N0 NB NQ OUT QO MI ST LO Q16 [G1 G2] LR RAR SHZN SHZT SHZS.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] (SB16 & NS8 & SN & SS & SL) PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold lvl_entry, ATKCI_FN_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    assert (SHZD : forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU' WM'. apply (shz_doc E m' OK). apply (AINV_A_munch E _ m m' OK AI MU'). unfold atkm_W. constructor; [cbn; lia| constructor]. }
    pose proof (munch_refl (atkm_W q) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold atkm_W in MU.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E i) < 256) by (unfold ttype; lia).
    hide AI.
    step. carve_frame 128%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 128 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    run.
    name_mem m1.
    assert (AI1 : AINV_A E m1) by (unhide AI; apply (AINV_A_munch E _ m m1 OK AI MU); constructor; [cbn; lia| constructor]).
    pose proof AI1 as (TAPEB1 & SBUFB1 & _ & DOCC1 & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia)) as RDT1.
    pose proof (tape_read_typeM m1 (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia) TIR) as RDB1.
    clear AI1.
    repeat (first [ shz_at SHZN node | shz_at SHZN (node + 8) | shz_at SHZD (ae_DOC E) | shz_at SHZT (ae_TAPE E + 8 * i) ]; run).
    lazymatch goal with |- evt asegs ?Q ?S => assert (EX1 : ttype (ae_T E i) <> 123 -> evt asegs Q S) end.
    { intros N123. if_dead2 by N123 TTR. run.
      apply evt_done. exists m1.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      split; [unhide AI; apply (AINV_A_munch E _ m m1 OK AI MU); constructor; [cbn; lia| constructor]|].
      split; [first [assumption | eapply rw_cells_transport; [exact OUT | exact MU | exact WM | cbn; lia]]|].
      left. do 24 eexists. split; [exact N123|]. split.
      { cbn [atkm_saved app]. eassumption. }
      unfold e_asan_memset; atp_st_eq_goal. }
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d i j EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e c Ed TY Ej NXT CLOSE TILES|d' e c Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    - apply EX1; destruct TY as [TY|[TY|TY]]; rewrite TY; discriminate.
    - apply EX1; destruct TY as [TY|[TY|TY]]; rewrite TY; discriminate.
    - apply EX1; rewrite TY; discriminate.
    - apply EX1; rewrite TY; discriminate.
    - clear EX1. unfold t_obj in TY. rewrite TY. if_false.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ TILES) as [IE CC].
    destruct (Z.eq_dec (i + 1) e) as [IE1|IE1].
    { repeat (first [ shz_at SHZN node | shz_at SHZN (node + 8) | rewrite TY | (rewrite zx32_tnextM by lia; rewrite NXT) | (rewrite land32_tnext by lia; rewrite NXT) | rewrite NXT | progress change (123 + -91) with 32 ]; run).
      if_false.
      repeat (first [ shz_at SHZN node | shz_at SHZN (node + 8) | rewrite TY | (rewrite zx32_tnextM by lia; rewrite NXT) | (rewrite land32_tnext by lia; rewrite NXT) | rewrite NXT | (rewrite mod32_tnext, NXT) ]; run).
      if_dead1 by IE1.
      runl [737508].
      repeat (pre_ok [737508]; first [ shz_at SHZN node | shz_at SHZN (node + 8) | shz_at SHZD (ae_DOC E + 8) ]; runl [737508]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => apply evt_done; exists mm end.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      split; [unhide AI; apply (AINV_A_munch E _ m _ OK AI MU); constructor; [cbn; lia| constructor]|].
      split; [first [assumption | eapply rw_cells_transport; [exact OUT | exact MU | exact WM | cbn; lia]]|].
      right; left. split.
      { unfold atkm_frame, atkm_saved; cbn [app]. eassumption. }
      do 27 eexists. atp_st_eq_goal. }
    repeat (first [ shz_at SHZN node | shz_at SHZN (node + 8) | rewrite TY | (rewrite zx32_tnextM by lia; rewrite NXT) | (rewrite land32_tnext by lia; rewrite NXT) | rewrite NXT | shz_at SHZD (ae_DOC E + 8) | progress change (123 + -91) with 32 ]; runl [737676]).
    if_false.
    repeat (first [ shz_at SHZN node | shz_at SHZN (node + 8) | rewrite TY | (rewrite zx32_tnextM by lia; rewrite NXT) | (rewrite land32_tnext by lia; rewrite NXT) | rewrite NXT | (rewrite mod32_tnext, NXT) | shz_at SHZD (ae_DOC E + 8) ]; runl [737676]).
    assert (EB : 0 <= e + 1 < 2^32) by (rewrite <- NXT; unfold tnext; apply Z.mod_pos_bound; lia).
    if_dead2 by IE1 I0 IE EB.
    runl [737676].
    repeat (pre_ok [737676]; first [ shz_at SHZN node | shz_at SHZN (node + 8) | shz_at SHZD (ae_DOC E + 8) ]; runl [737676]).
    destruct (object_iter _ _ _ _ (fun c0 cv H => H) HSN d' (i + 1) e c TILES IE1 ltac:(lia) ltac:(lia)) as (j' & STR & _ & JR & _ & _).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => apply evt_done; exists mm end.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    split; [unhide AI; apply (AINV_A_munch E _ m _ OK AI MU); constructor; [cbn; lia| constructor]|].
    split; [first [assumption | eapply rw_cells_transport; [exact OUT | exact MU | exact WM | cbn; lia]]|].
    right; right. split.
    { unfold atkm_frame, atkm_saved; cbn [app]. eassumption. }
    split; [apply SHZT; [exact MU| exact WM]|].
    split; [apply SHZS; [exact MU| exact WM]|].
    exists d', e, c. do 17 eexists.
    split; [exact Ed|]. split; [exact NXT|]. split; [exact STR|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact TILES|].
    atp_st_eq_goal.
  Qed.

End AtKcEntry.
