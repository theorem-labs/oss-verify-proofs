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
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac pre_ok l ::= lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let b := eval vm_compute in (andb (andb (Z.leb 736088 n) (Z.ltb n 737124)) (negb (existsb (Z.eqb n) l))) in
  lazymatch b with true => idtac end end.

Section AtkmLoop.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Definition atkm_nfx (q out : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
      ms = MS (mkR (wz 0xb3cec) (wz (q + -128)) gp (wz TPV) t0 t1 t2 s0 (wz (out + 16)) (wz out) (wz 0) (wz 16) a3 a4 a5 a6 a7
                   s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz e_asan_memset) fc None m (seg_rom asegs).

  Lemma atkm_nf : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 ->
    evt asegs (atkm_nfx q out gp F fc m)
               (MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz 0xb3cd8) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold atkm_frame, atkm_saved in FR. cbn [app] in FR.
    run. apply evt_done. unfold atkm_nfx, e_asan_memset. do 22 eexists. reflexivity.
  Qed.

  Definition atkm_headx (q out P RA it e L c : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms =>
      (exists (j' l : Z) (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
         str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) l /\ l <> L /\
         rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         stk asegs m (ae_lo E) (q + -128) /\ mem_inv asegs m /\ ae_lo E <= q + -128 /\ AINV_A E m /\
         shz m (ae_TAPE E) (8 * ae_n E) /\ elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' /\ 0 <= it /\ it + 1 < j' /\
         j' <= e /\ e + 1 <= ae_n E - 1 /\ shz m (ae_SBUF E) (ae_NS E) /\ 0 <= L < 2^40 /\
         tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) j' e (c - 1) /\
         ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (wz it) (wz 67240448) (wz 2147450880) (wz (8 * it)) (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                 F (wz 0xb3e0c) fc None m (seg_rom asegs))
      \/
      (exists (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
         str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) L /\
         ms = MS (mkR (wz 0xb3e08) (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L)
                     (wz P) (wz (ae_SBUF E + tval (ae_T E it) + 4)) (wz L) xa3 xa4 xa5 xa6 xa7
                      (wz it) (wz 67240448) (wz 2147450880) (wz (8 * it)) (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                 F (wz e_memcmp) fc None m (seg_rom asegs)).

  Lemma atkm_head : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA it e L c : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 -> AINV_A E m ->
    shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
    is_str (ae_T E) (ae_S E) (ae_sn E) it -> 0 <= it -> it + 1 <= e -> e + 1 <= ae_n E - 1 -> 0 <= L < 2^40 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c ->
    evt asegs (atkm_headx q out P RA it e L c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
               (MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (wz it) (wz 67240448) (wz 2147450880) xs5 (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                   F (wz 0xb3d80) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO AI SHZT SHZS STR I0 IE EN LR TIL.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] (SB16 & NS8 & SN & SS & SL) PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof FR as FR0. unfold atkm_frame, atkm_saved in FR. cbn [app] in FR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (key_word_rangeM _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0' & OL & LE & O56).
    pose proof AI as (TAPEB & SBUFB & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (tval (ae_T E it)) SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (tval (ae_T E it) + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (tval (ae_T E it) + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (tval (ae_T E it) + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byteM E OK (tval (ae_T E it)) ltac:(lia)) as Y0. pose proof (sbs_byteM E OK (tval (ae_T E it) + 1) ltac:(lia)) as Y1.
    pose proof (sbs_byteM E OK (tval (ae_T E it) + 2) ltac:(lia)) as Y2. pose proof (sbs_byteM E OK (tval (ae_T E it) + 3) ltac:(lia)) as Y3.
    set (ti := tval (ae_T E it)) in *. assert (TI : ti = tval (ae_T E it)) by reflexivity. clearbody ti.
    let v := eval vm_compute in (2^56) in assert (TV : ae_T E it mod v = ti) by (rewrite TI; reflexivity).
    repeat (first [ (shz_at SHZT (ae_TAPE E + 8 * it)) | (shz_at SHZS (ae_SBUF E + ti)) | (shz_at SHZS (ae_SBUF E + ti + 3))
                  | (rewrite KM) | (rewrite shl8_shr8_tvalM by lia; rewrite <- TI) | (rewrite shl_mod_smallM by lia)
                  | (rewrite land64_shl_smallM by lia) | (rewrite TV)
                  | (rewrite le32_of_lbu4M by lia;
                     change (ae_S E ti + 2 ^ 8 * ae_S E (ti + 1) + 2 ^ 16 * ae_S E (ti + 2) + 2 ^ 24 * ae_S E (ti + 3))
                       with (le32 (ae_S E) ti); rewrite LE) ]; runl [736780]).
    destruct (Z.eq_dec l L) as [EQL|NEL].
    { assert (CND : negb (bv_eqb (Z_to_bv 64 L) (Z_to_bv 64 l)) = false)
        by (rewrite EQL; change (negb (bv_unsigned (Z_to_bv 64 L) =? bv_unsigned (Z_to_bv 64 L)) = false); rewrite Z.eqb_refl; reflexivity).
      rewrite CND. cbv_concl_iota. run.
      clear TV KM. subst ti. apply evt_done. unfold atkm_headx. right.
      do 12 eexists. split; [rewrite <- EQL; exact SA|]. atp_st_eq. }
    assert (CND : negb (bv_eqb (Z_to_bv 64 L) (Z_to_bv 64 l)) = true).
    { change (negb (bv_unsigned (Z_to_bv 64 L) =? bv_unsigned (Z_to_bv 64 l)) = true).
      rewrite !a_u64_small by lia. apply (proj2 (Bool.negb_true_iff _)). apply Z.eqb_neq. lia. }
    rewrite CND. cbv_concl_iota.
    destruct (object_iter _ _ _ _ (fun c0 cv H => H) HSN d it e c TIL ltac:(lia) ltac:(lia) ltac:(lia)) as (j' & _ & EL & IJ & _ & TI').
    clear TV KM. subst ti. apply evt_done. unfold atkm_headx. left.
    exists j', l. do 16 eexists.
    split; [exact SA|]. split; [exact NEL|]. split; [exact FR0|].
    split; [exact ST|]. split; [exact MI|]. split; [exact LO|]. split; [exact AI|].
    split; [exact SHZT|]. split; [exact EL|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact SHZS|]. split; [lia|]. split; [exact TI'|].
    atp_st_eq.
  Qed.

  Definition atkm_advx (q out P RA it j' e L c : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms =>
      (j' = e /\
       exists (x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
         rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         stk asegs m (ae_lo E) (q + -128) /\ mem_inv asegs m /\ ae_lo E <= q + -128 /\
         ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      xs2 xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                 F (wz 0xb3cd8) fc None m (seg_rom asegs))
      \/
      (j' <> e /\ 0 <= e - j' < e - it /\
       exists (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 x28 x29 x30 x31 : word),
         rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         stk asegs m (ae_lo E) (q + -128) /\ mem_inv asegs m /\ ae_lo E <= q + -128 /\ AINV_A E m /\
         shz m (ae_TAPE E) (8 * ae_n E) /\ shz m (ae_SBUF E) (ae_NS E) /\
         is_str (ae_T E) (ae_S E) (ae_sn E) j' /\ 0 <= j' /\ j' + 1 <= e /\ e + 1 <= ae_n E - 1 /\ 0 <= L < 2^40 /\
         tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) j' e c /\
         ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (wz j') (wz 67240448) (wz 2147450880) xs5 (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                 F (wz 0xb3d80) fc None m (seg_rom asegs)).

  Lemma atkm_adv : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA it j' e L c : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 -> AINV_A E m ->
    shz m (ae_TAPE E) (8 * ae_n E) -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' -> j' <= e -> e + 1 <= ae_n E - 1 ->
    shz m (ae_SBUF E) (ae_NS E) -> 0 <= L < 2^40 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) j' e c ->
    evt asegs (atkm_advx q out P RA it j' e L c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
               (MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (wz it) (wz 67240448) (wz 2147450880) (wz (8 * it)) (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                   F (wz 0xb3e0c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO AI SHZT EL I0 IJ JE EN SHZS L40 TI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    pose proof AI as (TAPEB & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB ltac:(lia)) as RDT.
    unfold atkm_frame, atkm_saved in FR. cbn [app] in FR.
    unfold USTACK_TOP in HT. replace (ae_TAPE E + 8 * (it + 1)) with (ae_TAPE E + 8 + 8 * it) in RDT by lia.
    astep. chk0 SHZT (ae_TAPE E + 8 + 8 * it). run.
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    1: (unfold t_true, t_false, t_null in TY; destruct TY as [TY|[TY|TY]]; rewrite TY; run; replace (it + 2) with j' by lia).
    4: (unfold t_i64, t_u64, t_dbl in TY; destruct TY as [TY|[TY|TY]]; rewrite TY; run; replace (it + 3) with j' by lia).
    7: (unfold t_str in TY; rewrite TY; run; replace (it + 2) with j' by lia).
    8: (unfold t_arr in TY; rewrite TY; run; rewrite land32_tnext by lia; rewrite NXT, <- Ej).
    9: (unfold t_obj in TY; rewrite TY; run; rewrite land32_tnext by lia; rewrite NXT, <- Ej).
    all: (astep; if_cases K; zify_cond K; runl [0xb3cd8; 0xb3d80]).
    all: first
      [ apply evt_done; left; split; [rewrite ?land64_mod in K; lia|];
        do 27 eexists; split; [unfold atkm_frame, atkm_saved; cbn [app]; exact FR|];
        split; [exact ST|]; split; [exact MI|]; split; [exact LO| reflexivity]
      | apply evt_done; right;
        assert (NE : j' <> e) by (rewrite ?land64_mod in K; lia);
        split; [exact NE|]; split; [lia|];
        destruct (object_iter (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c0 cv H => H) HSN d j' e c TI NE ltac:(lia) ltac:(lia))
          as (j2 & STR2 & EL2 & IJ3 & AFT2 & TI2);
        do 17 eexists; split; [unfold atkm_frame, atkm_saved; cbn [app]; exact FR|];
        split; [exact ST|]; split; [exact MI|]; split; [exact LO|]; split; [exact AI|];
        split; [exact SHZT|]; split; [exact SHZS|]; split; [exact STR2|];
        split; [lia|]; split; [lia|]; split; [lia|]; split; [exact L40|]; split; [exact TI| reflexivity] ].
  Qed.

  Definition atkm_cmpx (q out P RA it e L c : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (oa ob oc od : list byte) : machine_state -> Prop :=
    fun ms =>
      (r = wz 0 /\
       exists (j' : Z) (x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
         is_str (ae_T E) (ae_S E) (ae_sn E) it /\ elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' /\ it + 1 < j' /\ j' <= e /\
         rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         stk asegs m (ae_lo E) (q + -128) /\ mem_inv asegs m /\ ae_lo E <= q + -128 /\
         rw_cells asegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] /\ q <= out /\ out + 24 <= ae_hi E /\ out mod 8 = 0 /\
         shz m out 24 /\ 0 <= RA < 2^64 /\ 0 <= it /\ it + 1 < 2^63 /\
         ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (wz it) xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                 F (wz 0xb3e8c) fc None m (seg_rom asegs))
      \/
      (r <> wz 0 /\
       exists (j' : Z) (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
         rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         stk asegs m (ae_lo E) (q + -128) /\ mem_inv asegs m /\ ae_lo E <= q + -128 /\ AINV_A E m /\
         shz m (ae_TAPE E) (8 * ae_n E) /\ elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' /\ 0 <= it /\ it + 1 < j' /\
         j' <= e /\ e + 1 <= ae_n E - 1 /\ shz m (ae_SBUF E) (ae_NS E) /\ 0 <= L < 2^40 /\
         tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) j' e (c - 1) /\
         ms = MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (wz it) (wz 67240448) (wz 2147450880) (wz (8 * it)) (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                 F (wz 0xb3e0c) fc None m (seg_rom asegs)).

  Lemma atkm_cmpret : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA it e L c : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r : word)
      (x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word) (oa ob oc od : list byte),
    rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 -> AINV_A E m ->
    shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
    is_str (ae_T E) (ae_S E) (ae_sn E) it -> 0 <= it -> it + 1 <= e -> e + 1 <= ae_n E - 1 -> 0 <= L < 2^40 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c ->
    rw_cells asegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> 0 <= RA < 2^64 ->
    evt asegs (atkm_cmpx q out P RA it e L c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r F fc m oa ob oc od)
               (MS (mkR (wz 0xb3e08) (wz (q + -128)) gp (wz TPV) x5 x6 x7 (wz 4294967297) (wz L) r xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (wz it) (wz 67240448) (wz 2147450880) (wz (8 * it)) (wz (ae_TAPE E)) (wz e) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz 32) (wz 4294967295) x28 x29 x30 x31)
                   F (wz 0xb3e08) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until od. intros FR ST MI LO AI SHT SHS ISS IT0 IE EN LB TI OUT QO OB O8 SHZO RA0.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ [_ [_ [NT [TP0 TPL]]]] _ _ _ _ _ [HL HT]]. unfold USTACK_TOP in HT.
    destruct (tiles_next _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI ltac:(lia)) as (j' & [HS HEL] & JE & TI').
    pose proof (elem_lt _ _ _ _ _ _ _ HEL) as IJ.
    step. if_cases K; zify_cond K.
    - assert (R0 : r = wz 0) by (apply bv_eq; rewrite K; reflexivity).
      apply evt_done. left. split; [exact R0|]. exists j'. do 26 eexists.
      split; [exact ISS|]. split; [exact HEL|]. split; [lia|]. split; [lia|].
      split; [exact FR|]. split; [exact ST|]. split; [exact MI|]. split; [exact LO|].
      split; [exact OUT|]. split; [exact QO|]. split; [exact OB|]. split; [exact O8|].
      split; [exact SHZO|]. split; [exact RA0|]. split; [exact IT0|]. split; [lia|].
      reflexivity.
    - apply evt_done. right. split; [intro R0; rewrite R0 in K; apply K; reflexivity|]. exists j'. do 16 eexists.
      split; [exact FR|]. split; [exact ST|]. split; [exact MI|]. split; [exact LO|]. split; [exact AI|].
      split; [exact SHT|]. split; [exact HEL|]. split; [exact IT0|]. split; [lia|]. split; [lia|].
      split; [exact EN|]. split; [exact SHS|]. split; [exact LB|]. split; [exact TI'|].
      reflexivity.
  Qed.

End AtkmLoop.
