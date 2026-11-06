(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pobject_L3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pobject_L1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pobject_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L3.CJ_pstring_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L1.CJ_pobject_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L1.CJ_pobject_ws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L3.CJ_pobject_L2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma po_bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; [cbn; lia|]. cbn [bytes_le_to_Z].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range| apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma po_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2^8) in Hb.
  pose proof (po_bytes_le_to_Z_nonneg bs) as H0.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned.
    lazymatch goal with |- bv_wrap 8 ?x = _ => change (bv_wrap 8 x) with (x mod 2^8) end.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_mod_mult, Z.lor_0_r. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by lia. rewrite Z.lor_0_l. exact IH.
Qed.

Lemma po_bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (po_bytes_le_to_Z_nonneg bs)) as E.
  rewrite po_Z_to_le_bytes_to_Z in E. rewrite E at 1. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma le8_of_bytes8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (po_bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in B.
  pose proof (po_bytes_le_to_Z_nonneg bs).
  rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). rewrite <- L. apply po_Z_to_le_bytes_to_Z.
Qed.

Section POE.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (POBJ_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis SDEL : Forall (STAT TI) S_DELETE.
  Hypothesis SCONST : Forall (STAT TI) S_PARSE_CONST.
  Hypothesis SPV : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis LFR : lf_room 2 LF (1000 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.
  Hypothesis MEMSET : asan_memset_spec.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B [] U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO AI TI sp m g sp0 SPB LR LF np P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation OFR := (OFRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation dch := (dch depth).
  Notation OLOOPc := (OLOOP AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LR LF np B U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation WSM := (ws_mem P CA blen bs).
  Notation NC := (18446744073709551615 - CA).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & HDn & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold POBJ_STACK, PARSE_STACK in LO.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold CSTO, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  (* [comment removed for export] *)
  Ltac blia := unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  (* [comment removed for export] *)
  Ltac ugd := let G := fresh "G" in zstep;
  first [ if_cases G; zify_cond G; [ solve [exfalso; lia] | ]
        | if_cases G; zify_cond G; [ | solve [exfalso; lia] ]
        | if_cases G; zify_cond G; try (exfalso; lia) ].   (* [comment removed for export] *)
  Notation FAILO24 := (fail_o24 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation OBJCLOSE := (obj_close AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation PRES_FRAME := (pres_frame sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PBUF := (pres_pbuf sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_TEXT := (pres_text sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PSH := (pres_pbuf_sh sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).

  Notation RET0O := (ret0_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation RET0E := (ret0_epi_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation OBJEMPTY := (obj_empty AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation OLOOPT := (oloop AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL SCONST SPV LFR nfuel FUEL PVREC MEMSET).
  Ltac xor1 c s := replace (Z.lxor (Z.b2z (0 <? c)) (Z.b2z (s <? 1))) with 1
      by (rewrite (proj2 (Z.ltb_lt 0 c) ltac:(lia)); rewrite (proj2 (Z.ltb_ge s 1) ltac:(lia)); reflexivity).

  Theorem po_body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (TRS : list (list Z)) (errv : word),
    ART AI sp0 SPB LB LF TRS B m mo g -> TINV TI np TRS ->
    bytes_at bsegs m CA bs -> rw_cells bsegs m AERRNO [C4 errv] -> mem_inv bsegs m ->
    stk bsegs m lo SP -> pbuf_sh m P ->
    rw_cells bsegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    frm0 fc -> a0 = wz U -> a1 = wz P ->
    LSCPS bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (wz PARSE_OBJECT) fc None m (seg_rom bsegs)) mo g.
  Proof.
    intros until errv. intros HL TV BY ERR MI ST PSH ND PB FRM A0 A1. lits. bandM. sepM.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_OBJECT, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL PLF) as BHA.
    pose proof (ppres_refl sp0 LR LF SP P m) as PR0. pose proof (gmono_refl g) as GM0.
    eapply lscps_step_evt.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -144, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof SB as SB0. shbase_split SB0.
    zstep. carve_frame 144%nat ST. do 13 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HL1 : ART AI sp0 SPB LB LF TRS B m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (PR1 : ppres sp0 LR LF SP P m m1) by (eapply (ppres_frame_store AI); [exact HL| exact INLR| exact MU| exact WM| alia| lia| exact SP5]).
    assert (PSH1 : pbuf_sh m1 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (TS1 : text_sh m1 CA blen) by (eapply text_sh_high_store; [exact TS| exact MU| alia| lia| alia]).
    clear MU WM HL PSH TS PR0.
    Ltac mid HLx BYx ERRx MIx STx PRx TVx PSHx :=
      split; [exact HLx|]; split; [exact BYx|]; split; [unfold AERRNO, ATP; exact ERRx|]; split; [exact MIx|];
      split; [exact STx|]; split; [exact PRx|]; split; [apply gmono_refl|]; split; [exact TVx| exact PSHx].
    (* [comment removed for export] *)
    zstep. zstep. land7 P. ugd. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH1 ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
    zstep. zstep. zstep. if_cases Kd; zify_cond Kd.
    { apply evt_done. eapply (RET0O _ off depth m1 mo g LB TRS B errv); [mid HL1 BY ERR MI ST PR1 TV PSH1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH1 ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LB LF TRS B m2 mo g) by (eapply (art_pbuf_store AI); [exact HL1| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR1|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH1| exact MU| alia| alia| alia]).
    assert (TS2 : text_sh m2 CA blen) by (eapply text_sh_high_store; [exact TS1| exact MU| alia| lia| alia]).
    clear MU WM HL1 PR1 PSH1 TS1.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 8) PSH2 ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done. eapply (RET0O _ off (depth + 1) m2 mo g LB TRS B errv); [mid HL2 BY ERR MI ST PR2 TV PSH2| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -112, SP + -104)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2f end.
    assert (HL2f : ART AI sp0 SPB LB LF TRS B m2f mo g) by (eapply (art_frame_store AI); [exact HL2| exact MU| exact WM| alia| alia]).
    assert (PR2f : ppres sp0 LR LF SP P m m2f).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_frame_store AI); [exact HL2| exact INLR| exact MU| exact WM| alia| lia| exact SP5]. }
    assert (PSH2f : pbuf_sh m2f P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (TS2f : text_sh m2f CA blen) by (eapply text_sh_high_store; [exact TS2| exact MU| alia| lia| alia]).
    clear MU WM HL2 PR2 PSH2 TS2. rename m2f into m2'. rename HL2f into HL2. rename PR2f into PR2. rename PSH2f into PSH2. rename TS2f into TS2.
    pose proof (sh_zero_shb m2' P (P + 56) P PSH2 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. replace (off + CA) with (CA + off) by lia.
    ugd. zstep. zstep. zstep. xor1 CA (CA + off). ugd. ugd.
    zstep. zstep.
    (nelim (text_read m2' CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    pose proof (TS2 (CA + off) ltac:(lia)) as CK. asan_chk CK.
    zstep. zstep. zstep. if_cases K123; zify_cond K123.
    { apply evt_done.
      apply (rw_cells_merge bsegs m2' _ [] [CB 32 _; C8 _]) in FR. cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
      eapply (RET0O _ off (depth + 1) m2' mo g LB TRS B errv); [mid HL2 BY ERR MI ST PR2 TV PSH2| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2') as MU. pose proof (wmono_refl bsegs m2') as WM.
    pose proof (sh_zero_shb m2' P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (TS3 : text_sh m3 CA blen) by (eapply text_sh_high_store; [exact TS2| exact MU| alia| lia| alia]).
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (BLK : forall A' k, In (A', k) LB -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I]. destruct (BHA A' k Hin). lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall x5' x7' x10' x14' x15' x16' x17' m4,
      rw_cells bsegs m4 P (pbuf_cells CA blen (skipws_off bs (off + 1)) (depth + 1)) -> bytes_at bsegs m4 CA bs -> mem_inv bsegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono bsegs m3 m4 ->
      evt bsegs (fun ms' => LSCPS bsegs POST ms' mo g)
        (CST 0x85cb4 ra x5' (Z_to_bv 64 U) x7' (Z_to_bv 64 (P + 16)) s1 x10' (Z_to_bv 64 depth) (Z_to_bv 64 blen) (Z_to_bv 64 CA) x14' x15' x16' x17'
             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) s5 (Z_to_bv 64 (Z.shiftr (P + 8) 3 + 2147450880)) s7 s8
             (Z_to_bv 64 (Z.shiftr (P + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) t3 t4 t5 t6 F fc m4)).
    { intros x5' x7' x10' x14' x15' x16' x17' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO. cbv beta delta [mkR].
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : ART AI sp0 SPB LB LF TRS B m4 mo g) by (eapply (art_pbuf_store AI); [exact HL2| exact PLF| exact MU24| exact WM24| lia| lia]).
      assert (PR4 : ppres sp0 LR LF SP P m m4).
      { eapply ppres_trans; [exact PR2|]. eapply ppres_pbuf_store; [exact MU24| exact WM24| lia| lia]. }
      assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU24| alia| alia| alia]).
      assert (TS4 : text_sh m4 CA blen) by (eapply text_sh_high_store; [exact TS2| exact MU24| alia| lia| alia]).
      clear MU4 WM4 MU24 WM24.
      assert (O2 : off + 1 <= skipws_off bs (off + 1) <= blen).
      { destruct (Z.eq_dec (off + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (off + 1)) as OR. rewrite LEN in OR. lia. }
      set (o2 := skipws_off bs (off + 1)) in *.
      pose proof (rw_cells_bound bsegs _ _ _ PB4) as PBB4. rewrite pbuf_cells_size in PBB4. unfold pbuf_cells, wz in PB4.
      (* [comment removed for export] *)
      pose proof (sh_zero_shb m4 P (P + 56) (P + 16) PSH4 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep. if_cases Kend2; zify_cond Kend2.
      { (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24)] m4) as MU5. pose proof (wmono_refl bsegs m4) as WM5.
        pose proof (sh_zero_shb m4 P (P + 56) (P + 16) PSH4 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. apply evt_done.
        apply (rw_cells_merge bsegs m5 _ [] [CB 32 _; C8 _]) in FR4. cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR4.
        eapply lscps_eq; [| eapply (RET0E _ (o2 - 1) (depth + 1) m5 mo g LB TRS B errv);
          [| exact HPU| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM| clear -BPRE OFF; blia]].
        { unfold CSTO, mkR. rewrite (zxb_zb 0) by lia. steq. }
        split. { eapply (art_pbuf_store AI); [exact HL4| exact PLF| exact MU5| exact WM5| lia| lia]. }
        split; [exact BY4|]. split; [unfold AERRNO, ATP; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        split. { eapply ppres_trans; [exact PR4|]. eapply ppres_pbuf_store; [exact MU5| exact WM5| lia| lia]. }
        split; [apply gmono_refl|]. split; [exact TV|]. eapply pbuf_sh_high_store; [exact PSH4| exact MU5| alia| alia| alia]. }
      (* [comment removed for export] *)
      zstep. rewrite zb_lxor_ones by lia. ugd.
      zstep. zstep. zstep.
      (nelim (text_read m4 CA bs o2 (Z_to_bv 64 (CA + o2)) BY4 ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros c2 Hc2 RD2 _).
      pose proof (byte_range c2) as Rc2.
      pose proof (TS4 (CA + o2) ltac:(lia)) as CK2. asan_chk CK2.
      zstep. zstep. zstep. if_cases K125; zify_cond K125.
      - (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24); (SP + -144, SP + -120)] m4) as MU5. pose proof (wmono_refl bsegs m4) as WM5.
        pose proof (sh_zero_shb m4 P (P + 56) (P + 16) PSH4 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. fix_lit_store. zstep. zstep. zstep. fix_lit_store. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        apply evt_done.
        (* [comment removed for export] *)
        lazymatch goal with H : rw_cells bsegs m5 (SP + -144) ?cs |- _ =>
          lazymatch cs with context [CB 8 ?jj] =>
            let WF := fresh "WF" in
            pose proof (proj1 (proj1 H)) as WF; cbn [cells_wf cell_wf] in WF;
            let LJ := fresh "LJ" in (nelim WF 5%nat; intros _ _ _ LJ _);
            eapply (rw_cells_recell m5 _ cs (OFRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P (le_bytes_to_word jj))) in H;
              [| cbn; repeat split; exact I
               | unfold OFRAME, SAVEDO, SHR; cbn [cells_bytes cbytes app]; rewrite (le8_of_bytes8 jj LJ); zfeq]
          end end.
        pose proof OLOOPT as OL. unfold OLOOP, CSTO, SHR in OL.
        eapply lscps_eq; [| eapply (OL (Z.to_nat (blen - (o2 - 1))) (o2 - 1) 0 0 [] m5 mo g LB TRS B errv);
          [lia| lia| lia| | exact HPU| left; split; reflexivity| | unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM
          | clear -O2; unfold PV_RATE; lia| clear -O2; cbn; lia]].
        { steq. }
        + split. { eapply (art_frame AI); [exact HL4| exact MU5| exact WM5|]. constructor; [| constructor; [| constructor]].
                   - do 8 right. left. exists (P - 32), 1. cbn. split; [exact PLF| change (fsz 1) with 128; lia].
                   - right; left. cbn. alia. }
          split; [exact BY4|]. split; [unfold AERRNO, ATP; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
          split. { eapply ppres_trans; [exact PR4|]. eapply ppres_of_munch; [exact MU5| exact WM5|].
                   intros a Ha nelH_; (nelim nelH_ 3%nat; intros Hc _ Hp). cbn. destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
                   - lia.
                   - pose proof (aclient_image_lt a Hi). lia.
                   - destruct (BHA A' n' (INLR _ Hin)). (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL4 (INLR _ Hin)) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
                   - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL4 Hin) 5%nat; intros Hk _ HF1 HF2 _).
                     try rewrite alloc_ceiling_eq in HF2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM.
                     assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
                     unfold SH, SHADOW_OFFSET in Hr. Z.div_mod_to_equations. lia.
                   - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
          split; [apply gmono_refl|]. split; [exact TV|].
          eapply pbuf_sh_munch; [exact PSH4| exact MU5| lia| lia| pbuf_dj (* [comment removed for export] *)].
        + lazymatch goal with H : rw_cells bsegs m5 (SP + -144) (OFRAME _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => exact H end.
      - (* [comment removed for export] *)
        apply evt_done.
        eapply lscps_eq; [| eapply (OBJEMPTY _ _ o2 m4 mo g LB TRS B errv);
          [| exact HPU| exact FR4| unfold pbuf_at; eqcells PB4| lia| eqcells ND4| lia| apply Fagree_refl| exact FRM| clear -O2; unfold PV_RATE; lia]].
        { steq. }
        split; [exact HL4|]. split; [exact BY4|]. split; [unfold AERRNO, ATP; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        split; [exact PR4|]. split; [apply gmono_refl|]. split; [exact TV| exact PSH4]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz.
      lazymatch goal with H : rw_cells bsegs m3 P _ |- _ => exact H end.
    - zstep. rewrite zb_lxor_ones by lia. zstep.
      pose proof (fin_off0 P blen (off + 1) bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (ws1 sp gp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC m3 TS3 PSH3 (Z.to_nat (blen - (off + 1))) (off + 1) (depth + 1) m3);
          [lia| lia| unfold pbuf_cells, wz; lazymatch goal with H : rw_cells bsegs m3 P _ |- _ => exact H end| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 11%nat; intros x5' x10' x14' x17' m4 -> PB4 BY4 MI4 MU4 WM4). unfold CSTO, SHR. rewrite <- FO in PB4.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.
End POE.

(* [comment removed for export] *)
Theorem po_step : forall AI TI nfuel,
  cjson_delete_stmt AI TI -> asan_memset_spec ->
  (forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf) -> parse_object_at AI TI nfuel.
Proof.
  intros AI TI nfuel DEL MEMSET PVREC. unfold parse_object_at. intros until ky.
  intros PI ND PB OFF DEP FUEL LO AL FRM TP A0 A1 LFR SPV SALL BPRE.
  (nelimp PI 16%nat; intros HL HPU HD DCA CAD BY LEN BLEN ERR MI ST CEIL TV PLF PSH SPF).
  apply Forall_app in SALL. destruct SALL as [SCONST SDEL].
  eapply (po_body AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky);
    [ eapply pv_pure_intro; [exact PI| exact ND| exact OFF| exact DEP| exact LO| exact TP]
    | exact BPRE | exact DEL | exact SDEL | exact SCONST | exact SPV | exact LFR | exact FUEL | exact PVREC | exact MEMSET
    | exact HL | exact TV | exact BY | exact ERR | exact MI | exact ST | exact PSH | exact ND | exact PB | exact FRM | exact A0 | exact A1 ].
Qed.


End CeilWrap.
End CJ_pobject_E.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_A2.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_A2.CJ_pvalue_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pobject_L3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pobject_L3.CJ_pstring_C.
Import CJ_pobject_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PVS.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).
  Hypothesis FLA : flag_apart_stmt AI.
  Hypothesis STPV : forall b, STAT TI (pv_trace (bv_unsigned ra) CH b).
  Hypothesis STPO : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis STC : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
  Hypothesis LFR : lf_room 2 LF (1001 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VFRx := (VFR ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation MAGIC_EXIT := (magic_exit AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Hypothesis PO : parse_object_at AI TI nfuel.

  Lemma sconst_pstr : STAT TI PSTR_TR_MALLOC /\ STAT TI PSTR_TR_FREE /\ Forall (STAT TI) S_DELETE /\ Forall (STAT TI) S_PARSE_CONST.
  Proof.
    pose proof STC as SC. apply Forall_app in SC. destruct SC as [SC SD]. pose proof SC as SC0. unfold S_PARSE_CONST in SC.
    apply Forall_cons_iff in SC. destruct SC as [_ SC]. apply Forall_cons_iff in SC. destruct SC as [S2 SC]. apply Forall_cons_iff in SC. destruct SC as [S3 _].
    split; [exact S2|]. split; [exact S3|]. split; [exact SD| exact SC0].
  Qed.

  (* [comment removed for export] *)
  Lemma pinv_at_SA : forall SA Fr m1 mo1 g1 TRS1 B1 errv1,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B1 errv1 ->
    parse_inv AI TI m1 mo1 g1 sp0 SPB LB [] LR ((Fr, 2) :: LF) TRS1 np B1 U P CA blen bs D n lo SA errv1.
  Proof.
    intros SA Fr m1 mo1 g1 TRS1 B1 errv1 (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR) (HL & BY & ERR & MI & ST & PR & GM & TV & PSH & CC). lits. bandM. sepM.
    split; [exact HL|]. split; [exact HPU|]. split; [exact HD|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
    split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; lia|]. split; [exact TV|]. split; [right; exact PLF|]. split; [exact PSH|].
    repeat split; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma call_string : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h jae jn cs48 lj
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x27 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    VFRx SA Fr m1 shb h jae jn cs48 lj ->
    pbuf_at m1 P CA blen off depth -> rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off < blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS bsegs POST (VSTx SA Fr 0x82ff8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 P) x22 x24 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD VF PB ND Ho FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    (nelimp sconst_pstr 4%nat; intros S2 S3 SD SC0).
    pose proof (pinv_at_SA SA Fr m1 mo1 g1 TRS1 B errv1 GE MD) as PI.
    (nelimp VF 10%nat; intros _ _ _ _ _ _ _ L48 _ _). unfold LOCSV, SHV in L48.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep. change (Z_to_bv 64 545708) with (wz PARSE_STRING).
    apply evt_done. cbv beta. eapply lscps_bind.
    { pose proof (parse_string_spec AI TI) as PS. unfold parse_string_stmt in PS.
      sepM. eapply PS with (off := off) (depth := depth); clear PS; rewrite ?unsigned_lit by lia;
        first [ exact PI
              | exact ND
              | exact PB
              | exact TP
              | exact S2
              | exact S3
              | (lazymatch goal with |- @eq ?c10T _ _ => lazymatch c10T with Z => fail | nat => fail | N => fail | positive => fail | _ => idtac end end; reflexivity)
              | lia
              | alia
              | reflexivity
              | clear -BPRE Ho OFF; blia ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 31%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' m2 r off2 LB2 X TRS2 B2 errv2 -> -> PI2 PR2 GM2 PB2 Ho2 RES)
.
    rewrite ?unsigned_lit in PI2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x83004)) with (Z_to_bv 64 0x83004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI2 16%nat; intros HL2 HP2 _ _ _ BY2 _ _ ERR2 MI2 ST2 _ TV2 _ PSH2 _).
    pose proof (VFR_ppres ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC SA Fr m1 m2 shb h jae jn cs48 lj _ GE VF PR2 ltac:(lia)) as VF2.
    (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m2 shb h jae jn cs48 lj VF2 ltac:(lia)) 3%nat; intros locs FRL SZL).
    (nelim VF2 10%nat; intros SHC2 L32 HDR2 AE2 NC2 L02 S0 L162 STP2 SAVW2).
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_ext; [exact CC| exact CHOK|]. intros a Ha.
      destruct (PR2 a ltac:(lia)) as [E _]; [| exact E]. split; [left; lia|]. unfold AERRNO, ATP. lia. }
    unfold wz. eapply (MAGIC_EXIT 0x83004 SA Fr r m2 mo2 g2 LB2 TRS2 B2 errv2 Fx fcx shb h locs off2 depth);
      [cbn; tauto| exact GE| | exact SHC2| exact L32| exact HDR2| exact FRL| lia| exact SAVW2| exact FA| exact FRM| exact PB2|].
    - split; [exact HL2|]. split; [exact BY2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [eapply ppres_trans; [exact PR| eapply ppres_weaken; [exact PR2| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf]]|].
      split; [eapply gmono_trans; [exact GM| exact GM2]|]. split; [exact TV2|]. split; [exact PSH2| exact CC2].
    - exists X. split; [exact HP2|].
      destruct RES as [(-> & -> & ND2 & HB2)|(-> & S & k & -> & NZ & ND2 & STR & Hk & ->)].
      + left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND2| clear -HB2 BPRE Ho OFF; blia].
      + right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        pose proof (RT_cost.cost_malloc_lin k ltac:(lia)) as CM.
        split; [clear -CM Hk Ho2; unfold PV_RATE; lia|]. split; [cbn; lia|].
        exists 0, 16, S, vi, vd, 0%nat, [(S, k)], []. split; [reflexivity|]. split; [exact ND2|]. split; [cbn; auto 10|].
        split; [exact STR|]. split; [apply cj_chain_nil| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_or_fail : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h jae jn cs48 lj
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x27 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    VFRx SA Fr m1 shb h jae jn cs48 lj ->
    pbuf_at m1 P CA blen off depth -> rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off < blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS bsegs POST (VSTx SA Fr 0x8338c x1 x5 x6 x7 (Z_to_bv 64 (CA + off)) (SHV (CA + off)) x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 P) x22 x24 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD VF PB ND Ho FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    (nelimp sconst_pstr 4%nat; intros S2 S3 SD SC0).
    pose proof (pinv_at_SA SA Fr m1 mo1 g1 TRS1 B errv1 GE MD) as PI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL ltac:(eapply Permutation_in; [exact HPU| right; exact HD]) DCA CAD) as TSH.
    (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m1 shb h jae jn cs48 lj VF ltac:(lia)) 3%nat; intros locs FRL SZL).
    (nelimp VF 10%nat; intros SHC L32 HDR AE NC L0 S0 L48 STP SAVW). unfold LOCSV, SHV in L48.
    destruct (nth_error bs (Z.to_nat off)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read bsegs _ CA bs off b _ BY Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (TSH (CA + off) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. zstep. if_cases K123; zify_cond K123.
    { (* [comment removed for export] *)
      zstep. apply evt_done.
      eapply (MAGIC_EXIT 0x83808 SA Fr 0 m1 mo1 g1 LB TRS1 B errv1 Fx fcx shb h locs off depth);
        [cbn; tauto| exact GE| exact MD| exact SHC| exact L32| exact HDR| exact FRL| lia| exact SAVW| exact FA| exact FRM| exact PB|].
      exists []. split; [exact HPU|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    zstep. zstep. change (Z_to_bv 64 547640) with (wz PARSE_OBJECT).
    apply evt_done. cbv beta. eapply lscps_bind.
    { pose proof PO as POS. unfold parse_object_at in POS.
      sepM. eapply POS with (off := off) (depth := depth); clear POS; rewrite ?unsigned_lit by lia;
        first [ exact PI
              | exact ND
              | exact PB
              | exact FUEL
              | exact FRM
              | exact TP
              | exact STPO
              | exact STC
              | exact BPRE
              | (lazymatch goal with |- @eq ?c10T _ _ => lazymatch c10T with Z => fail | nat => fail | N => fail | positive => fail | _ => idtac end end; reflexivity)
              | lia
              | alia
              | reflexivity
              | unfold lf_room in *; cbn [lf_count]; rewrite Z.eqb_refl; lia ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 36%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F2 fc2 m2 r off2 depth2 LB2 X TRS2 B2 errv2 -> -> FA2 FRM2 PI2 PR2 GM2 _ PB2 RES)
.
    rewrite ?unsigned_lit in PI2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x833ac)) with (Z_to_bv 64 0x833ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI2 16%nat; intros HL2 HP2 _ _ _ BY2 _ _ ERR2 MI2 ST2 _ TV2 _ PSH2 _).
    pose proof (VFR_ppres ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC SA Fr m1 m2 shb h jae jn cs48 lj _ GE VF PR2 ltac:(lia)) as VF2.
    (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m2 shb h jae jn cs48 lj VF2 ltac:(lia)) 3%nat; intros locs2 FRL2 SZL2).
    (nelim VF2 10%nat; intros SHC2 _ HDR2 AE2 NC2 L02 _ L162 STP2 SAVW2).
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_ext; [exact CC| exact CHOK|]. intros a Ha.
      destruct (PR2 a ltac:(lia)) as [E _]; [| exact E]. split; [left; lia|]. unfold AERRNO, ATP. lia. }
    unfold wz. eapply (MAGIC_EXIT 0x833ac SA Fr r m2 mo2 g2 LB2 TRS2 B2 errv2 F2 fc2 shb h locs2 off2 depth2);
      [cbn; tauto| exact GE| | exact SHC2| exact L32| exact HDR2| exact FRL2| lia| exact SAVW2| eapply Fagree_trans; [exact FA| exact FA2]| exact FRM2| exact PB2|].
    - split; [exact HL2|]. split; [exact BY2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [eapply ppres_trans; [exact PR| eapply ppres_weaken; [exact PR2| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf]]|].
      split; [eapply gmono_trans; [exact GM| exact GM2]|]. split; [exact TV2|]. split; [exact PSH2| exact CC2].
    - exists X. split; [exact HP2|]. exact RES.
  Qed.
End PVS.


End CeilWrap.
