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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pobject_ctx.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas.
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
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
(* [comment removed for export] *)
Ltac land7 p := replace (Z.land p 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).

(* [comment removed for export] *)
Definition SHR (a : Z) : word := Z_to_bv 64 (Z.shiftr a 3 + 2147450880).

Section PO.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (POBJ_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  (* [comment removed for export] *)
  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis SDEL : Forall (STAT TI) S_DELETE.
  Hypothesis SCONST : Forall (STAT TI) S_PARSE_CONST.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B [] U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).

  (* [comment removed for export] *)
  Definition SAVEDO : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition CSTO (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
            (Z_to_bv 64 2147450880) x26 x27 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition MIDO (m1 : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 : Z) (errv1 : word) : Prop :=
    ART AI sp0 SPB LB1 LF TRS1 B1 m1 mo1 g1 /\ bytes_at bsegs m1 CA bs /\ rw_cells bsegs m1 AERRNO [C4 errv1]
    /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (SP + -144) /\ ppres sp0 LR LF SP P m m1 /\ gmono g g1 /\ TINV TI np TRS1 /\ pbuf_sh m1 P.

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & HDn & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold POBJ_STACK, PARSE_STACK in LO.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, AMALLOC_STACK; lia | sclr_tac ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold CSTO, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).

  (* [comment removed for export] *)
  Lemma epilogue_run_o : forall (junk : list byte) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Fx fcx mm,
    rw_cells bsegs mm (SP + -144) (CB 40 junk :: SAVEDO) ->
    evt bsegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom bsegs))
        (CSTO 0x861e0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. bandM. sepM. unfold CSTO, SAVEDO in *.
    do 15 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_o : forall (junk : list byte) (off1 depth1 : Z) m1 mo1 g1 LB1 TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LB1 TRS1 B1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells bsegs m1 (SP + -144) (CB 40 junk :: SAVEDO) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) <= B1 ->
    LSCPS bsegs POST (CSTO 0x861dc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP1 FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. eapply evt_cut; [apply (epilogue_run_o junk); exact FR|]. intros ms' ->.
    unfold SAVEDO in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply lscps_done. unfold parse_value_post.
    nexists 17%nat. exists m1, 0, off1, depth1, LB1, [], TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH|]. repeat split; try assumption; alia. }
    split; [exact PR|]. split; [exact GM|]. split; [exact I|]. split; [exact PB|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_epi_o : forall (junk : list byte) (off1 depth1 : Z) m1 mo1 g1 LB1 TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LB1 TRS1 B1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells bsegs m1 (SP + -144) (CB 40 junk :: SAVEDO) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) <= B1 ->
    LSCPS bsegs POST (CSTO 0x861e0 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP1 FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO.
    eapply lscps_step_evt. cbv beta delta [mkR].
    eapply evt_cut; [apply (epilogue_run_o junk); exact FR|]. intros ms' ->.
    unfold SAVEDO in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply lscps_done. unfold parse_value_post.
    nexists 17%nat. exists m1, 0, off1, depth1, LB1, [], TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH|]. repeat split; try assumption; alia. }
    split; [exact PR|]. split; [exact GM|]. split; [exact I|]. split; [exact PB|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma pres_frame : forall LBx m1 m2 cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    rw_cells bsegs m1 (SP + -144) cs -> Z.of_nat (cells_size cs) = 144 -> rw_cells bsegs m2 (SP + -144) cs.
  Proof. intros LBx m1 m2 cs PR2 FR Hsz. lits. bandM. sepM. eapply cj_pres_rw_cells; [exact PR2| exact FR|]. left. rewrite Hsz. lia. Qed.

  Lemma pres_pbuf : forall LBx m1 m2 c l o d, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    pbuf_at m1 P c l o d -> pbuf_at m2 P c l o d.
  Proof.
    intros LBx m1 m2 c l o d PR2 PB. lits. bandM. sepM. unfold pbuf_at in *. eapply cj_pres_rw_cells; [exact PR2| exact PB|].
    do 4 right. left. exists (P - 32), 1. split; [exact PLF|]. rewrite pbuf_cells_size. change (fsz 1) with 128. lia.
  Qed.

  Lemma pres_block : forall LBx m1 m2 A cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (A, 64) LBx ->
    rw_cells bsegs m1 A cs -> Z.of_nat (cells_size cs) = 64 -> rw_cells bsegs m2 A cs.
  Proof. intros LBx m1 m2 A cs PR2 HIn ND Hsz. eapply cj_pres_rw_cells; [exact PR2| exact ND|]. do 3 right. left. exists A, 64. rewrite Hsz. split; [exact HIn| lia]. Qed.

  Lemma pres_text : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (D, n) LBx ->
    bytes_at bsegs m1 CA bs -> bytes_at bsegs m2 CA bs.
  Proof. intros LBx m1 m2 PR2 HIn BY. lits. bandM. sepM. eapply cj_pres_bytes_at; [exact PR2| exact BY|]. do 3 right. left. exists D, n. rewrite LEN. split; [exact HIn| lia]. Qed.

  Lemma pres_ppres : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> (forall b, In b LR -> In b LBx) ->
    ppres sp0 LR LF SP P m m1 -> ppres sp0 LR LF SP P m m2.
  Proof. intros LBx m1 m2 PR2 INL PR. eapply ppres_trans; [exact PR|]. eapply ppres_of_cj_pres; [exact PR2| lia| exact INL]. Qed.

  Lemma pres_pbuf_sh : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> (forall b, In b LR -> In b LBx) ->
    pbuf_sh m1 P -> pbuf_sh m2 P.
  Proof.
    intros LBx m1 m2 PR2 INL PSH. lits. bandM. sepM.
    apply (ppres_pbuf_sh sp0 LR LF SP P m1 m2); [| exact PSH| exact PLF| alia| alia| alia (* [comment removed for export] *)].
    eapply ppres_of_cj_pres; [exact PR2| lia| exact INL].
  Qed.

  (* [comment removed for export] *)
  Notation dch := (dch depth).

  (* [comment removed for export] *)
  Definition OFRAME (w24 : word) : list cell :=
    C8 (Z_to_bv 64 U) :: C8 (SHR (P + 32)) :: C8 (Z_to_bv 64 (P + 32)) :: C8 w24 :: C8 (SHR P) :: SAVEDO.

  Lemma OFRAME_fold : forall mm w24,
    rw_cells bsegs mm (SP + -144) (OFRAME w24) ->
    rw_cells bsegs mm (SP + -144) (CB 40 (le8 (Z_to_bv 64 U) ++ le8 (SHR (P + 32)) ++ le8 (Z_to_bv 64 (P + 32)) ++ le8 w24 ++ le8 (SHR P)) :: SAVEDO).
  Proof.
    intros mm w24 FR. unfold OFRAME in FR.
    apply (rw_cells_merge bsegs mm _ [] [C8 (Z_to_bv 64 U); C8 (SHR (P + 32)); C8 (Z_to_bv 64 (P + 32)); C8 w24; C8 (SHR P)]) in FR.
    cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma fail_oD : forall (junk : list byte) (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells bsegs m1 (SP + -144) (CB 40 junk :: SAVEDO) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS bsegs POST (CSTO 0x861d8 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 head) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HPX CH Hdd FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    assert (B0 : 0 <= B - pv_cost_pre (blen - off)).
    { clear -BPRE OFF. unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *. lia. }
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. change (Z_to_bv 64 534036) with (wz DELETE_ENTRY).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (DEL dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPX' | exact ST | exact ERR | exact MI | exact TP | exact TV | exact SDEL | reflexivity | alia
              | rewrite cost_free_eq in *; lia ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 TRS2 -> MI2 ST2 ERR2 HL2 HP2 TV2 GM2 PR2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x861dc)) with (Z_to_bv 64 0x861dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INL : forall b, In b LR -> In b ((U, 64) :: LR)) by (intros b Hb; right; exact Hb).
    apply (pres_frame _ _ _ _ PR2) in FR; [| reflexivity].
    apply (pres_pbuf _ _ _ _ _ _ _ PR2) in PB.
    apply (pres_block _ _ _ U _ PR2 ltac:(left; reflexivity)) in ND; [| reflexivity].
    apply (pres_text _ _ _ PR2 ltac:(right; exact (proj1 HDn))) in BY.
    eapply (ret0_o junk off1 depth1 m2 mo2 g2 LR2 TRS2 (B1 - cost_free * Z.of_nat (length X)) errv1);
      [| apply Permutation_sym; exact HP2| exact FR| exact PB| exact ND| exact FA| exact FRM| rewrite cost_free_eq in *; lia].
    split; [exact HL2|]. split; [exact BY|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [eapply pres_ppres; [exact PR2| exact INL| exact PR]|]. split; [eapply gmono_trans; [exact GM| exact GM2]|].
    split; [exact TV2|]. eapply pres_pbuf_sh; [exact PR2| exact INL| exact PSH].
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o1 : forall (junk : list byte) (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells bsegs m1 (SP + -144) (CB 40 junk :: SAVEDO) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS bsegs POST (CSTO 0x861d0 x1 x5 x6 x7 x8 (Z_to_bv 64 head) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CH) 3%nat; intros HR1 _ HR2).
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. if_cases Kh; zify_cond Kh.
    - (* [comment removed for export] *)
      subst head. pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HPX. cbn [length] in HB.
      apply evt_done. eapply ret0_o; [exact MIDm| exact HPX| exact FR| exact PB| exact ND| exact FA| exact FRM| lia].
    - apply evt_done.
      eapply fail_oD; [exact MIDm| exact HPX| exact CH| exact Hdd| exact FR| exact PB| exact ND| exact FA| exact FRM| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o24 : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells bsegs m1 (SP + -144) (OFRAME (Z_to_bv 64 head)) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS bsegs POST (CSTO 0x861cc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done.
    eapply fail_o1; [exact MIDm| exact HPX| exact CH| exact Hdd| | exact PB| exact ND| exact FA| exact FRM| exact HB].
    apply (OFRAME_fold m1 (Z_to_bv 64 head)). unfold OFRAME, SAVEDO, SHR. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o3bc : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells bsegs m1 (SP + -144) (OFRAME (Z_to_bv 64 head)) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS bsegs POST (CSTO 0x86170 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x26 x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM HB. lits. bandM. sepM. unfold CSTO. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done.
    eapply fail_oD; [exact MIDm| exact HPX| exact CH| exact Hdd| | exact PB| exact ND| exact FA| exact FRM| exact HB].
    apply (OFRAME_fold m1 (Z_to_bv 64 head)). unfold OFRAME, SAVEDO, SHR. exact FR.
  Qed.
  (* [comment removed for export] *)
  Lemma obj_tail : forall (junk : list byte) (w32 : word) (o2 hv : Z) (X : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_PRINTABLE m1 (S dch) hv X -> depth <= 999 ->
    rw_cells bsegs m1 (SP + -144) (CB 24 junk :: C8 (Z_to_bv 64 hv) :: C8 w32 :: SAVEDO) ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen -> Fagree F Fx -> frm0 fcx ->
    B - PV_RATE * (o2 + 1 - off) <= B1 -> Z.of_nat (length X) <= o2 + 1 - off ->
    LSCPS bsegs POST (CSTO 0x85d04 x1 x5 (Z_to_bv 64 U) x7 (Z_to_bv 64 (P + 16)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                           x18 x19 x20 x21 x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HPX CH Hd FR PB ND Ho FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold AERRNO, ATP in ERR. unfold SAVEDO in FR.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m1 U 64 (U + 24) 4 SOU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. sepM. asan_chk CK4.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 28)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    zstep. zstep. fix_lit_store.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1a end.
    assert (SOUa : shadow_ok m1a U 64) by (eapply shadow_ok_high_store; [exact SOU| exact MU| lia| alia| lia| alia]).
    pose proof (shadow_ok_shchk m1a U 64 (U + 16) 8 SOUa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK8. asan_chk CK8.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B1 m2 mo1 g1) by (eapply (art_block_store AI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store AI); [exact HL| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hv X).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL PR PSH CH SOU SOUa.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX LF TRS1 B1 m3 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL2| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hv X).
    { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 PLF) 8%nat; intros _ _ _ _ _ _ _ FD).
      destruct (FD A k ltac:(eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hin])); change (fsz 1) with 128 in *; lia. }
    clear MU WM HL2 PR2 PSH2 CH2.
    zstep. zstep.
    apply (rw_cells_merge bsegs m3 _ [] [CB 24 junk; C8 (Z_to_bv 64 hv); C8 w32]) in FR.
    cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
    eapply evt_cut; [apply (epilogue_run_o (junk ++ le8 (Z_to_bv 64 hv) ++ le8 w32)); exact FR|]. intros ms' ->.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply lscps_done. unfold parse_value_post.
    nexists 17%nat. exists m3, 1, (o2 + 1), depth, LBX, ([] ++ X), TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL3|]. split; [exact HPX|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH3|]. repeat split; try assumption; alia. }
    split; [exact PR3|]. split; [exact GM|]. split; [exact I|].
    split. { unfold pbuf_at. eqcells PB. }
    right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact HB|]. split; [cbn [app]; exact HX|].
    exists hv, 64, 0. do 2 eexists. exists (S dch), [], X. split; [reflexivity|].
    split; [eqcells ND|]. split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [exact CH3|]. unfold CJ_pvalue_lemmas.dch. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma obj_close : forall (o3 hd A c : Z) (Xall : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x7 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S dch) hd Xall -> depth <= 999 ->
    rw_cells bsegs m1 (SP + -144) (OFRAME (Z_to_bv 64 hd)) ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> 0 <= c < 256 -> Fagree F Fx -> frm0 fcx ->
    B - PV_RATE * (o3 - off) <= B1 -> Z.of_nat (length Xall) <= o3 - off ->
    LSCPS bsegs POST (CSTO 0x86178 x1 x5 (Z_to_bv 64 U) x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 hd) (Z_to_bv 64 (CA + o3)) (Z_to_bv 64 c)
                           x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P + 24)) x19 x20 x21 x22 (Z_to_bv 64 A) x24
                           (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros MIDm HPX HNZ CH Hd FR PB ND Ho Hc FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    pose proof PB as PB'. pose proof FR as FRo.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    ugd.                                                         (* [comment removed for export] *)
    zstep. zstep. if_cases K125; zify_cond K125.
    { (* [comment removed for export] *)
      apply evt_done. eapply fail_o24; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold CJ_pvalue_lemmas.dch; lia| exact FRo| exact PB'| eqcells ND| exact FA| exact FRM|].
      clear -HB HX Ho BPRE OFF. unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *. lia. }
    clear FRo PB'.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
    zstep. zstep.
    assert (INH : In (hd, 64) LBX). { apply INX. exact (cj_chain_head_block _ _ _ _ _ CH HNZ). }
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INH) 4%nat; intros H1 H2 H3 H4).
    try rewrite alloc_ceiling_eq in H4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in H1. bandM. sepM.
    zstep. land7 hd.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B1 m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hd Xall).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I].
      (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL PLF) 8%nat; intros _ _ _ _ _ _ _ FD).
      destruct (FD A' k (INX _ Hin)); change (fsz 1) with 128 in *; lia. }
    clear MU WM PR PSH.
    ugd.                                                         (* [comment removed for export] *)
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    rewrite EX in HPX, INX.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL2 HPh U 64 ltac:(apply in_or_app; right; left; reflexivity)) as [_ HU].
    destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact (proj1 HDn))) as [_ HD].
    assert (HPF : hd + 64 + 16 <= P - 32 \/ P - 32 + 128 <= hd - 16).
    { (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 PLF) 8%nat; intros _ _ _ _ _ _ _ FD).
      destruct (FD hd 64 INH); change (fsz 1) with 128 in *; lia. }
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL2 INH) as SOH.
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    zstep. zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m2 hd 64 (hd + 8) 8 SOH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK8. asan_chk CK8.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX LF TRS1 B1 m3 mo1 g1) by (eapply (art_block_store AI); [exact HL2| exact INH| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store AI); [exact HL2| exact HPh| intros b Hb; apply in_or_app; right; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink AI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    clear MU WM PR2 PSH2 CH2 SVh SKh CHCh CHNh. rewrite <- EX in HPX.
    (* [comment removed for export] *)
    zstep. land7 U. zstep. if_cases GU; zify_cond GU; [| exfalso; lia].
    apply evt_done.
    apply (rw_cells_merge bsegs m3 _ [] [C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 (Z.shiftr (P + 32) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 32))]) in FR.
    cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
    eapply lscps_eq; [| eapply (obj_tail _ _ o3 hd Xall m3 mo1 g1 LBX TRS1 B1 errv1);
      [| exact HPX| exact CH3| exact Hd| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM| unfold PV_RATE in *; lia| lia]].
    { steq. }
    split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
    split; [exact PR3|]. split; [exact GM|]. split; [exact TV| exact PSH3].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_empty : forall (junk : list byte) (w32 : word) (o2 : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      x1 x5 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: LR) LBX ->
    rw_cells bsegs m1 (SP + -144) (CB 32 junk :: C8 w32 :: SAVEDO) ->
    pbuf_at m1 P CA blen o2 (depth + 1) -> depth <= 999 ->
    rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen -> Fagree F Fx -> frm0 fcx ->
    B - PV_RATE * (o2 + 1 - off) <= B1 ->
    LSCPS bsegs POST (CSTO 0x85cec x1 x5 (Z_to_bv 64 U) x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 depth) x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 (P + 24)) x19 x20 x21 x22 x23 x24 (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros MIDm HP1 FR PB Hd ND Ho FA FRM HB. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HP1).
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold AERRNO, ATP in ERR. unfold SAVEDO in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
    pose proof (munch_refl [(SP + -120, SP + -112)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1a end.
    assert (HL1a : ART AI sp0 SPB LBX LF TRS1 B1 m1a mo1 g1) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (PR1a : ppres sp0 LR LF SP P m m1a).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_frame_store AI); [exact HL| | exact MU| exact WM| alia| lia| exact SP5].
      intros b Hb. eapply Permutation_in; [exact HP1| right; exact Hb]. }
    assert (PSH1a : pbuf_sh m1a P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    clear MU WM HL PR PSH.
    pose proof (munch_refl [(P + 24, P + 32)] m1a) as MU. pose proof (wmono_refl bsegs m1a) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B1 m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL1a| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR1a|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH1a| exact MU| alia| alia| alia]).
    clear MU WM PR1a PSH1a HL1a.
    (* [comment removed for export] *)
    zstep. land7 U. ugd.
    apply evt_done.
    eapply lscps_eq; [| eapply (obj_tail _ w32 o2 0 [] m2 mo1 g1 LBX TRS1 B1 errv1);
      [| exact HP1| apply cj_chain_nil| exact Hd| | unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM| exact HB| cbn; lia]].
    { steq. }
    - split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
      split; [exact PR2|]. split; [exact GM|]. split; [exact TV| exact PSH2].
    - exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition obj_inv (m1 : word -> option byte) (head cur : Z) (X : list cblock) : Prop :=
    (head = 0 /\ X = [])
    \/ (head <> 0 /\ cur <> 0 /\ exists B1 Bv Bk Bc (chc tyc vsc kyc : Z) (pvc p1c vic p2c vdc : word),
          X = B1 ++ (cur, 64) :: Bv ++ Bk ++ Bc
          /\ cj_lseg CJ_PRINTABLE m1 dch head cur B1
          /\ rw_cells bsegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc kyc)
          /\ CJ_PRINTABLE tyc /\ cj_str m1 vsc Bv /\ cj_str m1 kyc Bk /\ cj_chain CJ_PRINTABLE m1 dch chc Bc).

  Lemma obj_inv_chain : forall m1 head cur X, obj_inv m1 head cur X -> cj_chain CJ_PRINTABLE m1 (S dch) head X.
  Proof.
    intros m1 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)].
    - apply cj_chain_nil.
    - apply cj_lseg_chain0. eapply cj_lseg_snoc; eauto. apply CJ_PRINTABLE_range. exact TY.
  Qed.

  Lemma obj_inv_magree : forall m1 m2 head cur X, obj_inv m1 head cur X -> magree (in_cblock X) m1 m2 -> obj_inv m2 head cur X.
  Proof.
    intros m1 m2 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)] MA.
    - left. auto.
    - right. split; [exact NZ|]. split; [exact NZc|]. exists B1, Bv, Bk, Bc, chc, tyc, vsc, kyc, pvc, p1c, vic, p2c, vdc. split; [reflexivity|].
      split. { eapply cj_lseg_magree; [exact SEG| exact MA|]. intros a Ha. rewrite in_cblock_app. left. exact Ha. }
      split. { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. rewrite in_cblock_app, in_cblock_cons. right. left. lia. }
      split; [exact TY|].
      split. { eapply cj_str_magree; [exact MA| exact SV|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. left. exact Ha. }
      split. { eapply cj_str_magree; [exact MA| exact SK|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. left. exact Ha. }
      eapply cj_chain_magree; [exact CH| exact MA|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Variable nfuel : nat.
  Definition OLOOP (c : nat) : Prop :=
    forall (o head cur : Z) (X : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (w24 : word)
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MIDO m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX -> obj_inv m1 head cur X ->
      rw_cells bsegs m1 (SP + -144) (OFRAME w24) ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o - off) <= B1 -> Z.of_nat (length X) <= o - off ->
      LSCPS bsegs POST (CSTO 0x85da0 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 head) x10 x11 x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (SHR (P + 8)) x23 (Z_to_bv 64 cur)
                             (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
End PO.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
Ltac land7 p := replace (Z.land p 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
End CJ_pobject_ctx.

(* [comment removed for export] *)
Module CJ_pobject_ws.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas CJ_pobject_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
Local Ltac sh_transport_via MU H ::= sh_transport_via_fast MU H.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WS.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Hypothesis PVC : pv_pure (POBJ_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp).
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & HDn & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold POBJ_STACK, PARSE_STACK in LO.

  (* [comment removed for export] *)
  Definition ws_mem (m0 m2 : word -> option byte) (r d : Z) : Prop :=
    rw_cells bsegs m2 P (pbuf_cells CA blen r d) /\ bytes_at bsegs m2 CA bs /\ mem_inv bsegs m2
    /\ munch [(P + 16, P + 24)] m0 m2 /\ wmono bsegs m0 m2.

  (* [comment removed for export] *)
  Lemma fin_stop' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin blen bs i = i.
  Proof.
    intros i b Hi Hn Hb. lits. bandM. sepM. unfold fin.
    replace (ws_count (skipn (Z.to_nat i) bs)) with O.
    2:{ destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E; [reflexivity|]. cbn.
        assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
        rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst.
        destruct (Z.leb_spec (bv_unsigned c) 32); [lia| reflexivity]. }
    cbn [Z.of_nat]. rewrite Z.add_0_r. destruct (Z.eqb_spec i blen); lia.
  Qed.

  Lemma fin_ws' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
    fin blen bs i = (if i + 1 =? blen then blen - 1 else fin blen bs (i + 1)).
  Proof.
    intros i b Hi Hn Hb. lits. bandM. sepM. unfold fin.
    destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E.
    { exfalso. assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = None) by (rewrite E; reflexivity).
      rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. discriminate. }
    assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst c.
    assert (Er : rest = skipn (Z.to_nat (i + 1)) bs).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- skipn_skipn with (x := 1%nat) (y := Z.to_nat i).
      hnf. rewrite E. reflexivity. }
    cbn [ws_count]. destruct (Z.leb_spec (bv_unsigned b) 32); [|lia]. rewrite <- Er.
    destruct (Z.eqb_spec (i + 1) blen) as [E1|NE1].
    - pose proof (ws_count_le rest) as HL.
      assert (length rest = 0)%nat. { rewrite Er, length_skipn. lia. }
      replace (ws_count rest) with O by lia.
      lazymatch goal with |- (if ?x =? ?y then _ else _) = _ => replace x with y by lia end. rewrite Z.eqb_refl. reflexivity.
    - replace (i + Z.of_nat (S (ws_count rest))) with (i + 1 + Z.of_nat (ws_count rest)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Notation NC := (18446744073709551615 - CA).

  (* [comment removed for export] *)
  Ltac ws_body IH cnt i PB BY MI MU WM TSH PSH m0 nex :=
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB;
    pose proof (rw_cells_bound bsegs _ _ _ PB) as PBB; rewrite pbuf_cells_size in PBB;
    unfold pbuf_cells, wz in PB; unfold CSTO, SHR;
    let b := fresh "b" in let Hn := fresh "Hn" in
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia];
    pose proof (u8ro_read bsegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD;
    pose proof (byte_range b) as Rb;
    let G := fresh "G" in
    zstep; if_cases G; zify_cond G; [exfalso; lia|];
    zstep; zstep; zstep;
    let CK := fresh "CK" in
    pose proof (TSH (CA + i) ltac:(lia)) as CK; asan_chk CK;
    zstep; zstep;
    let K := fresh "K" in let K2 := fresh "K2" in
    if_cases K; zify_cond K;
    [ (* [comment removed for export] *)
      zstep; if_cases K2; zify_cond K2; [| exfalso; lia];
      apply evt_done; nex;
      split; [reflexivity|];
      split; [unfold pbuf_cells, wz; rewrite (fin_stop' i b) by first [lia | exact Hn]; exact PB|];
      split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM]
    | (* [comment removed for export] *)
      let Z16 := fresh "Z16" in
      pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16; asan_chk Z16; clear Z16;
      zstep; zstep; zstep; if_cases K2; zify_cond K2;
      [ rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|];
        replace (CA + i + 1) with (CA + (i + 1)) by lia;
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; eassumption| exact BY| exact MI| exact MU| exact WM]
      | zstep;
        let Z16' := fresh "Z16" in
        pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16'; asan_chk Z16'; clear Z16';
        zstep; zstep;
        rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia];
        apply evt_done; nex;
        split; [reflexivity|];
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; eassumption|];
        split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM] ] ].

  (* [comment removed for export] *)
  Lemma ws1 : forall (m0 : word -> option byte), text_sh m0 CA blen -> pbuf_sh m0 P ->
    forall (cnt : nat) (i d : Z) (m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x11 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells bsegs m1 P (pbuf_cells CA blen i d) -> bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono bsegs m0 m1 ->
    evt bsegs (fun ms' => exists x5' x10' x14' x17' m2,
                 ms' = CST 0x85cb4 x1 x5' x6 x7 (Z_to_bv 64 (P + 16)) x9 x10' x11 (Z_to_bv 64 blen) (Z_to_bv 64 CA) x14' (Z_to_bv 64 NC) (Z_to_bv 64 32) x17'
                          x18 x19 x20 x21 x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x85c5c x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 x11 (Z_to_bv 64 blen) (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 NC) (Z_to_bv 64 32) x17
             x18 x19 x20 x21 x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros m0 TSH PSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. bandM. sepM. sepM. ws_body IH cnt i PB BY MI MU WM TSH PSH m0 ltac:(nexists 5%nat).
  Qed.

  (* [comment removed for export] *)
  Lemma ws2 : forall (m0 : word -> option byte), text_sh m0 CA blen -> pbuf_sh m0 P ->
    forall (cnt : nat) (i d : Z) (m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x27 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells bsegs m1 P (pbuf_cells CA blen i d) -> bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono bsegs m0 m1 ->
    evt bsegs (fun ms' => exists x10' x11' x12' x15' x16' m2,
                 ms' = CST 0x85ec0 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10' x11' x12' (Z_to_bv 64 CA) (Z_to_bv 64 NC) x15' x16' x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x85e68 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 CA) (Z_to_bv 64 NC) x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros m0 TSH PSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. bandM. sepM. sepM. ws_body IH cnt i PB BY MI MU WM TSH PSH m0 ltac:(nexists 6%nat).
  Qed.

  (* [comment removed for export] *)
  Lemma ws3 : forall (m0 : word -> option byte), text_sh m0 CA blen -> pbuf_sh m0 P ->
    forall (cnt : nat) (i d : Z) (m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x27 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells bsegs m1 P (pbuf_cells CA blen i d) -> bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono bsegs m0 m1 ->
    evt bsegs (fun ms' => exists x10' x11' x13' x15' x16' m2,
                 ms' = CST 0x85f5c x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10' x11' (Z_to_bv 64 CA) x13' (Z_to_bv 64 NC) x15' x16' x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x85f04 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 blen) (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 NC) x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros m0 TSH PSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. bandM. sepM. sepM. ws_body IH cnt i PB BY MI MU WM TSH PSH m0 ltac:(nexists 6%nat).
  Qed.

  (* [comment removed for export] *)
  Lemma ws4 : forall (m0 : word -> option byte), text_sh m0 CA blen -> pbuf_sh m0 P ->
    forall (cnt : nat) (i d : Z) (m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x27 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells bsegs m1 P (pbuf_cells CA blen i d) -> bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono bsegs m0 m1 ->
    evt bsegs (fun ms' => exists x10' x11' x13' x15' x16' m2,
                 ms' = CST 0x86058 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10' x11' (Z_to_bv 64 CA) x13' (Z_to_bv 64 NC) x15' x16' x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x86000 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 blen) (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 NC) x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros m0 TSH PSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. bandM. sepM. sepM. ws_body IH cnt i PB BY MI MU WM TSH PSH m0 ltac:(nexists 6%nat).
  Qed.

  (* [comment removed for export] *)
  Lemma ws5 : forall (m0 : word -> option byte), text_sh m0 CA blen -> pbuf_sh m0 P ->
    forall (cnt : nat) (i d : Z) (m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x27 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells bsegs m1 P (pbuf_cells CA blen i d) -> bytes_at bsegs m1 CA bs -> mem_inv bsegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono bsegs m0 m1 ->
    evt bsegs (fun ms' => exists x10' x12' x13' x15' x16' m2,
                 ms' = CST 0x860f8 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10' (Z_to_bv 64 CA) x12' x13' (Z_to_bv 64 NC) x15' x16' x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x860a0 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 NC) x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 (SHR (P + 16)) x27 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros m0 TSH PSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. bandM. sepM. sepM. ws_body IH cnt i PB BY MI MU WM TSH PSH m0 ltac:(nexists 6%nat).
  Qed.
End WS.


End CeilWrap.
End CJ_pobject_ws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
Import CJ_pobject_ctx.
Import CJ_pobject_ws.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POL.
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
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, AMALLOC_STACK; lia | sclr_tac ].
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
  Ltac xor1 c s := replace (Z.lxor (Z.b2z (0 <? c)) (Z.b2z (s <? 1))) with 1
      by (rewrite (proj2 (Z.ltb_lt 0 c) ltac:(lia)); rewrite (proj2 (Z.ltb_ge s 1) ltac:(lia)); reflexivity).

  Notation FAILO24 := (fail_o24 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation OBJCLOSE := (obj_close AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation PRES_FRAME := (pres_frame sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PBUF := (pres_pbuf sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_TEXT := (pres_text sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PSH := (pres_pbuf_sh sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).

  (* [comment removed for export] *)
  Lemma after_ws5 : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A : Z) (pvA : word) (chA tyA vsA kyA : Z) (viA vdA : word) (X Bv Bk Bc : list cblock)
           m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
           x1 x5 x7 x9 x10 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bk ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells bsegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA kyA) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_str m1 kyA Bk -> cj_chain CJ_PRINTABLE m1 dch chA Bc ->
      rw_cells bsegs m1 (SP + -144) (OFR (Z_to_bv 64 hd)) ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o3 - off) <= B1 -> Z.of_nat (length (X ++ (A, 64) :: Bv ++ Bk ++ Bc)) <= o3 - off ->
      LSCPS bsegs POST (CST 0x860f8 x1 x5 (Z_to_bv 64 U) x7 (Z_to_bv 64 (P + 16)) x9 x10 (Z_to_bv 64 CA) x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (SHR (P + 8)) (Z_to_bv 64 A) x24
                             (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG NDA HTA SVA SKA CHA FR PB ND FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    assert (CH : cj_chain CJ_PRINTABLE m1 (S dch) hd (X ++ (A, 64) :: Bv ++ Bk ++ Bc)).
    { eapply cj_lseg_chain; [exact SEG|]. eapply cj_chain_one; [exact ANZ| exact NDA| apply CJ_PRINTABLE_range; exact HTA| exact HTA| exact SVA| exact SKA| exact CHA]. }
    assert (FAIL : forall x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x22' x23' x24' x26' x27' x28' x29' x30' x31',
      LSCPS bsegs POST (CST 0x861cc x1 x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x22' x23' x24'
                             x26' x27' x28' x29' x30' x31' Fx fcx m1) mo1 g1).
    { intros. eapply FAILO24; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold CJ_pvalue_lemmas.dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM| clear -HB HX Ho Ho3 BPRE OFF; blia]. }
    unfold CSTO in FAIL.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. pose proof FR as FRo. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) apply evt_done. apply FAIL. }
    zstep. replace (o3 + CA) with (CA + o3) by lia.
    ugd. zstep. zstep. zstep. xor1 CA (CA + o3). ugd. ugd.
    zstep. zstep.
    (nelim (text_read m1 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
    pose proof (byte_range b) as Rb.
    pose proof (TS (CA + o3) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      apply evt_done. pose proof (IHc (Z.to_nat (blen - o3)) ltac:(lia)) as IH. unfold OLOOP, CSTO, SHR in IH.
      eapply (IH o3 hd A (X ++ (A, 64) :: Bv ++ Bk ++ Bc) m1 mo1 g1 LBX TRS1 B1 errv1);
        [lia| lia| exact Hd| exact MIDm| exact HPX| | unfold OFRAME, SAVEDO, SHR; exact FR| exact PB'| exact ND| exact FA| exact FRM| exact HB| exact HX].
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bk, Bc, chA, tyA, vsA, kyA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [exact NDA|]. split; [exact HTA|]. split; [exact SVA|]. split; [exact SKA| exact CHA]. }
    (* [comment removed for export] *)
    zstep. apply evt_done.
    eapply lscps_eq; [| eapply (OBJCLOSE o3 hd A (bv_unsigned b) (X ++ (A, 64) :: Bv ++ Bk ++ Bc) m1 mo1 g1 LBX TRS1 B1 errv1);
      [exact MIDm| exact HPX| exact HNZ| exact CH| exact Hd| exact FRo| exact PB'| exact ND| lia| lia| exact FA| exact FRM| exact HB| exact HX]].
    steq.
  Qed.
  Notation AFTER_WS5 := after_ws5.

  (* [comment removed for export] *)
  Lemma after_val : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o4 hd A KS k : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock)
           m1 mo1 g1 LBX TRS1 (B4 B5 : Z) errv1 Fx fcx
           x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o + 2 <= o4 -> depth <= 999 ->
      MID m1 mo1 g1 LBX TRS1 B5 errv1 -> Permutation ((A, 64) :: X5 ++ (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells bsegs m1 (SP + -144) (OFR (Z_to_bv 64 hd)) ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o4 - 1 - off) <= B4 -> Z.of_nat (length X) + 2 <= o4 - 1 - off ->
      ( (r = 0 /\ X5 = [] /\ rw_cells bsegs m1 A (node_cells 0 pvA 0 16 (wz 0) 0 (wz 0) (wz 0) (wz 0) KS)
          /\ B4 - pv_cost_pre (blen - o4) <= B5)
        \/ (r = 1 /\ depth5 = depth + 1 /\ o4 <= off5 <= blen /\ B4 - PV_RATE * (off5 - o4) <= B5
             /\ Z.of_nat (length X5) <= off5 - o4
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells bsegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' KS)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      LSCPS bsegs POST (CST 0x86064 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (SHR (P + 8)) (Z_to_bv 64 A) x24
                             (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho4 Hd MIDm HPX HNZ ANZ SEG SK FR PB ND FA FRM HB HX RES. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; apply in_or_app; right; left; reflexivity]).
    assert (INA : In (A, 64) LBX) by (eapply perm_in_head; exact HPX).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL PLF) as BHA.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    eapply lscps_step_evt. cbv beta delta [mkR].
    destruct RES as [(-> & -> & NDA & HB5) | (-> & -> & Ho5 & HB5 & HX5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| exact SK| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO24; [exact MIDm| | exact CH| unfold CJ_pvalue_lemmas.dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM
        | clear -HB HX HB5 Ho Ho4 BPRE OFF; blia].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound bsegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ [(KS, k)] ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done_k. }
      pose proof PB as PB'. pose proof FR as FRo.
      unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
      assert (CHA' : cj_chain CJ_PRINTABLE m1 dch chA Bc) by (eapply cj_chain_mono_d; [exact CHA| unfold CJ_pvalue_lemmas.dch; lia]).
      clear CHA.
      assert (HXall : Z.of_nat (length (X ++ (A, 64) :: Bv ++ [(KS, k)] ++ Bc)) <= off5 - off).
      { clear -HX HX5 Ho4 Ho5. rewrite !length_app in *. cbn [length] in *. rewrite ?length_app in *. cbn [length] in *. unfold cblock in *. lia. }
      zstep. if_false.
      zstep.
      pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
      zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
      zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (AFTER_WS5 c IHc o off5 hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m1 mo1 g1 LBX TRS1 B5 errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX'| exact HNZ| exact ANZ| exact SEG| eqcells NDA| exact HTA| exact SVA| exact SK| exact CHA'
          | exact FRo| exact PB'| eqcells ND| exact FA| exact FRM| clear -HB HB5 Ho4 Ho5; unfold PV_RATE in *; lia| exact HXall].
      + zstep. rewrite zb_lxor_ones by lia.
        pose proof (fin_off0 P blen off5 bs LEN ltac:(lia)) as FO.
        eapply evt_cut.
        { eapply (ws5 sp gp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC m1 TS PSH (Z.to_nat (blen - off5)) off5 (depth + 1) m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 12%nat; intros x10' x12' x13' x15' x16' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO, SHR. rewrite <- FO in PB2.
        destruct (BHA A 64 INA) as [_ APd].
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B5 m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU2| exact WM2| lia| lia]).
        assert (PR2 : ppres sp0 LR LF SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU2| exact WM2| lia| lia]. }
        assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU2| alia| alia| alia]).
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I]. destruct (BHA A' k' Hin). lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        assert (SVA2 : cj_str m2 vsA Bv).
        { eapply cj_str_frame; [exact SVA| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
        assert (CHA2 : cj_chain CJ_PRINTABLE m2 dch chA Bc).
        { eapply cj_chain_frame; [exact CHA'| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
        pose proof (skipws_off_range bs off5 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (AFTER_WS5 c IHc o (skipws_off bs off5) hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m2 mo1 g1 LBX TRS1 B5 errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX'| exact HNZ| exact ANZ| exact SEG2| eqcells NDA| exact HTA| exact SVA2| exact SK2| exact CHA2
          | unfold OFRAME, SAVEDO, SHR; exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| clear -HB HB5 Ho4 Ho5 OR; unfold PV_RATE in *; lia
          | eapply Z.le_trans; [exact HXall| lia]].
        split; [exact HL2|]. split; [exact BY2|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI2|]. split; [exact ST|].
        split; [exact PR2|]. split; [exact GM|]. split; [exact TV| exact PSH2].
  Qed.

  (* [comment removed for export] *)
  Lemma key_done : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A KS k : Z) (pvA : word) (X : list cblock) m1 mo1 g1 LBX TRS1 B3 errv1 Fx fcx
           x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o + 2 <= o3 <= blen -> depth <= 999 ->
      MID m1 mo1 g1 LBX TRS1 B3 errv1 -> Permutation ((A, 64) :: (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells bsegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells bsegs m1 (SP + -144) (OFR (Z_to_bv 64 hd)) ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells bsegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o3 - off) <= B3 -> Z.of_nat (length X) + 2 <= o3 - off ->
      LSCPS bsegs POST (CST 0x85f5c x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 0) x10 x11 (Z_to_bv 64 CA) x13 x14 x15 x16 x17
                             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (SHR (P + 8)) (Z_to_bv 64 A) x24
                             (SHR (P + 16)) (SHR (P + 24)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG SK NDA FR PB ND FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound bsegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
    assert (INA : In (A, 64) LBX) by (eapply perm_in_head; exact HPX).
    assert (INU : In (U, 64) LBX) by (eapply Permutation_in; [exact HPX| right; right; left; reflexivity]).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL PLF) as BHA.
    assert (APART : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
    { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL| exact HPX| exact Hin]. }
    destruct (APART U 64 ltac:(right; left; reflexivity)) as [_ AU]. destruct (APART D n ltac:(right; right; apply in_or_app; right; exact (proj1 HDn))) as [_ AD].
    destruct (BHA A 64 INA) as [_ APd].
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INA) as SOA.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    ugd.                                                       (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (munch_refl [(A + 32, A + 64)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m1 A 64 (A + 32) 8 SOA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; (lia_on Ho Ho3 ANZ HX HDn OFF NAB A2 H H0 H4))) as CK32. asan_chk CK32.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m1 A 64 (A + 56) 8 SOA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; (lia_on Ho Ho3 ANZ HX HDn OFF NAB A2 H H0 H4))) as CK56. asan_chk CK56.
    zstep. zstep. sepM. fix_lit_store. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B3 m2 mo1 g1) by (eapply (art_block_store AI); [exact HL| exact INA| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store AI); [exact HL| exact HPX| intros b Hb; right; right; apply in_or_app; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| (cut_on [Ho Ho3 HDn PF1 OFF U1 D1 NAB] (cut_on [Ho Ho3 HDn PF1 OFF U1 D1 NAB] alia))| alia| alia]).
    assert (TS2 : text_sh m2 CA blen) by (eapply text_sh_high_store; [exact TS| exact MU| (cut_on [Ho Ho3 HDn PF1 OFF U1 D1 NAB] (cut_on [Ho Ho3 HDn PF1 OFF U1 D1 NAB] alia))| lia| alia]).
    assert (DJ : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> disjoint_from [(A + 32, A + 64)] A' n').
    { intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' Hin). lia. }
    assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. right; right. apply in_or_app. left. exact Hin. }
    assert (SK2 : cj_str m2 KS [(KS, k)]).
    { eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A' n' [E|[]]. inversion E; subst. apply DJ. left. reflexivity. }
    assert (MID2 : MID m2 mo1 g1 LBX TRS1 B3 errv1).
    { split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
      split; [exact PR2|]. split; [exact GM|]. split; [exact TV| exact PSH2]. }
    clear MU WM HL PR SEG SK DJ MIDm PSH TS SOA.
    (* [comment removed for export] *)
    assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
    { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG2| intros; exact I| lia]|].
      eapply cj_chain_one; [exact ANZ| eqcells NDA| lia| exact I| apply cj_str_null| exact SK2| apply cj_chain_nil]. }
    cbn [app] in CH.
    assert (HPXf : Permutation ((U, 64) :: (X ++ (A, 64) :: [(KS, k)]) ++ LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR). }
    assert (FAIL : forall x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x22' x23' x24' x26' x27' x28' x29' x30' x31' m', m' = m2 ->
      LSCPS bsegs POST (CST 0x861cc x1 x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x22' x23' x24'
                             x26' x27' x28' x29' x30' x31' Fx fcx m') mo1 g1).
    { intros until m'. intros ->. eapply FAILO24; [exact MID2| exact HPXf| exact CH| unfold CJ_pvalue_lemmas.dch; lia| unfold OFRAME, SAVEDO, SHR; exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM
        | clear -HB HX Ho Ho3 BPRE OFF; blia]. }
    unfold CSTO in FAIL.
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 8) PSH2 ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done. apply FAIL. reflexivity. }
    zstep. ugd. zstep. zstep. zstep. xor1 CA (CA + o3). ugd. ugd.
    zstep. zstep.
    (nelim (text_read m2 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    pose proof (TS2 (CA + o3) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. if_cases K58; zify_cond K58.
    { apply evt_done. apply FAIL. reflexivity. }
    clear FAIL CH HPXf.
    (* [comment removed for export] *)
    (nelimp MID2 9%nat; intros HL _ _ _ _ PR _ _ PSH).
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
    { intros A' k' Hin. cbn. split; [|exact I]. destruct (BHA A' k' Hin). lia. }
    assert (TS3 : text_sh m3 CA blen) by (eapply text_sh_high_store; [exact TS2| exact MU| alia| lia| alia]).
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    (* [comment removed for export] *)
    assert (JOIN : forall x10' x11' x13' x14' x15' x16' m4,
      rw_cells bsegs m4 P (pbuf_cells CA blen (skipws_off bs (o3 + 1)) (depth + 1)) -> bytes_at bsegs m4 CA bs -> mem_inv bsegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono bsegs m3 m4 ->
      evt bsegs (fun ms' => LSCPS bsegs POST ms' mo1 g1)
        (CST 0x86058 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 0) x10' x11' (Z_to_bv 64 CA) x13' x14' x15' x16' x17
             (Z_to_bv 64 (P + 24)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + 2147450880)) (Z_to_bv 64 A) x24
             (Z_to_bv 64 (Z.shiftr (P + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) x28 x29 x30 x31 Fx fcx m4)).
    { intros x10' x11' x13' x14' x15' x16' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO.
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4. pose proof NDA as NDA4. trc NDA4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : ART AI sp0 SPB LBX LF TRS1 B3 m4 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU24| exact WM24| lia| lia]).
      assert (PR4 : ppres sp0 LR LF SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU24| exact WM24| lia| lia]. }
      assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU24| alia| alia| alia]).
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
      { eapply cj_lseg_frame; [exact SEG2| exact MU24| exact WM24|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
      assert (SK4 : cj_str m4 KS [(KS, k)]).
      { eapply cj_str_frame; [exact SK2| exact MU24| exact WM24|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
      clear MU4 WM4 MU24 WM24.
      assert (O4 : o3 + 1 <= skipws_off bs (o3 + 1) <= blen).
      { destruct (Z.eq_dec (o3 + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (o3 + 1)) as OR. rewrite LEN in OR. lia. }
      set (o4 := skipws_off bs (o3 + 1)) in *.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      assert (PI : parse_inv AI TI m4 mo1 g1 sp0 SPB LBX [] ((KS, k) :: (U, 64) :: X ++ LR) LF TRS1 np B3 A P CA blen bs D n lo (SP + -144) errv1).
      { split; [exact HL4|]. split; [exact HPX|]. split; [right; right; apply in_or_app; right; exact (proj1 HDn)|].
        split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|].
        split; [unfold AERRNO, ATP; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
        split; [exact PSH4|]. repeat split; try assumption; (cut_on [Hd CEIL LO PF1 U1 D1 NAB SP2 SP4 Ho Ho3 HDn SP6 OFF O4] alia). }
      change (Z_to_bv 64 535984) with (wz PARSE_VALUE).
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { pose proof (PVREC (Z.to_nat (blen - o4)) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
        sepM. eapply PVS with (U := A) (P := P) (off := o4) (depth := depth + 1) (nx := 0) (ty := 16) (ky := KS) (CH := []); clear PVS; rewrite ?unsigned_lit by (lia_on Hd CEIL LO PF1 U1 D1 SPR NAB PBB);
          first [ exact PI | unfold pbuf_at; exact PB4 | eqcells NDA4 | exact FRM | exact TP | reflexivity | exact I
                | unfold lf_room in *; (cut_to Ho Ho3 HX HDn PF1 OFF U1 D1 NAB Kend O4 Hd DEP CEIL LO SP6 LFR; (cut_to Ho Ho3 Hd CEIL LO OFF O4 DEP SP6 LFR; lia))
                | apply not_pc0_high; lia
                | intros bb; exact (SPV bb)
                | exact SPV
                | apply Forall_app; split; [exact SCONST| exact SDEL]
                | lazymatch goal with |- chain_link _ _ _ => cbn; lia end
                | clear -HB BPRE OFF O4 Ho3 Ho; blia
                | alia ]. }
      cbv beta. intros ms5 mo5 g5 PO'.
      (nelim PO' 36%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 TRS5 B5 errv5 -> -> FA5 FRM5 PI5 PR5 GM5 _ PB5 RES)
.
      rewrite ?unsigned_lit in PI5, PR5 by lia.
      replace (ret_pc (Z_to_bv 64 0x86064)) with (Z_to_bv 64 0x86064) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (nelim PI5 16%nat; intros HL5 HP5 _ _ _ BY5 _ _ ERR5 MI5 ST5 _ TV5 _ PSH5 _).
      apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in FR4; [| lia| cbn; lia| alia| alia].
      apply (ppres_rw_cells_block _ _ _ _ _ _ _ _ _ U 64 PR5) in ND4; [| right; left; reflexivity| lia| cbn; lia| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| lia].
      apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b' Hb'; right; right; apply in_or_app; left; exact Hb'| intros A' n' Hin; apply BHA; apply INX; exact Hin].
      apply (ppres_cj_str _ _ _ _ _ _ _ _ _ PR5) in SK4; [| intros b' [E|[]]; inversion E; subst; left; reflexivity| intros A' n' [E|[]]; inversion E; subst; apply BHA; exact INS].
      assert (PR6 : ppres sp0 LR LF SP P m m5).
      { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b' Hb'; right; right; apply in_or_app; right; exact Hb'| intros f Hf; exact Hf]. }
      unfold wz. eapply (after_val c IHc o o4 hd A KS k pvA X r off5 depth5 X5 m5 mo5 g5 LB5 TRS5 B3 B5 errv5);
        [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| exact ANZ| exact SEG4| exact SK4| unfold OFRAME, SAVEDO, SHR; exact FR4| exact PB5| eqcells ND4
        | eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| clear -HB O4; unfold PV_RATE in *; lia| lia| exact RES].
      split; [exact HL5|]. split; [exact BY5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PR6|].
      split; [eapply gmono_trans; [exact GM| exact GM5]|]. split; [exact TV5| exact PSH5]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - (* [comment removed for export] *)
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz.
      lazymatch goal with H : rw_cells bsegs m3 P _ |- _ => exact H end.
    - zstep. rewrite zb_lxor_ones by lia.
      pose proof (fin_off0 P blen (o3 + 1) bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (ws4 sp gp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC m3 TS3 PSH3 (Z.to_nat (blen - (o3 + 1))) (o3 + 1) (depth + 1) m3);
          [lia| lia| unfold pbuf_cells, wz; lazymatch goal with H : rw_cells bsegs m3 P _ |- _ => exact H end| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 12%nat; intros x10' x11' x13' x15' x16' m4 -> PB4 BY4 MI4 MU4 WM4). unfold CSTO, SHR. rewrite <- FO in PB4.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.
End POL.


End CeilWrap.
