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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pobject_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_utraps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strncmp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pvalue_N.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaSplit.
Module CJ_pvalue_E.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strncmp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Scan_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pvalue_N OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_pvalue_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_pvalue_L.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].

Section PVE.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.
  Hypothesis STRTOD : rstrtod_stmt.
  Hypothesis PS : parse_string_stmt HI.
  Hypothesis PO : parse_object_at HI nfuel.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTV sp gp tp s7 s8 s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDV HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6).
  Notation dch := (dch depth).
  Notation ALOOPc := (ALOOP HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma ret0_epi : forall (junk : list byte) (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    MID m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x140d0 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND FA FRM. lits. unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    eapply evt_cut; [eapply epilogue_run; [exact PVC| exact FR]|]. intros ms' ->.
    unfold SAVEDV in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    nexists 17%nat. exists m1, 0, off1, depth1, LB1, [], errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.

  (* [comment removed for export] *)
  Lemma lit_ret1 : forall (junk : list byte) (off1 ty1 : Z) (vi1 : word) m1 mo1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    MID m1 mo1 LB errv1 ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty1 p1 0 vi1 p2 vd ky) -> CJ_PRINTABLE ty1 -> off <= off1 <= blen ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x140d0 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) FR PB ND HT Ho FA FRM. lits. unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    eapply evt_cut; [eapply epilogue_run; [exact PVC| exact FR]|]. intros ms' ->.
    unfold SAVEDV in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    nexists 17%nat. exists m1, 1, off1, depth, LB, ([] ++ []), errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HPU|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    exists 0, ty1, 0, vi1, vd, 0%nat, [], []. split; [reflexivity|]. split; [exact ND|]. split; [exact HT|].
    split; [apply cj_str_null|]. split; [apply cj_chain_nil| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_entry : forall (junk : list byte) (b : byte) m1 mo1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    MID m1 mo1 LB errv1 ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off < blen -> nth_error bs (Z.to_nat off) = Some b -> bv_unsigned b = 91 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x13d48 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 off) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 blen) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm FR PB ND Ho Hb Hb91 FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kd; zify_cond Kd.
    { apply evt_done. eapply ret0_tail; [exact PVC| exact MIDm| exact HPU| exact FR| exact PB'| eqcells ND| exact FA| exact FRM]. }
    (* [comment removed for export] *)
    clear PB'. pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL CJ PR.
    (* [comment removed for export] *)
    (nelim (text_read m2 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b0 Hb0 RD0 _).
    rewrite Hb in Hb0. injection Hb0 as <-.
    zstep. if_cases Kz; zify_cond Kz; [killK Kz|]. clear Kz.
    zstep. zstep. zstep. if_cases K91; zify_cond K91; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := off + 1) (depth := depth + 1) (bs := bs);
        [unfold pbuf_at, pbuf_cells; eqcells PB| reflexivity| lia| lia| lia| exact BY| exact LEN| lia| lia| exact MI]. }
    intros ms' PO'. (nelim PO' 13%nat; intros a1' a2' a3' a4' a5' a6' m3 -> MU3 WM3 MI3 PB3 BY3).
    replace (ret_pc (Z_to_bv 64 0x13d7c)) with (Z_to_bv 64 0x13d7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FR MU3 WM3. trc ND MU3 WM3. trc ERR MU3 WM3. trc ST MU3 WM3. clear PB BY MI.
    apply (munch_trans _ _ _ _ MU) in MU3. apply (wmono_trans _ _ _ _ WM) in WM3. clear MU WM.
    assert (HL3 : LHEAP HI SPB LB m3 mo1) by (eapply (lheap_frame_store HI); [exact HL2| exact MU3| exact WM3| alia| alia]).
    assert (CJ3 : CJST m3) by (eapply CJST_high_store; [exact CJ2| exact MU3| exact WM3| alia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_pbuf_store HI); [exact HL2| exact INLR| exact MU3| exact WM3| alia| alia| alia]. }
    clear MU3 WM3 HL2 CJ2 PR2 RD0 m2.
    assert (O2 : off + 1 <= skipws_off bs (off + 1) <= blen).
    { destruct (Z.eq_dec (off + 1) blen) as [E|NE].
      - rewrite skipws_off_noop by lia. lia.
      - pose proof (skipws_off_range bs (off + 1)) as OR. rewrite LEN in OR. lia. }
    set (o2 := skipws_off bs (off + 1)) in *.
    assert (MID3 : MID m3 mo1 LB errv1).
    { split; [exact HL3|]. split; [exact BY3|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI3|]. split; [exact ST| exact PR3]. }
    pose proof PB3 as PB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (bytes_at_bound _ _ _ _ BY3) as BYB3.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *)
      pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      zstep. zstep.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      zstep. apply evt_done. eapply (ret0_epi _ (o2 - 1) (depth + 1) m4 mo1 LB errv1); [| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
      split. { eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]. }
      split; [exact BY3|]. split. { eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]. }
      split; [unfold PERRNO; exact ERR|]. split; [exact MI3|]. split; [exact ST|].
      eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (CA + o2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    (nelim (text_read m3 CA bs o2 (Z_to_bv 64 (CA + o2)) BY3 ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros c2 Hc2 RD2 _).
    pose proof (byte_range c2) as Rc2.
    zstep. zstep. zstep.
    if_cases K93; zify_cond K93.
    - (* [comment removed for export] *)
      pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      zstep. apply evt_done.
      pose proof (aloop HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC nfuel FUEL PVREC (Z.to_nat (blen - (o2 - 1)))) as AL.
      unfold ALOOP, CSTV in AL.
      eapply (AL (o2 - 1) 0 0 [] m4 mo1 LB errv1); [lia| lia| lia| | exact HPU| left; split; reflexivity| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
      split. { eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]. }
      split; [exact BY3|]. split. { eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]. }
      split; [unfold PERRNO; exact ERR|]. split; [exact MI3|]. split; [exact ST|].
      eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| exact INLR| exact MU| exact WM| alia| alia| alia].
    - (* [comment removed for export] *)
      pose proof (munch_refl [(P + 24, P + 32)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA.
      apply evt_done.
      eapply (arr_success HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC nfuel _ o2 0 [] m4 mo1 LB errv1);
        [| exact HPU| apply cj_chain_nil| lia| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia| exact FA| exact FRM].
      split. { eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]. }
      split; [exact BY3|]. split. { eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]. }
      split; [unfold PERRNO; exact ERR|]. split; [exact MI3|]. split; [exact ST|].
      eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| exact INLR| exact MU| exact WM| alia| alia| alia].
  Qed.

  (* [comment removed for export] *)
  Lemma POSTV_shift : forall m1 ms' mo', ppres LR SP P m m1 ->
    parse_value_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR U P CA blen off depth bs D n lo m1 nx pv ty p1 vi p2 vd ky ms' mo' ->
    POST ms' mo'.
  Proof.
    intros m1 ms' mo' PR H. unfold POSTV, parse_value_post in *.
    (nelim H 32%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' r off' depth' LB' X errv' E H1 H2 H3 H4 H5 H6 H7).
    nexists 15%nat. exists F', fc', m', r, off', depth', LB', X, errv'.
    repeat (split; [eassumption|]). split; [eapply ppres_trans; [exact PR| exact H5]|]. split; [exact H6| exact H7].
  Qed.

  Lemma string_post_conv : forall (fc : bv 32) m1 ms' mo', ppres LR SP P m m1 -> frm0 fc ->
    parse_string_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR U P CA blen off depth bs D n lo m1 nx pv 0 ty p1 0 vi p2 vd ky ms' mo' ->
    POST ms' mo'.
  Proof.
    intros fc m1 ms' mo' PR FRM H. lits. unfold POSTV, parse_value_post, parse_string_post in *.
    (nelim H 28%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r off' LB' X errv' E H1 H2 H3 H4 H5 H6).
    nexists 15%nat. exists F, fc, m', r, off', depth, LB', X, errv'.
    split; [exact E|]. split; [exact H1|]. split; [apply Fagree_refl|]. split; [exact FRM|]. split; [exact H2|].
    split; [eapply ppres_trans; [exact PR| exact H3]|]. split; [exact H4|].
    destruct H6 as [(-> & -> & ND)|(-> & S & k & -> & NZ & ND & STR)].
    - left. split; [reflexivity|]. split; [reflexivity| exact ND].
    - right. split; [reflexivity|]. split; [reflexivity|]. split; [exact H5|].
      exists 0, 16, S, vi, vd, 0%nat, [(S, k)], []. split; [reflexivity|]. split; [exact ND|]. split; [cbn; auto 10|].
      split; [exact STR|]. split; [apply cj_chain_nil| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma disp : forall (junk : list byte) (fc : bv 32) m1 mo errv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    MID m1 mo LB errv ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    frm0 fc ->
    SCPS usegs POST (CST 0x13c0c x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 off) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 (off + 5)) x28 x29 x30 x31 F fc m1) mo.
  Proof.
    intros until x31. intros MIDm FR PB ND FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. pose proof ND as ND'. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    assert (PI : stk usegs m1 lo SP -> parse_inv HI m1 mo SPB LB [] LR U P CA blen bs D n lo SP errv).
    { intros ST'. split; [exact HL|]. split; [exact HPU|]. split; [exact (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|].
      split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|].
      split; [exact ST'|]. split; [alia|]. lia. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) apply evt_done. eapply ret0_tail; [exact PVC| exact MIDm| exact HPU| exact FR| exact PB'| exact ND'| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases KW; zify_cond KW; [killK KW|]. clear KW.
    zstep.
    (nelim (text_read m1 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. if_cases K34; zify_cond K34.
    2:{ (* [comment removed for export] *)
      do 10 zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep. apply evt_done.
      eapply scps_mono.
      { pose proof PS as PSS. unfold parse_string_stmt in PSS.
        eapply PSS; clear PSS; [exact (PI ST)| exact ND'| exact PB'| lia| alia| exact TP| reflexivity| reflexivity]. }
      cbv beta. intros ms' mo' PSP. eapply string_post_conv; [exact PR| exact FRM| exact PSP]. }
    zstep. zstep. if_cases K45; zify_cond K45.
    { (* [comment removed for export] *) apply evt_done. eapply number_tail; [exact PVC| exact STRTOD| exact MIDm| exact FR| exact PB'| exact ND'| apply Fagree_refl| exact FRM]. }
    zstep. zstep. zstep. if_cases Kdig; zify_cond Kdig.
    { (* [comment removed for export] *) apply evt_done. eapply number_tail; [exact PVC| exact STRTOD| exact MIDm| exact FR| exact PB'| exact ND'| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    zstep. if_cases KW2; zify_cond KW2; [killK KW2|]. clear KW2.
    zstep. zstep. if_cases K91; zify_cond K91.
    { (* [comment removed for export] *) apply evt_done. eapply arr_entry; [exact MIDm| exact FR| exact PB'| exact ND'| lia| exact Hb| lia| apply Fagree_refl| exact FRM]. }
    zstep. zstep. if_cases K123; zify_cond K123.
    { (* [comment removed for export] *) apply evt_done. eapply ret0_tail; [exact PVC| exact MIDm| exact HPU| exact FR| exact PB'| exact ND'| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    do 10 zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep. apply evt_done.
    eapply scps_mono.
    { pose proof PO as POS. unfold parse_object_at in POS.
      eapply POS; clear POS; [exact (PI ST)| exact ND'| exact PB'| lia| lia| exact FUEL| alia| exact FRM| exact TP| reflexivity| reflexivity]. }
    cbv beta. intros ms' mo' PSP. eapply POSTV_shift; [exact PR| exact PSP].
  Qed.

  (* [comment removed for export] *)
  Lemma strncmp_call : forall (retpc : Z) (fc : bv 32) m1 (k : nat) (lit : list byte) (LA : Z)
      x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    bytes_at usegs m1 CA bs -> bytes_at usegs m1 LA lit -> mem_inv usegs m1 ->
    off + Z.of_nat k <= blen -> (k <= length lit)%nat -> (0 < k)%nat -> 0 <= LA -> LA + Z.of_nat (length lit) <= 2^64 ->
    0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    evt usegs (fun ms' => exists (v : Z) x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31',
                 ms' = CST retpc (Z_to_bv 64 retpc) x5' x6' x7' (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 v) x11' x12' x13' x14' x15' x16' x17'
                          x18 x19 x20 x21 x22 x28' x29' x30' x31' F fc m1)
      (CST 0x220b8 (Z_to_bv 64 retpc) x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 LA) (Z_to_bv 64 (Z.of_nat k)) x13 x14 x15 x16 x17
           x18 x19 x20 x21 x22 x28 x29 x30 x31 F fc m1).
  Proof.
    intros until x31. intros BY LIT MI Hk Hkl Hk0 LA0 LA1 Hret Heven. lits. unfold CSTV.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    destruct (strncmp_model_total (firstn k (skipn (Z.to_nat off) bs)) lit (Z.of_nat k) ltac:(lia)
                ltac:(rewrite firstn_skipn_length; lia) ltac:(lia)) as [v Hv].
    eapply evt_cut.
    { eapply strncmp_spec with (ls := firstn k (skipn (Z.to_nat off) bs)) (rs := lit) (v := v); rewrite ?unsigned_lit by lia.
      - apply bytes_at_window; [exact BY| lia| lia].
      - exact LIT.
      - exact Hv.
      - exact MI. }
    intros ms' PO'. (nelim PO' 18%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 _).
    apply munch_nil_eq in MU2. subst m2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc).
    2:{ symmetry. apply ret_pc_even; [lia| exact Heven]. }
    apply evt_done. nexists 15%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma chk_true : forall (junk : list byte) (fc : bv 32) m1 mo errv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    MID m1 mo LB errv ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    frm0 fc ->
    SCPS usegs POST (CST 0x13be8 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 off) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 (off + 5)) x28 x29 x30 x31 F fc m1) mo.
  Proof.
    intros until x31. intros MIDm FR PB ND FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. pose proof ND as ND'. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_cases K4; zify_cond K4.
    { apply evt_done. eapply disp; [exact MIDm| exact FR| exact PB'| exact ND'| exact FRM]. }
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases KW; zify_cond KW; [killK KW|]. clear KW.
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut; [eapply (strncmp_call 0x13c08 fc m1 4 lit_true LIT_TRUE); [exact BY| apply lit_true_at; exact MI| exact MI| lia| cbn; lia| lia| unfold LIT_TRUE; lia| unfold LIT_TRUE; cbn; lia| lia| reflexivity]|].
    intros ms' nelH_; (nelim nelH_ 16%nat; intros v x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' ->). unfold CSTV.
    zstep. if_cases Kv; zify_cond Kv.
    2:{ apply evt_done. eapply disp; [exact MIDm| exact FR| exact PB'| exact ND'| exact FRM]. }
    (* [comment removed for export] *)
    clear ND' PB'.
    zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA.
    zstep. zstep.
    pose proof (munch_refl [(U + 24, U + 28)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_block_store HI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPU| intros b' Hb'; exact Hb'| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL CJ PR.
    pose proof (munch_refl [(U + 40, U + 44)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LB m3 mo) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPU| intros b' Hb'; exact Hb'| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL2 CJ2 PR2.
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : LHEAP HI SPB LB m4 mo) by (eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL3 CJ3 PR3.
    zstep. apply evt_done.
    eapply (lit_ret1 _ (off + 4) 2 (Z_to_bv 64 1) m4 mo errv); [| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| cbn; auto 10| lia| apply Fagree_refl| exact FRM].
    split; [exact HL4|]. split; [exact BY|]. split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR4].
  Qed.

  (* [comment removed for export] *)
  Lemma chk_false : forall (junk : list byte) (fc : bv 32) m1 mo errv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    MID m1 mo LB errv ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    frm0 fc ->
    SCPS usegs POST (CST 0x13bc0 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 off) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x22 x28 x29 x30 x31 F fc m1) mo.
  Proof.
    intros until x31. intros MIDm FR PB ND FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. pose proof ND as ND'. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. if_cases K5; zify_cond K5.
    { apply evt_done. eapply chk_true; [exact MIDm| exact FR| exact PB'| exact ND'| exact FRM]. }
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases KW; zify_cond KW; [killK KW|]. clear KW.
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut; [eapply (strncmp_call 0x13be4 fc m1 5 lit_false LIT_FALSE); [exact BY| apply lit_false_at; exact MI| exact MI| lia| cbn; lia| lia| unfold LIT_FALSE; lia| unfold LIT_FALSE; cbn; lia| lia| reflexivity]|].
    intros ms' nelH_; (nelim nelH_ 16%nat; intros v x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' ->). unfold CSTV.
    zstep. if_cases Kv; zify_cond Kv.
    2:{ apply evt_done. eapply chk_true; [exact MIDm| exact FR| exact PB'| exact ND'| exact FRM]. }
    (* [comment removed for export] *)
    clear ND' PB'.
    zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA.
    zstep.
    pose proof (munch_refl [(U + 24, U + 28)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_block_store HI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPU| intros b' Hb'; exact Hb'| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL CJ PR.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LB m3 mo) by (eapply (lheap_frame_store HI); [exact HL2| exact MU| exact WM| alia| alia]).
    assert (CJ3 : CJST m3) by (eapply CJST_high_store; [exact CJ2| exact MU| exact WM| alia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_pbuf_store HI); [exact HL2| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL2 CJ2 PR2.
    zstep. apply evt_done.
    eapply (lit_ret1 _ (off + 5) 1 vi m3 mo errv); [| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| cbn; auto 10| lia| apply Fagree_refl| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at usegs m CA bs -> CJST m -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
    stk usegs m lo SP ->
    rw_cells usegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    frm0 fc -> a0 = wz U -> a1 = wz P ->
    SCPS usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz PARSE_VALUE) fc None m (seg_rom usegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST ND PB FRM A0 A1. lits. pose proof (ppres_refl LR SP P m) as PR0.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_VALUE, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    pose proof (munch_refl [(SP + -144, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. carve_frame 144%nat ST. do 8 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 80 ?j :: _) => set (junk0 := j) in FR; clearbody junk0 end.
    assert (HL1 : LHEAP HI SPB LB m1 mo) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ1 : CJST m1) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR1 : ppres LR SP P m m1).
    { eapply ppres_trans; [exact PR0|]. eapply (ppres_frame_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| lia]. }
    clear MU WM HL CJ PR0.
    assert (MID1 : MID m1 mo LB errv).
    { split; [exact HL1|]. split; [exact BY|]. split; [exact CJ1|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR1]. }
    (* [comment removed for export] *)
    zstep. if_cases KP; zify_cond KP; [exfalso; lia|].
    zstep. zstep. zstep. rewrite (align8_land7 P) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA.
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    zstep. zstep. zstep.
    assert (CF : forall x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31',
      SCPS usegs POST (CST 0x13bc0 x1' x5' x6' x7' (Z_to_bv 64 P) (Z_to_bv 64 U) x10' x11' x12' x13' x14' x15' x16' x17'
                           (Z_to_bv 64 off) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x22' x28' x29' x30' x31' F fc m1) mo).
    { intros. eapply (chk_false junk0); [exact MID1| unfold SAVEDV; exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FRM]. }
    unfold CSTV in CF.
    zstep. if_cases K4; zify_cond K4.
    { apply evt_done. apply CF. }
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases KW; zify_cond KW; [killK KW|]. clear KW.
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut; [eapply (strncmp_call 0x13bbc fc m1 4 lit_null LIT_NULL); [exact BY| apply lit_null_at; exact MI| exact MI| lia| cbn; lia| lia| unfold LIT_NULL; lia| unfold LIT_NULL; cbn; lia| lia| reflexivity]|].
    intros ms' nelH_; (nelim nelH_ 16%nat; intros v x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' ->). unfold CSTV.
    zstep. if_cases Kv; zify_cond Kv.
    2:{ apply evt_done. apply CF. }
    (* [comment removed for export] *)
    clear CF.
    zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA.
    zstep.
    pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_frame_store HI); [exact HL1| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR1|]. eapply (ppres_pbuf_store HI); [exact HL1| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL1 CJ1 PR1 MID1.
    pose proof (munch_refl [(U + 24, U + 28)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LB m3 mo) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPU| intros b' Hb'; exact Hb'| alia| exact MU| exact WM| lia| lia]. }
    clear MU WM HL2 CJ2 PR2.
    zstep. zstep. apply evt_done.
    eapply (lit_ret1 junk0 (off + 4) 4 vi m3 mo errv); [| unfold SAVEDV; exact FR| unfold pbuf_at; eqcells PB| eqcells ND| cbn; auto 10| lia| apply Fagree_refl| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.
End PVE.

(* [comment removed for export] *)
Theorem pv_step : forall HI nfuel,
  rstrtod_stmt -> parse_string_stmt HI ->
  (forall nf, (nf < nfuel)%nat -> parse_value_at HI nf) -> parse_object_at HI nfuel -> parse_value_at HI nfuel.
Proof.
  intros HI nfuel STRTOD PS PVREC PO. unfold parse_value_at. intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & CJ & ERR & MI & ST & CEIL & SPP & PSPB & SPB62 & PAL) ND PB OFF DEP FUEL LO FRM TP A0 A1.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (lh_nodup HI _ _ _ _ HL) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  eapply (pv_body HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky);
    [| exact FUEL| exact PVREC| exact STRTOD| exact PS| exact PO| exact HL| exact BY| exact CJ| exact ERR| exact MI| exact ST| exact ND| exact PB| exact FRM| exact A0| exact A1].
  - split; [exact HPU|]. split; [split; [exact HD| split; [exact DCA| exact CAD]]|]. split; [exact LEN|]. split; [exact BLEN|].
    split; [exact CEIL|]. split; [exact LO|]. split; [split; [exact SPP| split; [exact PSPB| split; [exact SPB62| exact PAL]]]|]. split; [exact OFF|]. split; [exact DEP|].
    split; [exact TP|]. split; [eapply (lh_block_range HI); [exact HL| exact INU]|]. split; [eapply (lh_block_range HI); [exact HL| exact IND]|].
    destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL INU IND UD); lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].
End CJ_pvalue_E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Scan_iface.
Import CJ_pvalue_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_pobject_E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem parse_value_spec : forall HI, rstrtod_stmt -> parse_string_stmt HI -> parse_value_stmt HI.
Proof.
  intros HI ST PS nfuel. induction nfuel as [nf IH] using lt_wf_ind.
  apply pv_step; [exact ST| exact PS| exact IH|]. apply po_step; [exact PS| exact IH].
Qed.

Theorem parse_object_spec : forall HI, rstrtod_stmt -> parse_string_stmt HI -> parse_object_stmt HI.
Proof. intros HI ST PS nfuel. apply po_step; [exact PS|]. intros nf _. apply parse_value_spec; [exact ST| exact PS]. Qed.


End CeilWrap.
