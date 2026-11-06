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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_S.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_N1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_N2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_N3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_E1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pvalue_E2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_pvalue_pro OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_S OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_N1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_N2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_N3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_A1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A4.CJ_pvalue_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_E1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
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

(* [comment removed for export] *)
Lemma strncmp_stop_le' : forall x y n, (strncmp_stop x y n <= n)%nat.
Proof.
  induction x as [|a x IH]; intros y n; destruct n as [|n]; cbn; try lia.
  destruct y as [|b y]; [lia|]. destruct (_ && _); [| lia]. specialize (IH y n). lia.
Qed.
Lemma strncmp_stop_cons : forall a x b y n,
  strncmp_stop (a :: x) (b :: y) (S n) = if (a =? b) && negb (a =? 0) then S (strncmp_stop x y n) else O.
Proof. intros. reflexivity. Qed.
Lemma strncmp_stop_firstn : forall x y n,
  strncmp_stop (firstn (Nat.min (S (strncmp_stop x y n)) n) x) (firstn (Nat.min (S (strncmp_stop x y n)) n) y) n = strncmp_stop x y n.
Proof.
  induction x as [|a x IH]; intros y n.
  - destruct n; reflexivity.
  - destruct n as [|n]; [reflexivity|]. destruct y as [|b y]; [reflexivity|].
    rewrite strncmp_stop_cons. destruct ((a =? b) && negb (a =? 0)) eqn:E.
    + rewrite <- Nat.succ_min_distr. cbn [firstn]. rewrite strncmp_stop_cons, E. f_equal. apply IH.
    + change (Nat.min 1 (S n)) with 1%nat. cbn [firstn]. rewrite strncmp_stop_cons, E. reflexivity.
Qed.
Lemma map_firstn' : forall {A B} (f : A -> B) n l, map f (firstn n l) = firstn n (map f l).
Proof. intros A B f n. induction n as [|n IH]; intros [|a l]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma bytes_at_prefix : forall m A l k, bytes_at asegs m A l -> bytes_at asegs m A (firstn k l).
Proof.
  intros m A l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Section PVE2.
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
  Notation DCH := (dch depth).
  Notation CS08x := (CS08 P).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK, SKIPWS_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold VST, SHV, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.
  Hypothesis PO : parse_object_at AI TI nfuel.
  Hypothesis STRTOD : rstrtod_stmt.
  Hypothesis SSPW : sspw_stmt AI.
  Hypothesis SNC : strncmp_icpt_spec.

  (* [comment removed for export] *)
  Notation TAILNULL := (tail_null AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).
  Notation TAILFALSE := (tail_false AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).
  Notation TAILTRUE := (tail_true AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).
  Notation CALL_STRING := (call_string AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STC nfuel).
  Notation OBJ_OR_FAIL := (obj_or_fail AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STPO STC LFR nfuel FUEL PO).
  Notation NUM_FRONT := (num_front AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL STRTOD SSPW).
  Notation ARR_ENTRY := (arr_entry AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK CHL RA1 RA2 FLA STPV STPO STC LFR nfuel FUEL DEL MEMSET PVREC).
  Notation HMAGIC := (Z_to_bv 64 0x41b58ab3).

  (* [comment removed for export] *)
  Definition VFRE (SA Fr : Z) (m1 : word -> option byte) (jae jn : list byte) (ls : list cell) : Prop :=
    SHCW m1 Fr PRO_SHV /\ rw_cells asegs m1 Fr [C8 HMAGIC]
    /\ rw_cells asegs m1 (Fr + 32) [CB 8 jae] /\ rw_cells asegs m1 (Fr + 64) [CB 64 jn]
    /\ rw_cells asegs m1 SA ls /\ cells_size ls = 88%nat
    /\ stk asegs m1 (SA + 88) (SP + -104) /\ rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Lemma VFRE_munch : forall SA Fr m1 m2 jae jn ls W,
    VGEOMx SA Fr -> VFRE SA Fr m1 jae jn ls -> munch W m1 m2 -> wmono asegs m1 m2 ->
    (forall lo' hi', In (lo', hi') W -> (alloc_ceiling <= lo' /\ hi' <= SA) \/ (AIMG_HI <= lo' /\ hi' <= alloc_ceiling /\ (hi' <= Fr \/ Fr + 256 <= lo') /\ sclr lo' (hi' - lo'))) ->   (* [comment removed for export] *)
    VFRE SA Fr m2 jae jn ls.
  Proof.
    intros SA Fr m1 m2 jae jn ls W (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') (SHC & HDR & AE & NC & L & SZ & STP & SAVW) MU WM HW. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO, HW. bandM. sepM. try rewrite alloc_ceiling_eq in FHI, HW. pose proof (SH_bounds Fr ltac:(lia)) as SB.
    pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (255 / 8) with 31 in SB2.
    assert (DJ : forall A k, 0 <= k -> ((SA <= A /\ A + k <= SP) \/ (Fr <= A /\ A + k <= Fr + 256) \/ (A = SH Fr /\ k = 32)) -> disjoint_from W A k).
    { pose proof (frame2_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). rewrite SH_shiftr in FB1, FB2.
      clear - HW SB SB2 CEIL LO GSA FHI FLO DEP FB1 FB2. intros A k Hk HA. revert HW. induction W as [|[lo' hi'] W IH]; intros HW; [exact I|]. cbn. split.
      - destruct (HW lo' hi' ltac:(left; reflexivity)) as [[H1 H2]|(H1 & H2 & H3)]; lia.
      - apply IH. intros lo2 hi2 Hin. apply HW. right. exact Hin. }
    split. { unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, SH_shiftr. cbn [length PRO_SHV map]. apply DJ; [lia|]. right; right. split; [reflexivity|]. reflexivity. }
    split. { eapply rw_cells_transport; [exact HDR| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact AE| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact L| exact MU| exact WM|]. apply DJ; rewrite ?SZ; cbn; lia. }
    split; [exact SZ|].
    split. { eapply stk_transport_disjoint; [exact STP| exact MU| exact WM|]. apply DJ; lia. }
    eapply rw_cells_transport; [exact SAVW| exact MU| exact WM|]. apply DJ; cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma VFRE_VFR : forall SA Fr m1 jae jn j0 j64,
    VFRE SA Fr m1 jae jn (LOCSE P Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]) -> VFRx SA Fr m1 PRO_SHV HMAGIC jae jn [CB 16 j0] j64.
  Proof.
    intros SA Fr m1 jae jn j0 j64 nelH_; (nelim nelH_ 8%nat; intros SHC HDR AE NC L SZ STP SAVW).
    unfold LOCSE in L. cbn [app] in L.
    pose proof (proj1 (rw_cells_split_app m1 SA [CB 16 j0] _) L) as [L0 L16]. cbn [cells_size Cells.csize Nat.add] in L16.
    split; [exact SHC|]. split; [reflexivity|]. split; [exact HDR|]. split; [exact AE|]. split; [exact NC|].
    split; [exact L0|]. split; [reflexivity|]. split; [unfold LOCSV; replace (SA + 16) with (SA + Z.of_nat 16) by lia; exact L16|]. split; [exact STP| exact SAVW].
  Qed.

  (* [comment removed for export] *)
  Lemma stk_store : forall SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 -> munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 -> SA <= lo' -> hi' <= SP - 104 ->
    mem_inv asegs m2 -> SHCW m1 Fr PRO_SHV ->
    MID SA Fr m2 mo1 g1 LB TRS1 B errv1 /\ SHCW m2 Fr PRO_SHV.
  Proof.
    intros SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2 GE MD MU WM Hlo Hhi MI2 SHC. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    pose proof (SH_bounds Fr ltac:(lia)) as SB. pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (255 / 8) with 31 in SB2.
    pose proof (SH_bounds P ltac:(lia)) as SBP. pose proof (SH_bounds (P + 55) ltac:(lia)) as SBP2. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    split.
    - split. { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor]. right; left. cbn. alia. }
      split; [eapply bytes_at_transport; [exact BY| exact MU| dj]|].
      split; [eapply rw_cells_transport; [exact ERR| exact MU| exact WM| unfold AERRNO, ATP; dj]|].
      split; [exact MI2|]. split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj]|].
      split. { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn.
               pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LB ((Fr, 2) :: LF) m1 mo1 g1 TRS1 B a HL INLR
                             ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
               try rewrite alloc_ceiling_eq in BLW. clear -BLW CEIL LO GSA DEP Hlo Hhi. lia. }
      split; [exact GM|]. split; [exact TV|]. split; [eapply pbuf_sh_munch; [exact PSH| exact MU| lia| lia| pbuf_dj (* [comment removed for export] *)]|].
      eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo2 hi2 [E|[]]. inversion E; subst. left. lia.
    - unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, SH_shiftr. cbn [length PRO_SHV map]. dj.
  Qed.

  (* [comment removed for export] *)
  Lemma strncmp_call : forall (SA Fr retpc k LA : Z) (lit : list byte) m1 mo1 g1 TRS1 errv1 Fx fcx jae jn ls
      x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 -> VFRE SA Fr m1 jae jn ls ->
    bytes_at asegs m1 LA lit -> In (LA, k + 1) AGLOB_STRS -> Z.of_nat (length lit) = k + 1 -> 0 <= LA -> LA + k + 1 <= 2^30 ->
    off + k <= blen -> 0 < k -> 4096 <= retpc < 2^32 -> retpc mod 2 = 0 ->
    evt asegs (fun ms' => exists (v : Z) (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) (m2 : word -> option byte),
                 ms' = VSTx SA Fr retpc (Z_to_bv 64 retpc) x5' x6' x7' (Z_to_bv 64 v) x11' x12' x13' x14' x15' x16' x17' x19 x20 x21 x22 x23 x24 x28' x29' x30' x31' Fx fcx m2
                 /\ MID SA Fr m2 mo1 g1 LB TRS1 B errv1 /\ VFRE SA Fr m2 jae jn ls
                 /\ munch [(SA - 2400, SA)] m1 m2 /\ wmono asegs m1 m2)
      (VSTx SA Fr ASTRNCMP_T (Z_to_bv 64 retpc) x5 x6 x7 (Z_to_bv 64 (CA + off)) (Z_to_bv 64 LA) (Z_to_bv 64 k) x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros until x31. intros GE MD VFE LIT INS LL LA0 LA1 Hk Hk0 Hret Heven. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW FBLK GAL SP6.
    (* [comment removed for export] *)
    set (X := firstn (Z.to_nat k) (skipn (Z.to_nat off) bs)). set (Y := firstn (Z.to_nat k) lit).
    set (i := strncmp_stop (map bv_unsigned X) (map bv_unsigned Y) (Z.to_nat k)).
    assert (LX : length X = Z.to_nat k) by (subst X; apply firstn_skipn_length; lia).
    assert (LY : length Y = Z.to_nat k) by (subst Y; rewrite length_firstn; lia).
    assert (Hi : (i <= Z.to_nat k)%nat) by (subst i; apply strncmp_stop_le').
    set (r := Z.min (Z.of_nat i + 1) k).
    set (x := firstn (Z.to_nat r) X). set (y := firstn (Z.to_nat r) Y).
    assert (KEY : strncmp_stop (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat k) = i).
    { subst x y. rewrite !map_firstn'. replace (Z.to_nat r) with (Nat.min (S i) (Z.to_nat k)) by (subst r; lia). subst i. apply strncmp_stop_firstn. }
    assert (BX : bytes_at asegs m1 (CA + off) x).
    { subst x X. apply bytes_at_prefix. apply bytes_at_window; [exact BY| lia| lia]. }
    assert (BYl : bytes_at asegs m1 LA y) by (subst y Y; apply bytes_at_prefix; apply bytes_at_prefix; exact LIT).
    assert (Lx : Z.of_nat (length x) = r) by (subst x; rewrite length_firstn; lia).
    assert (Ly : Z.of_nat (length y) = r) by (subst y; rewrite length_firstn; lia).
    assert (Er : r = Z.min (Z.of_nat i + 1) k) by reflexivity. assert (Hr : 1 <= r <= k) by lia.
    clearbody x y r i. clear X Y LX LY.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (INLR _ HD)) as SOD.
    pose proof (INLR _ HD) as INDX.   (* [comment removed for export] *)
    pose proof (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL) as (GSH & _). rewrite Forall_forall in GSH. specialize (GSH _ INS). cbn [fst snd] in GSH.
    eapply evt_cut.
    { pose proof SNC as SX. unfold strncmp_icpt_spec in SX.
      eapply SX with (x := x) (y := y) (p := CA + off) (q := LA) (n := k) (lo := lo); clear SX; rewrite ?unsigned_lit by lia; rewrite ?KEY;
        first [ eapply (art_icpt_cells AI); exact HL | exact MI | exact ST | reflexivity | exact BX | exact BYl
              | intros _; split; [eapply shadow_ok_sub; [exact SOD| lia| lia| lia]| eapply shadow_ok_sub; [exact GSH| lia| lia| lia]]
              | app_rng0
              | left; unfold lowmem_range, KLOWSHADOW_BEG; lia
              | alia ]. }
    cbv beta. intros ms' PO'.
    (nelim PO' 20%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2).
    rewrite ?unsigned_lit in MU2, ST2 by lia. unfold ASTRFN_STACK in MU2.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| exact Heven]).
    apply evt_done. eexists. nexists 14%nat. exists m2. split; [reflexivity|].
    split.
    - split. { eapply (art_frame AI); [exact HL| exact MU2| exact WM2|]. constructor; [| constructor]. right; left. cbn. alia. }
      split; [eapply bytes_at_transport; [exact BY| exact MU2| dj]|].
      split; [eapply rw_cells_transport; [exact ERR| exact MU2| exact WM2| unfold AERRNO, ATP; dj]|].
      split; [exact MI2|]. split; [exact ST2|].
      split. { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hp. cbn.
               pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LB ((Fr, 2) :: LF) m1 mo1 g1 TRS1 B a HL INLR
                             ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
               try rewrite alloc_ceiling_eq in BLW. clear -BLW CEIL LO GSA DEP. lia. }
      split; [exact GM|]. split; [exact TV|].
      split. { eapply pbuf_sh_munch; [exact PSH| exact MU2| lia| lia|]. pbuf_dj (* [comment removed for export] *). }
      eapply chain_cells_munch; [exact CC| exact CHOK| exact MU2| lia| lia|]. intros lo2 hi2 [E|[]]. inversion E; subst. left. lia.
    - split; [| split; [exact MU2| exact WM2]]. eapply VFRE_munch; [exact GE| exact VFE| exact MU2| exact WM2|]. intros lo' hi' [E|[]]. inversion E; subst. left. alia.
  Qed.

  Ltac prelude GE MD :=
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR); (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC);
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO; try rewrite alloc_ceiling_eq in FHI; unfold AERRNO, ATP in ERR;
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.

  (* [comment removed for export] *)
  Lemma disp : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx jae jn (j0 j64 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr PRO_SHV -> rw_cells asegs m1 Fr [C8 HMAGIC] -> rw_cells asegs m1 (Fr + 32) [CB 8 jae] -> rw_cells asegs m1 (Fr + 64) [CB 64 jn] ->
    rw_cells asegs m1 SA (LOCSE P Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82ea8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 CA) x20 (Z_to_bv 64 P) (Z_to_bv 64 blen) x23 (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC HDR AE NC L STP SAVW PB ND FA FRM. lits. bandM. sepM. prelude GE MD.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    pose proof (VFRE_VFR SA Fr m1 jae jn j0 j64 (conj SHC (conj HDR (conj AE (conj NC (conj L (conj eq_refl (conj STP SAVW)))))))) as VF.
    pose proof L as L'. unfold LOCSE in L'. cbn [app] in L'. unfold SHV in L'.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *)
      (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m1 PRO_SHV HMAGIC jae jn [CB 16 j0] j64 VF ltac:(lia)) 3%nat; intros locs FRL SZL).
      zstep. apply evt_done.
      eapply (MAGIC_EXIT 0x83568 SA Fr 0 m1 mo1 g1 LB TRS1 B errv1 Fx fcx PRO_SHV HMAGIC locs off depth);
        [cbn; tauto| exact GE| exact MD| exact SHC| reflexivity| exact HDR| exact FRL| lia| exact SAVW| exact FA| exact FRM| exact PB'|].
      exists []. split; [exact HPU|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [eqcells ND| clear -BPRE OFF; blia]. }
    destruct (nth_error bs (Z.to_nat off)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs off b _ BY Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. pose proof (TSH (CA + off) ltac:(lia)) as CK. asan_chk CK.
    zstep. zstep. zstep. if_cases K34; zify_cond K34.
    - (* [comment removed for export] *)
      pose proof (TSH (CA + off) ltac:(lia)) as CK2. asan_chk CK2.
      zstep. zstep. zstep. if_cases K45; zify_cond K45.
      { apply evt_done. eapply lscps_eq; [| eapply (NUM_FRONT SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx HMAGIC jae jn [CB 16 j0] j64);
          [exact GE| exact MD| exact VF| exact PB'| eqcells ND| lia| exact FA| exact FRM]]. steq. }
      zstep. zstep. zstep. if_cases Kdig; zify_cond Kdig.
      { apply evt_done. eapply lscps_eq; [| eapply (NUM_FRONT SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx HMAGIC jae jn [CB 16 j0] j64);
          [exact GE| exact MD| exact VF| exact PB'| eqcells ND| lia| exact FA| exact FRM]]. steq. }
      (* [comment removed for export] *)
      pose proof (TSH (CA + off) ltac:(lia)) as CK3. asan_chk CK3.
      zstep. zstep. zstep. if_cases K91; zify_cond K91.
      + (* [comment removed for export] *)
        apply evt_done. eapply lscps_eq; [| eapply (OBJ_OR_FAIL SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx PRO_SHV HMAGIC jae jn [CB 16 j0] j64);
          [exact GE| exact MD| exact VF| exact PB'| eqcells ND| lia| exact FA| exact FRM]]. steq.
      + (* [comment removed for export] *)
        apply evt_done. eapply lscps_eq; [| eapply (ARR_ENTRY SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx PRO_SHV HMAGIC jae jn j0 j64 b);
          [exact GE| exact MD| exact VF| exact PB'| eqcells ND| lia| exact Hn| clear -K91 Rb; lia| exact FA| exact FRM]]. steq.
    - (* [comment removed for export] *)
      apply evt_done. eapply lscps_eq; [| eapply (CALL_STRING SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx PRO_SHV HMAGIC jae jn [CB 16 j0] j64);
        [exact GE| exact MD| exact VF| exact PB'| eqcells ND| lia| exact FA| exact FRM]]. steq.
  Qed.

  (* [comment removed for export] *)
  Lemma chk_true : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx jae jn (j0 j64 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr PRO_SHV -> rw_cells asegs m1 Fr [C8 HMAGIC] -> rw_cells asegs m1 (Fr + 32) [CB 8 jae] -> rw_cells asegs m1 (Fr + 64) [CB 64 jn] ->
    rw_cells asegs m1 SA (LOCSE P Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82e8c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 CA) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 P) (Z_to_bv 64 blen) x23 (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC HDR AE NC L STP SAVW PB ND FA FRM. lits. bandM. sepM. prelude GE MD.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K4; zify_cond K4.
    { apply evt_done. eapply (disp SA Fr m1 mo1 g1 TRS1 errv1 Fx fcx jae jn j0 j64);
        [exact GE| exact MD| exact SHC| exact HDR| exact AE| exact NC| exact L| exact STP| exact SAVW| exact PB'| eqcells ND| exact FA| exact FRM]. }
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (strncmp_call SA Fr 0x82ea4 4 LIT_TRUE lit_true m1 mo1 g1 TRS1 errv1 Fx fcx jae jn (LOCSE P Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]));
        [exact GE| exact MD| | apply lit_true_at; exact MI| (nelimp lit_slots 3%nat; intros _ _ IT); exact IT| reflexivity| unfold LIT_TRUE; lia| unfold LIT_TRUE; lia| lia| lia| lia| reflexivity].
      split; [exact SHC|]. split; [exact HDR|]. split; [exact AE|]. split; [exact NC|]. split; [exact L|]. split; [reflexivity|]. split; [exact STP| exact SAVW]. }
    cbv beta. intros ms' PO'. (nelim PO' 21%nat; intros v y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 -> MD2 VFE2 MU2 WM2).
    trc ND MU2 WM2. trc PB MU2 WM2.
    (nelim VFE2 8%nat; intros SHC2 HDR2 AE2 NC2 L2 _ STP2 SAVW2).
    unfold VST, SHV. zstep. if_cases Kv; zify_cond Kv.
    - (* [comment removed for export] *)
      apply evt_done. eapply (TAILTRUE SA Fr m2 mo1 g1 TRS1 errv1 Fx fcx PRO_SHV HMAGIC j0 j64);
        [exact GE| exact MD2| exact SHC2| reflexivity| exact HDR2| exact L2| exact STP2| exact SAVW2| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| lia| exact FA| exact FRM].
    - apply evt_done. eapply (disp SA Fr m2 mo1 g1 TRS1 errv1 Fx fcx jae jn j0 j64);
        [exact GE| exact MD2| exact SHC2| exact HDR2| exact AE2| exact NC2| exact L2| exact STP2| exact SAVW2| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma chk_false : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx jae jn (j0 j56 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr PRO_SHV -> rw_cells asegs m1 Fr [C8 HMAGIC] -> rw_cells asegs m1 (Fr + 32) [CB 8 jae] -> rw_cells asegs m1 (Fr + 64) [CB 64 jn] ->
    rw_cells asegs m1 SA (LOCSE P Fr j0 [CB 24 j56]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82e68 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 CA) (Z_to_bv 64 (off + 4)) (Z_to_bv 64 P) (Z_to_bv 64 blen) (Z_to_bv 64 U) (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC HDR AE NC L STP SAVW PB ND FA FRM. lits. bandM. sepM. prelude GE MD.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold LOCSE in L. cbn [app] in L. unfold SHV in L.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA + 56, SA + 64)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    destruct (stk_store SA Fr m1 mo1 g1 TRS1 errv1 _ _ m2 GE MD MU WM ltac:(lia) ltac:(lia) MI2 SHC) as [MD2 SHC2].
    pose proof (proj1 (proj2 (proj2 (proj2 MD2)))) as MI2'.
    clear MU WM MD SHC HL BY ERR ST PR PSH CC.
    zstep. zstep. if_cases K5; zify_cond K5.
    { apply evt_done. eapply (chk_true SA Fr m2 mo1 g1 TRS1 errv1 Fx fcx jae jn j0 _);
        [exact GE| exact MD2| exact SHC2| exact HDR| exact AE| exact NC| unfold LOCSE, SHV; cbn [app]; first [exact L| eqcells L]| exact STP| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact FA| exact FRM]. }
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (strncmp_call SA Fr 0x82e88 5 LIT_FALSE lit_false m2 mo1 g1 TRS1 errv1 Fx fcx jae jn (LOCSE P Fr j0 [C8 (Z_to_bv 64 U); CB 16 _]));
        [exact GE| exact MD2| | apply lit_false_at; exact MI2'| (nelimp lit_slots 3%nat; intros _ IF _); exact IF| reflexivity| unfold LIT_FALSE; lia| unfold LIT_FALSE; lia| lia| lia| lia| reflexivity].
      split; [exact SHC2|]. split; [exact HDR|]. split; [exact AE|]. split; [exact NC|]. split; [unfold LOCSE, SHV; cbn [app]; first [exact L| eqcells L]|]. split; [reflexivity|]. split; [exact STP| exact SAVW]. }
    cbv beta. intros ms' PO'. (nelim PO' 21%nat; intros v y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MD3 VFE3 MU3 WM3).
    trc ND MU3 WM3. trc PB MU3 WM3.
    (nelim VFE3 8%nat; intros SHC3 HDR3 AE3 NC3 L3 _ STP3 SAVW3).
    unfold VST, SHV. zstep. if_cases Kv; zify_cond Kv.
    - (* [comment removed for export] *)
      apply evt_done. eapply (TAILFALSE SA Fr m3 mo1 g1 TRS1 errv1 Fx fcx PRO_SHV HMAGIC j0 _);
        [exact GE| exact MD3| exact SHC3| reflexivity| exact HDR3| exact L3| exact STP3| exact SAVW3| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| lia| exact FA| exact FRM].
    - apply evt_done. eapply (chk_true SA Fr m3 mo1 g1 TRS1 errv1 Fx fcx jae jn j0 _);
        [exact GE| exact MD3| exact SHC3| exact HDR3| exact AE3| exact NC3| exact L3| exact STP3| exact SAVW3| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Theorem pv_body : forall (mo1 : Model) (TRS1 : list (list Z)) (errv1 : word) (SA Fr : Z) m5 Fx fcx (jae jn lj : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m5 mo1 g LB TRS1 B errv1 ->
    SHCW m5 Fr PRO_SHV -> rw_cells asegs m5 Fr [C8 HMAGIC] ->
    rw_cells asegs m5 (Fr + 32) [CB 8 jae] -> rw_cells asegs m5 (Fr + 64) [CB 64 jn] ->
    rw_cells asegs m5 SA [CB 80 lj; C8 (Z_to_bv 64 Fr)] -> stk asegs m5 (SA + 88) (SP + -104) ->
    rw_cells asegs m5 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m5 P CA blen off depth -> rw_cells asegs m5 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82de8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 (Z_to_bv 64 P) s6 (Z_to_bv 64 U) s8 x28 x29 x30 x31 Fx fcx m5) mo1 g.
  Proof.
    intros until x31. intros GE MD SHC HDR AE NC L STP SAVW PB ND FA FRM. lits. bandM. sepM. prelude GE MD.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. if_cases KP; zify_cond KP; [exfalso; lia|].
    zstep. zstep. pose proof (sh_zero_shb m5 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA + 16, SA + 56)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    pose proof (sh_zero_shb m5 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. pose proof (sh_zero_shb m5 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8.
    zstep. zstep.
    zstep. zstep. asan_chk Z16. clear Z16.
    zstep. zstep. zstep. zstep. zstep. zstep. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    lazymatch goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    destruct (stk_store SA Fr m5 mo1 g TRS1 errv1 _ _ m6 GE MD MU WM ltac:(lia) ltac:(lia) MI6 SHC) as [MD6 SHC6].
    pose proof (proj1 (proj2 (proj2 (proj2 MD6)))) as MI6'.
    clear MU WM MD SHC HL BY ERR ST PR PSH CC.
    (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4.
    { apply evt_done. eapply (chk_false SA Fr m6 mo1 g TRS1 errv1 Fx fcx jae jn _ _);
        [exact GE| exact MD6| exact SHC6| exact HDR| exact AE| exact NC| unfold LOCSE, SHV; cbn [app]; first [exact L| eqcells L]| exact STP| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact FA| exact FRM]. }
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (strncmp_call SA Fr 0x82e64 4 LIT_NULL lit_null m6 mo1 g TRS1 errv1 Fx fcx jae jn (LOCSE P Fr _ [CB 24 _]));
        [exact GE| exact MD6| | apply lit_null_at; exact MI6'| (nelimp lit_slots 3%nat; intros IN _ _); exact IN| reflexivity| unfold LIT_NULL; lia| unfold LIT_NULL; lia| lia| lia| lia| reflexivity].
      split; [exact SHC6|]. split; [exact HDR|]. split; [exact AE|]. split; [exact NC|]. split; [unfold LOCSE, SHV; cbn [app]; first [exact L| eqcells L]|]. split; [reflexivity|]. split; [exact STP| exact SAVW]. }
    cbv beta. intros ms' PO'. (nelim PO' 21%nat; intros v y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m7 -> MD7 VFE7 MU7 WM7).
    trc ND MU7 WM7. trc PB MU7 WM7.
    (nelim VFE7 8%nat; intros SHC7 HDR7 AE7 NC7 L7 _ STP7 SAVW7).
    unfold VST, SHV. zstep. if_cases Kv; zify_cond Kv.
    - (* [comment removed for export] *)
      apply evt_done. eapply (TAILNULL SA Fr m7 mo1 g TRS1 errv1 Fx fcx PRO_SHV HMAGIC _ _);
        [exact GE| exact MD7| exact SHC7| reflexivity| exact HDR7| exact L7| exact STP7| exact SAVW7| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| lia| exact FA| exact FRM].
    - apply evt_done. eapply (chk_false SA Fr m7 mo1 g TRS1 errv1 Fx fcx jae jn _ _);
        [exact GE| exact MD7| exact SHC7| exact HDR7| exact AE7| exact NC7| exact L7| exact STP7| exact SAVW7| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact FA| exact FRM].
  Qed.
End PVE2.


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
End CJ_pvalue_E2.

(* [comment removed for export] *)
Module CJ_pvalue.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_pvalue_pro OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_N2 CJ_pvalue_E2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem pv_step : forall AI TI nfuel,
  flag_apart_stmt AI -> cjson_delete_stmt AI TI -> asan_memset_spec -> rstrtod_stmt -> sspw_stmt AI -> strncmp_icpt_spec ->
  (forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf) -> parse_object_at AI TI nfuel -> parse_value_at AI TI nfuel.
Proof.
  intros AI TI nfuel FLA DEL MEMSET STRTOD SSPW SNC PVREC PO. unfold parse_value_at. intros until ky.
  intros PI ND PB OFF DEP FUEL LO SP16 FRM TP A0 A1 LFR CC CHOK CHL RA1 RA2 STPV STPO STC BPRE.
  pose proof (pv_pure_intro AI TI (PARSE_STACK depth) m mo g sp tp sp0 SPB LB LR LF TRS np B U P CA blen off depth bs D n lo errv nx pv 0 ty p1 0 vi p2 vd ky
                PI ND OFF DEP LO TP) as PVC.
  pose proof PI as (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & ERR & MI & ST & CEIL & TV & PLF & PSH & _).
  subst a0 a1.
  eapply pv_pro;
    first [ exact PVC | exact BPRE | exact CHOK | exact CHL | exact RA1 | exact RA2 | exact FLA
          | apply stkmalloc_stmt'_holds; right; reflexivity
          | exact HL | exact TV | exact BY | exact ERR | exact MI | exact ST | exact PSH | exact CC | exact LFR | exact ND | exact PB | exact FRM
          | unfold PV_BODY; intros; eapply pv_body; eassumption ].
Qed.


End CeilWrap.
End CJ_pvalue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_shgetc_A Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_N2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_S.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_S.CJ_pobject_E.
Import CJ_pvalue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem parse_value_spec : forall AI TI,
  flag_apart_stmt AI -> cjson_delete_stmt AI TI -> asan_memset_spec -> rstrtod_stmt -> sspw_stmt AI -> strncmp_icpt_spec ->
  parse_value_stmt AI TI.
Proof.
  intros AI TI FLA DEL MEMSET STRTOD SSPW SNC nfuel. induction nfuel as [nfuel IH] using lt_wf_ind.
  apply pv_step; try assumption. apply po_step; [exact DEL| exact MEMSET| exact IH].
Qed.

Theorem parse_object_spec : forall AI TI,
  flag_apart_stmt AI -> cjson_delete_stmt AI TI -> asan_memset_spec -> rstrtod_stmt -> sspw_stmt AI -> strncmp_icpt_spec ->
  parse_object_stmt AI TI.
Proof.
  intros AI TI FLA DEL MEMSET STRTOD SSPW SNC nfuel. apply po_step; [exact DEL| exact MEMSET|].
  intros nf _. apply parse_value_spec; assumption.
Qed.


End CeilWrap.
