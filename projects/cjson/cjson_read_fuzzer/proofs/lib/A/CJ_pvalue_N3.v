(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_shgetc_A Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data CJ_iface AShadow CJ_tree.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_N1 CJ_pvalue_N2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

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
Lemma map_Z_to_bv_unsigned : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma u8arr_prefix : forall m A l j, u8arr asegs m A l -> (j <= length l)%nat -> bytes_at asegs m A (firstn j l).
Proof.
  intros m A l j [BY _] Hj. rewrite <- (firstn_skipn j l) in BY. apply bytes_at_app in BY. exact (proj1 BY).
Qed.

Lemma Forall_firstn_nth : forall (l : list byte) (P : byte -> Prop) k d,
  (k <= length l)%nat -> (forall j, (j < k)%nat -> P (nth j l d)) -> Forall P (firstn k l).
Proof.
  intros l P k d Hk H. apply Forall_forall. intros x Hin.
  apply In_nth with (d := d) in Hin. (nelim Hin 3%nat; intros j Hj <-). rewrite length_firstn in Hj.
  rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply H. lia.
Qed.

Lemma firstn_S_nth : forall {X} (l : list X) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  induction l as [|a l IH]; intros k x H; [destruct k; discriminate|].
  destruct k as [|k]; cbn in H |- *; [inversion H; reflexivity|]. rewrite (IH _ _ H). reflexivity.
Qed.

Section PVN.
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

  Notation MASK := 288230376218820613.
  Hypothesis STRTOD : rstrtod_stmt.
  Hypothesis SSPW : sspw_stmt AI.

  Notation NUM_LOOP := (num_loop ra sp gp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC nfuel).
  Notation NUM_BACK := (num_back AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL STRTOD SSPW).

  (* [comment removed for export] *)
  Lemma num_front : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx h jae jn cs08 lj
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    VFRx SA Fr m1 PRO_SHV_N h jae jn cs08 lj ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off < blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x83154 x1 x5 x6 x7 (Z_to_bv 64 (CA + off)) (SHV (CA + off)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 CA) (Z_to_bv 64 U) (Z_to_bv 64 P) x22 x23 (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD VF PB ND Ho FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n ltac:(eapply Permutation_in; [exact HPU| right; exact HD])) as FDD.
    pose proof (FBLK U 64 ltac:(eapply perm_in_head; exact HPU)) as FUU.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL ltac:(eapply Permutation_in; [exact HPU| right; exact HD]) DCA CAD) as TSH.
    (nelimp VF 10%nat; intros SHC L32 HDR AE NC L0 S0 L16 STP SAVW).
    unfold SHCW, PRO_SHV_N in SHC. cbn [map] in SHC. unfold LOCSV, SHV in L16.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ _ LCV). change (cells_at asegs m1 ALCONV [C8 (wz ADOTSTR)]) with (ro_cells asegs m1 ALCONV [C8 (wz ADOTSTR)]) in LCV.
    unfold ALCONV, ADOTSTR, wz in LCV.
    pose proof (lconv_shb AI nfuel _ _ _ _ _ _ _ _ _ HL) as [LSH DSH].
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(Fr + 32, Fr + 40); (Fr + 64, Fr + 128); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. sepM. sbstep. zstep. sepM. fix_lit_store. sepM. do 8 sbstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x83184)) with (Z_to_bv 64 0x83184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. zstep. try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. zstep. if_false.
    zstep. pose proof (sh_zero_shb _ P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    pose proof (sh_zero_shb _ P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. pose proof (sh_zero_shb _ P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (bv_unsigned (zb 0)) with 0 by reflexivity.
    replace (blen <? blen - off) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    match goal with |- context [Z_to_bv 64 (Z.land ?x (blen - off))] =>
      replace (Z_to_bv 64 (Z.land x (blen - off))) with (Z_to_bv 64 (blen - off))
        by (f_equal; change x with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (TSH2 : text_sh m2 CA blen).
    { eapply text_sh_munch; [exact TSH| exact MU| lia| lia|]. cbn [disjoint_from].
      pose proof (SH_bounds CA ltac:(lia)). pose proof (SH_bounds (CA + blen - 1) ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [| exact I].
      destruct FDD as [FD1|FD2].
      - pose proof (SH_mono (CA + blen - 1) (Fr - 1) ltac:(lia)) as M1. pose proof (SH_aligned_add Fr (-1) ltac:(Z.div_mod_to_equations; lia)) as M2.
        replace (Fr + -1) with (Fr - 1) in M2 by lia. change (-1 / 8) with (-1) in M2. rewrite SHFR. unfold SH, SHADOW_OFFSET in *. lia.
      - pose proof (SH_mono (Fr + 256) CA ltac:(lia)) as M1. rewrite (SH_aligned_add Fr 256) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (256 / 8) with 32 in M1.
        rewrite SHFR. unfold SH, SHADOW_OFFSET in *. lia. }
    pose proof (u8arr_of_rw_cells asegs m2 _ _ _ NC) as NB. assert (BL : length jn = 64%nat) by (destruct NC as [[Hwf _] _]; cbn in Hwf; lia).
    eapply evt_cut.
    { eapply (NUM_LOOP SA Fr m2 _ _ _ _ _ _ _ _ _ _ (Z.to_nat 63) 0 m2); [exact GE| exact TSH2| exact BY| lia| lia| lia| exact NB| exact BL| intros j Hj; lia| apply munch_refl| apply wmono_refl| exact MI]. }
    intros ms' NQH. (nelim NQH 18%nat; intros k nb m3 x6' x7' x10' x11' x17' x28' EQ NB3 BL3 Hk Hkb NUMCH MU3 WM3 MI3).
    clear NB.
    trc L0 MU3 WM3. trc L16 MU3 WM3. trc SAVW MU3 WM3. trc STP MU3 WM3. trc ST MU3 WM3. trc HDR MU3 WM3. trc AE MU3 WM3. trc BY MU3 WM3. trc ERR MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3.
    eapply rw_cells_transport in SHC; [| exact MU3| exact WM3| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET in *; lia].
    assert (MU13 : munch [(Fr + 32, Fr + 40); (Fr + 64, Fr + 128); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] m1 m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU3]. intros x Hx. cbn in Hx |- *. lia. }
    pose proof (wmono_trans _ _ _ _ WM WM3) as WM13. clear MU WM MU3 WM3 MI.
    (* [comment removed for export] *)
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    assert (INLR : forall b', In b' LR -> In b' LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (HL3 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m3 mo1 g1).
    { eapply (art_frame AI); [exact HL| exact MU13| exact WM13|]. constructor; [| constructor; [| constructor; [| constructor]]].
      - do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia.
      - do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia.
      - do 9 right. exists Fr, 2. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 2) with 256. lia. }
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU13| exact WM13|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_not_frbody AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m1 mo1 g1 TRS1 B SA a GE HL INLR Ha Hp) as N1.
      pose proof (pv_addr_not_frsh AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m1 mo1 g1 TRS1 B SA a GE HL INLR Ha Hp) as N2.
      rewrite SHFR. unfold SH, SHADOW_OFFSET in N2. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
    assert (PSH3 : pbuf_sh m3 P).
    { eapply pbuf_sh_munch; [exact PSH| exact MU13| lia| lia|]. cbn [disjoint_from].
      pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 55) ltac:(lia)).
      pose proof (SH_mono (P - 32) P ltac:(lia)). pose proof (SH_mono (P + 55) (P - 32 + 127) ltac:(lia)).
      rewrite (SH_aligned_add (P - 32) 127) in * by first [mod8 | (Z.div_mod_to_equations; lia)]. change (127 / 8) with 15 in *.
      destruct PFR as [PF|PF].
      - pose proof (SH_mono (Fr + 256) (P - 32) ltac:(lia)) as M1. rewrite (SH_aligned_add Fr 256) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (256 / 8) with 32 in M1.
        rewrite SHFR. unfold SH, SHADOW_OFFSET in *. split; [lia|]. split; [lia|]. split; [lia| exact I].
      - pose proof (SH_mono (P - 32 + 128) Fr ltac:(lia)) as M1. rewrite (SH_aligned_add (P - 32) 128) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (128 / 8) with 16 in M1.
        rewrite SHFR. unfold SH, SHADOW_OFFSET in *. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU13| lia| lia|]. intros lo' hi' Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[]]]]; inversion E; subst; left; unfold SH, SHADOW_OFFSET in *; lia. }
    assert (MD3 : MID SA Fr m3 mo1 g1 LB TRS1 B errv1).
    { split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI3|]. split; [exact ST|].
      split; [exact PR3|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH3| exact CC3]. }
    assert (NSH : forall k', 0 <= k' < 64 -> shb m3 (Fr + 64 + k') 0).
    { intros k' Hk'. eapply (ncs_shb nfuel); [unfold SHCW, NUM_SHV; cbn [map]; exact SHC| exact FAL| lia| lia| lia]. }
    (* [comment removed for export] *)
    assert (JOIN : forall y1 y6 y7 y11 y12 y17 y28,
      evt asegs (fun ms' => LSCPS asegs POST ms' mo1 g1)
        (MS (mkR y1 (Z_to_bv 64 SA) gp tp (Z_to_bv 64 3) y6 y7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 64 + k)) y11 y12 (Z_to_bv 64 10) (Z_to_bv 64 58)
               (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) y17 (Z_to_bv 64 Fr) (Z_to_bv 64 ((P + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 U) (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 (Z_to_bv 64 off)
               (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) y28 x29 x30 x31)
            Fx (Z_to_bv 64 0x832d4) fcx None m3 (seg_rom asegs))).
    { intros. pose proof (u8arr_store_ok asegs _ _ _ k (Z_to_bv 64 (Fr + 64 + k)) NB3 ltac:(lia) eq_refl) as SOK.
      pose proof (munch_refl [(Fr + 64, Fr + 128)] m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
      zstep. rewrite le1_lit.
      pose proof (u8arr_write asegs _ _ _ k (Z_to_bv 8 0) NB3 ltac:(lia)) as NB4. sepM. store_done.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      assert (HL4 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m4 mo1 g1).
      { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor].
        do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia. }
      assert (PR4 : ppres sp0 LR LF SP P m m4).
      { eapply ppres_trans; [exact PR3|]. eapply ppres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. cbn.
        pose proof (pv_addr_not_frbody AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m3 mo1 g1 TRS1 B SA a GE HL3 INLR Ha Hp) as N1. split; [lia| exact I]. }
      assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_munch; [exact PSH3| exact MU4| lia| lia| cbn [disjoint_from]; pose proof (SH_bounds P ltac:(lia)); unfold SH, SHADOW_OFFSET in *; lia]).
      assert (CC4 : chain_cells m4 CH).
      { eapply chain_cells_munch; [exact CC3| exact CHOK| exact MU4| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
      apply evt_done. eapply (NUM_BACK SA Fr _ mo1 g1 TRS1 errv1 Fx fcx _ cs08 _ (upd nb (Z.to_nat k) (Z_to_bv 8 0)) k);
        [exact GE| | unfold SHCW, NUM_SHV; cbn [map]; exact SHC| exact HDR| exact AE| exact NB4| rewrite upd_length; exact BL3| apply nth_error_upd_same; lia| | lia| lia
        | exact L0| exact S0| unfold LOCSV, SHV; exact L16| exact STP| exact SAVW| unfold pbuf_at; exact PB| exact ND| exact FA| exact FRM].
      - split; [exact HL4|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI3|]. split; [exact ST|].
        split; [exact PR4|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH4| exact CC4].
      - intros j Hj. destruct (nth_error_lt_some nb j ltac:(lia)) as [b Hb]. erewrite nth_error_nth; [| rewrite nth_error_upd_other by lia; exact Hb].
        specialize (NUMCH j Hj). erewrite nth_error_nth in NUMCH; [exact NUMCH| exact Hb]. }
    destruct EQ as [-> | ->]; unfold VST, SHV.
    - zstep. zstep. zstep. pose proof (NSH k ltac:(lia)) as CK. asan_chk CK. apply JOIN.
    - zstep. zstep. zstep. pose proof (NSH k ltac:(lia)) as CK. asan_chk CK. apply JOIN.
  Qed.
End PVN.


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
