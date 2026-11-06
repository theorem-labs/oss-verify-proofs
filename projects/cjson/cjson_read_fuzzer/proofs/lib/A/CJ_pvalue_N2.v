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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_N1.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
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
  (* [comment removed for export] *)
  Definition sspw_stmt : Prop := forall sp0' SPB' LB' LF' TRS' B' mm mo' g', ART AI sp0' SPB' LB' LF' TRS' B' mm mo' g' -> exists canary, ssp_cells mm canary.
  Hypothesis SSPW : sspw_stmt.

  Notation NUM_FIN := (num_fin AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).

  (* [comment removed for export] *)
  Lemma num_back : forall (SA Fr : Z) m3 mo1 g1 TRS1 errv1 Fx fcx h cs08 lj (nb : list byte) (k : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m3 mo1 g1 LB TRS1 B errv1 ->
    SHCW m3 Fr NUM_SHV -> rw_cells asegs m3 Fr [C8 h] -> rw_cells asegs m3 (Fr + 32) [C8 (Z_to_bv 64 0)] ->
    u8arr asegs m3 (Fr + 64) nb -> length nb = 64%nat -> nth_error nb (Z.to_nat k) = Some (Z_to_bv 8 0) ->
    (forall j, (j < Z.to_nat k)%nat -> is_numch (bv_unsigned (nth j nb (wb 0))) = true) -> 0 <= k <= 63 -> k <= blen - off ->
    rw_cells asegs m3 SA cs08 -> cells_size cs08 = 16%nat -> rw_cells asegs m3 (SA + 16) (LOCSV U P Fr lj) ->
    stk asegs m3 (SA + 88) (SP + -104) -> rw_cells asegs m3 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m3 P CA blen off depth -> rw_cells asegs m3 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x832d8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (SHV (P + 16)) (Z_to_bv 64 U) (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m3) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC HDR AE NB BL NTH NUMCH Hk Hkb L0 S0 L16 STP SAVW PB ND FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n ltac:(eapply Permutation_in; [exact HPU| right; exact HD])) as FDD.
    pose proof (FBLK U 64 ltac:(eapply perm_in_head; exact HPU)) as FUU.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    assert (INLR : forall b', In b' LR -> In b' LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    unfold SHCW, NUM_SHV in SHC. cbn [map] in SHC. unfold LOCSV, SHV in L16.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    (* [comment removed for export] *)
    set (pre := map bv_unsigned (firstn (Z.to_nat k) nb)).
    assert (LPRE : length pre = Z.to_nat k) by (unfold pre; rewrite length_map, length_firstn; lia).
    assert (PRECH : Forall (fun c => is_numch c = true) pre).
    { unfold pre. apply Forall_map. apply (Forall_firstn_nth _ _ _ (wb 0)); [lia|]. intros j Hj. apply NUMCH. exact Hj. }
    assert (TXT : bytes_at asegs m3 (Fr + 64) (map (Z_to_bv 8) (pre ++ [0]))).
    { rewrite map_app. unfold pre. rewrite map_Z_to_bv_unsigned. cbn [map].
      replace (firstn (Z.to_nat k) nb ++ [Z_to_bv 8 0]) with (firstn (S (Z.to_nat k)) nb).
      - apply (u8arr_prefix _ _ _ _ NB). lia.
      - apply firstn_S_nth. exact NTH. }
    assert (PRER : Forall (fun c => 0 <= c < 256) pre) by (eapply Forall_impl; [| exact PRECH]; intros c Hc; apply numch_range; exact Hc).
    assert (PREX : Forall (fun c => c <> 120 /\ c <> 88) pre) by (eapply Forall_impl; [| exact PRECH]; intros c Hc; apply numch_not_x; exact Hc).
    (nelim (scan_strtod_total_gen pre PRER PREX) 4%nat; intros bits used SC Hused).
    destruct (SSPW _ _ _ _ _ _ _ _ _ HL) as [canary SSP].
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof STRTOD as RS. unfold rstrtod_stmt, rstrtod_post, RSTRTOD, RERRNO, RATP, RSTRTOD_DEPTH, RGLOBALS_TOP in RS.
    eapply evt_cut.
    { sepM. eapply RS with (T := Fr + 64) (PE := Fr + 32) (txt := pre ++ [0]) (post := []) (lo := lo) (bits := bits) (used := used) (canary := canary); clear RS;
        rewrite ?unsigned_lit by (lia_on CEIL LO SP4 SP5 DEP TOPR GSA);
        first [ exact TXT | exact PRECH | exact SC | exact ST | exact SSP | exact ERR | exact MI | exact FRM | reflexivity | exact AE
              | apply Forall_app; split; [exact PRER| constructor; [lia| constructor]]
              | rewrite LPRE; lia
              | unfold zlength; rewrite length_app, LPRE; cbn [length]; lia
              | unfold wz, ATP in TP; exact TP
              | (lia_on CEIL LO DEP GSA FLO SP4 SP5 TOPR FHI) ]. }
    cbv beta. intros ms' PO.
    (nelim PO 32%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m5 ev' -> MU5 WM5 MI5 FRM5 FAG F10 ST5 PE5 TXT5 SSP5 ERR5 USED)
.
    rewrite ?unsigned_lit in MU5, ST5 by lia. unfold zlength in USED. rewrite LPRE in USED.
    replace (ret_pc (Z_to_bv 64 0x832e4)) with (Z_to_bv 64 0x832e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FA5 : Fagree F F') by (eapply Fagree_trans; [exact FA| apply Fagree_of_strtod; exact FAG]).
    trc L0 MU5 WM5. trc L16 MU5 WM5. trc SAVW MU5 WM5. trc STP MU5 WM5. trc HDR MU5 WM5. trc PB MU5 WM5. trc ND MU5 WM5. sepM. trc BY MU5 WM5.
    eapply rw_cells_transport in SHC; [| exact MU5| exact WM5| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET in *; (lia_on Hkb DCA CAD CEIL LO PF1 OFF DEP U1 D1 GSA GAL FAL FLO FHI SHFR)].
    assert (HL5 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m5 mo1 g1).
    { eapply (art_frame AI); [exact HL| exact MU5| exact WM5|]. constructor; [| constructor; [| constructor; [| constructor]]].
      - right; left. cbn. alia.
      - do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia.
      - do 3 right. left. unfold AERRNO, ATP. cbn. lia. }
    assert (PR5 : ppres sp0 LR LF SP P m m5).
    { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU5| exact WM5|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_not_frbody AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m3 mo1 g1 TRS1 B SA a GE HL INLR Ha Hp) as N1.
      (nelim Hp 3%nat; intros Hc He Hpp). unfold AERRNO, ATP in He.
      pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LB ((Fr, 2) :: LF) m3 mo1 g1 TRS1 B a HL INLR
                    ltac:(intros f Hf; right; exact Hf) Ha ltac:(split; [exact Hc| split; [exact He| exact Hpp]])) as BLW.
      try rewrite alloc_ceiling_eq in BLW. clear -N1 BLW He CEIL LO GSA. lia. }
    assert (PSH5 : pbuf_sh m5 P).
    { eapply pbuf_sh_munch; [exact PSH| exact MU5| lia| lia|]. cbn [disjoint_from]. pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 55) ltac:(lia)).
      unfold SH, SHADOW_OFFSET in *. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
    assert (CC5 : chain_cells m5 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU5| lia| lia|]. intros lo' hi' Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[]]]]; inversion E; subst; left; lia. }
    pose proof (u8arr_transport asegs _ _ m5 _ _ NB MU5 WM5 ltac:(cbn [disjoint_from]; rewrite BL; lia)) as NB5 || pose proof I as NB5.
    clear MU5 WM5 HL PR PSH CC MI ST TXT TXT5 SSP SSP5.
    (* [comment removed for export] *)
    assert (MD5 : MID SA Fr m5 mo1 g1 LB TRS1 B ev').
    { split; [exact HL5|]. split; [exact BY|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|].
      split; [exact PR5|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH5| exact CC5]. }
    zstep. zstep. if_cases Ku; zify_cond Ku.
    { (* [comment removed for export] *)
      zstep. zstep.
      apply evt_done. eapply (NUM_FIN SA Fr m5 mo1 g1 TRS1 ev' F' fc' h cs08 lj 0 off);
        [exact GE| exact MD5| unfold SHCW, NUM_SHV; cbn [map]; exact SHC| exact HDR| exact L0| exact S0| exact L16| exact STP| exact SAVW| unfold pbuf_at; exact PB| | exact FA5| exact FRM5].
      exists []. split; [exact HPU|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [unfold node_cells, wz; exact ND| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL5 INU) as SOU.
    pose proof (shadow_ok_sh_zero m5 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m5 U (U + 64) (U + 48) SZU ltac:(lia)) as CK48. asan_chk CK48. clear CK48.
    pose proof (munch_refl [(U + 24, U + 56)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. zstep. sepM. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (JW : forall (w : word) Fz fcz y10 y12, Fagree F Fz -> frm0 fcz ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo1 g1)
        (MS (mkR (Z_to_bv 64 0x832e4) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) y10 (Z_to_bv 64 (Fr + 64 + used)) w y12 a4' a5' a6' a7'
               (Z_to_bv 64 Fr) (Z_to_bv 64 ((P + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 U) (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 (Z_to_bv 64 off)
               (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            Fz (Z_to_bv 64 0x8333c) fcz None m6 (seg_rom asegs))).
    { intros w Fz fcz y10 y12 FAz FRMz.
      zstep. zstep. zstep.
      pose proof (sh_zero_shb m5 U (U + 64) (U + 40) SZU ltac:(lia)) as CK40. sepM. asan_chk CK40. clear CK40.
      zstep.
      zstep. zstep. zstep.
      pose proof (sh_zero_shb m5 U (U + 64) (U + 24) SZU ltac:(lia)) as CK24. sepM. asan_chk CK24. clear CK24.
      zstep. zstep. fix_lit_store.
      pose proof (sh_zero_shb m5 P (P + 56) (P + 16) PSH5 ltac:(lia)) as Z16. sepM. asan_chk Z16. clear Z16.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      (* [comment removed for export] *)
      assert (HL7 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m7 mo1 g1) by (eapply (art_block_store AI); [exact HL5| exact INU| exact MU| exact WM| lia| lia]).
      assert (PR7 : ppres sp0 LR LF SP P m m7).
      { eapply ppres_trans; [exact PR5|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [eapply (ppres_block_store AI); [exact HL5| exact HPU| intros b' Hb'; exact Hb'| try rewrite alloc_ceiling_eq; lia| lia| exact MU| exact WM| lia| lia]| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf]. }
      assert (PSH7 : pbuf_sh m7 P) by (eapply pbuf_sh_munch; [exact PSH5| exact MU| lia| lia| cbn [disjoint_from]; pose proof (SH_bounds P ltac:(lia)); unfold SH, SHADOW_OFFSET in *; (lia_on PF1 PF2 BMf)]).
      assert (CC7 : chain_cells m7 CH).
      { eapply chain_cells_munch; [exact CC5| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
      clear MU WM.
      pose proof (munch_refl [(P + 16, P + 24)] m7) as MU. pose proof (wmono_refl asegs m7) as WM.
      zstep. zstep. zstep. zstep. sepM. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
      assert (HL8 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m8 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL7| right; exact PLF| exact MU| exact WM| lia| lia]).
      assert (PR8 : ppres sp0 LR LF SP P m m8) by (eapply ppres_trans; [exact PR7| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
      assert (PSH8 : pbuf_sh m8 P) by (eapply pbuf_sh_munch; [exact PSH7| exact MU| lia| lia| cbn [disjoint_from]; pose proof (SH_bounds P ltac:(lia)); unfold SH, SHADOW_OFFSET in *; (lia_on Hkb DCA CAD CEIL LO PF1 PF3 OFF DEP U1 D1 GSA GAL FLO)]).
      assert (CC8 : chain_cells m8 CH).
      { eapply chain_cells_munch; [exact CC7| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
      zstep.
      replace (Fr + 64 + used - (Fr + 64) + off) with (off + used) by lia.
      apply evt_done. eapply (NUM_FIN SA Fr m8 mo1 g1 TRS1 ev' Fz fcz h cs08 lj 1 (off + used));
        [exact GE| | unfold SHCW, NUM_SHV; cbn [map]; exact SHC| exact HDR| exact L0| exact S0| exact L16| exact STP| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| | exact FAz| exact FRMz].
      - split; [exact HL8|]. split; [exact BY|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|].
        split; [exact PR8|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH8| exact CC8].
      - exists []. split; [exact HPU|]. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold PV_RATE; lia|]. split; [cbn; lia|].
        exists 0, 8, 0, w, (reg_get F' 10), 0%nat, [], []. split; [reflexivity|]. split; [eqcells ND|]. split; [cbn; auto 10|].
        split; [apply cj_str_null|]. split; [apply cj_chain_nil| lia]. }
    zstep. zstep. zstep. rewrite bword_nez. if_cases K1.
    - zstep. eapply JW; [repeat (apply Fagree_set; [| first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]]); exact FA5| assumption].
    - zstep. zstep. zstep. zstep. rewrite bword_nez. if_cases K2.
      + eapply JW; [repeat (apply Fagree_set; [| first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]]); exact FA5| assumption].
      + zstep. zstep. eapply JW; [repeat (apply Fagree_set; [| first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]]); exact FA5| assumption].
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
