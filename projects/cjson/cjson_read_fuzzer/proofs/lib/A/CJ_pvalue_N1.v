(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
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

  (* [comment removed for export] *)
  Definition PRO_SHV_N : list byte := map zb [-15; -15; -15; -15; -8; -14; -14; -14; -8; -8; -8; -8; -8; -8; -8; -8; -13; -13; -13; -13; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
  Definition NUM_SHV : list byte := map zb [-15; -15; -15; -15; 0; -14; -14; -14; 0; 0; 0; 0; 0; 0; 0; 0; -13; -13; -13; -13; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

  Lemma shb_of_C1 : forall mm a v, rw_cells asegs mm (SH a) [C1 (zb v)] -> 0 <= a < 2^47 -> shb mm a v.
  Proof.
    intros mm a v [[_ HB] _] Ha. cbn [cells_bytes cbytes app] in HB. (nelim HB 3%nat; intros _ _ HB).
    specialize (HB O ltac:(cbn; lia)). cbn [nth_error] in HB. rewrite Z.add_0_r in HB.
    unfold shb. apply mrd_shadow in HB; [exact HB| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma lconv_shb : forall sp0' SPB' LB' LF' TRS' B' mm mo' g', ART AI sp0' SPB' LB' LF' TRS' B' mm mo' g' ->
    rw_cells asegs mm 2147533763 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs mm 2147461204 [C1 (Z_to_bv 8 0)].
  Proof.
    intros until g'. intros HL.
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL (SH ALCONV) ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, ALCONV; cbn; lia)) as H1.
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL (SH ADOTSTR) ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, ADOTSTR; cbn; lia)) as H2.
    replace (alowsh (SH ALCONV)) with 0 in H1 by (vm_compute; reflexivity).
    replace (alowsh (SH ADOTSTR)) with 0 in H2 by (vm_compute; reflexivity).
    change (SH ALCONV) with 2147533763 in H1. change (SH ADOTSTR) with 2147461204 in H2. unfold zb in H1, H2. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ncs_shb : forall mm Fr k, SHCW mm Fr NUM_SHV -> Fr mod 256 = 0 -> 0 <= Fr -> Fr + 256 <= 2^47 -> 0 <= k < 64 -> shb mm (Fr + 64 + k) 0.
  Proof.
    intros mm Fr k H FAL F0 F47 Hk. unfold NUM_SHV in H. apply SHCW_sh_bytes in H.
    eapply (sh_bytes_shb mm Fr _ (Z.to_nat (8 + k / 8)) 0 (Fr + 64 + k) H); [Z.div_mod_to_equations; lia| | Z.div_mod_to_equations; lia| lia].
    assert (E : k / 8 = 0 \/ k / 8 = 1 \/ k / 8 = 2 \/ k / 8 = 3 \/ k / 8 = 4 \/ k / 8 = 5 \/ k / 8 = 6 \/ k / 8 = 7) by (Z.div_mod_to_equations; lia).
    destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
  Qed.
  Lemma ae_shb : forall mm Fr, SHCW mm Fr NUM_SHV -> Fr mod 256 = 0 -> 0 <= Fr -> Fr + 256 <= 2^47 -> shb mm (Fr + 32) 0.
  Proof.
    intros mm Fr H FAL F0 F47. unfold NUM_SHV in H. apply SHCW_sh_bytes in H.
    eapply (sh_bytes_shb mm Fr _ 4 0 (Fr + 32) H); [Z.div_mod_to_equations; lia| reflexivity| cbn; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Definition NQ (SA Fr : Z) (m1 : word -> option byte) (Fx : bvmap 5 word) (fcx : bv 32) (x1 x19 x20 x23 x24 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (nb : list byte) (mm : word -> option byte) (x6 x7 x10 x11 x17 x28 : word),
      (ms' = VSTx SA Fr 0x832c0 x1 (Z_to_bv 64 3) (Z_to_bv 64 k) x7 x10 x11 (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
                   (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) x17 x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24 x28 x29 x30 x31 Fx fcx mm
       \/ ms' = VSTx SA Fr 0x8353c x1 (Z_to_bv 64 3) x6 x7 x10 (Z_to_bv 64 k) (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
                   (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) x17 x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24 x28 x29 x30 x31 Fx fcx mm)
      /\ u8arr asegs mm (Fr + 64) nb /\ length nb = 64%nat
      /\ 0 <= k <= 63 /\ k <= blen - off
      /\ (forall j, (j < Z.to_nat k)%nat -> is_numch (bv_unsigned (nth j nb (wb 0))) = true)
      /\ munch [(Fr + 64, Fr + 128)] m1 mm /\ wmono asegs m1 mm /\ mem_inv asegs mm.

  (* [comment removed for export] *)
  Lemma num_loop : forall (SA Fr : Z) (m1 : word -> option byte) Fx fcx x1 x19 x20 x23 x24 x29 x30 x31 (cnt : nat) (i : Z) mm nb x6 x7 x10 x28,
    VGEOMx SA Fr -> text_sh m1 CA blen ->
    bytes_at asegs m1 CA bs ->
    Z.of_nat cnt = 63 - i -> 0 <= i <= 62 -> i <= blen - off ->
    u8arr asegs mm (Fr + 64) nb -> length nb = 64%nat ->
    (forall j, (j < Z.to_nat i)%nat -> is_numch (bv_unsigned (nth j nb (wb 0))) = true) ->
    munch [(Fr + 64, Fr + 128)] m1 mm -> wmono asegs m1 mm -> mem_inv asegs mm ->
    evt asegs (NQ SA Fr m1 Fx fcx x1 x19 x20 x23 x24 x29 x30 x31)
      (VSTx SA Fr 0x8323c x1 (Z_to_bv 64 3) x6 x7 x10 (Z_to_bv 64 i) (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
            (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros until x31. intros cnt. induction cnt as [cnt IH] using lt_wf_ind.
    intros i mm nb x6 x7 x10 x28 GE TSH BY1 Hcnt Hi Hio BUF BL NUMCH MU WM MI. lits. bandM. sepM. unfold VST, SHV.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY1) as BYB. pose proof (FBLK D n ltac:(eapply Permutation_in; [exact HPU| right; exact HD])) as FDD.
    assert (BY : bytes_at asegs mm CA bs). { eapply bytes_at_transport; [exact BY1| exact MU|]. cbn. lia. }
    assert (EXIT : forall (wh : bool) x6' x11' x7' x10' x17' x28' mm' nb' k,
              u8arr asegs mm' (Fr + 64) nb' -> length nb' = 64%nat -> 0 <= k <= 63 -> k <= blen - off ->
              (forall j, (j < Z.to_nat k)%nat -> is_numch (bv_unsigned (nth j nb' (wb 0))) = true) ->
              munch [(Fr + 64, Fr + 128)] m1 mm' -> wmono asegs m1 mm' -> mem_inv asegs mm' ->
              evt asegs (NQ SA Fr m1 Fx fcx x1 x19 x20 x23 x24 x29 x30 x31)
                (if wh then VSTx SA Fr 0x832c0 x1 (Z_to_bv 64 3) (Z_to_bv 64 k) x7' x10' x11' (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
                              (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) x17' x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24 x28' x29 x30 x31 Fx fcx mm'
                 else VSTx SA Fr 0x8353c x1 (Z_to_bv 64 3) x6' x7' x10' (Z_to_bv 64 k) (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
                              (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) x17' x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24 x28' x29 x30 x31 Fx fcx mm')).
    { intros. apply evt_done. unfold NQ. exists k, nb', mm'. nexists 6%nat. split; [destruct wh; [left; reflexivity| right; reflexivity]|].
      repeat (split; [eassumption|]). assumption. }
    unfold VST, SHV in EXIT.
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) zstep. eapply (EXIT true (Z_to_bv 64 0)); try eassumption; try (cut_to Hi DCA CAD CEIL LO PF1 OFF DEP U1 D1 GSA FLO Kend; lia). intros j Hj. apply NUMCH. lia. }
    destruct (nth_error bs (Z.to_nat (off + i))) as [c|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs (off + i) c (Z_to_bv 64 (CA + off + i)) BY Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    pose proof (byte_range c) as Rc.
    (* [comment removed for export] *)
    assert (STORE : forall (cv : Z) x6' x7' x28', is_numch cv = true -> 0 <= cv < 256 ->
      evt asegs (NQ SA Fr m1 Fx fcx x1 x19 x20 x23 x24 x29 x30 x31)
        (MS (mkR x1 (Z_to_bv 64 SA) gp tp (Z_to_bv 64 3) x6' x7' sp (Z_to_bv 64 SA) (Z_to_bv 64 cv) (Z_to_bv 64 i) (Z_to_bv 64 46) (Z_to_bv 64 10) (Z_to_bv 64 58)
               (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) (Z_to_bv 64 Fr) x19 x20 (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 x24
               (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28' x29 x30 x31)
            Fx (Z_to_bv 64 0x83228) fcx None mm (seg_rom asegs))).
    { intros cv x6' x7' x28' NC Rcv.
      pose proof (u8arr_store_ok asegs _ _ _ i (Z_to_bv 64 (Fr + 64 + i)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. zstep. zstep. zstep. rewrite le1_lit.
      pose proof (u8arr_write asegs _ _ _ i (Z_to_bv 8 cv) BUF ltac:(lia)) as BUF'. clear BUF. store_done. rename BUF' into BUF.
      assert (NUMCH' : forall j, (j < Z.to_nat (i + 1))%nat -> is_numch (bv_unsigned (nth j (upd nb (Z.to_nat i) (Z_to_bv 8 cv)) (wb 0))) = true).
      { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
        - erewrite nth_error_nth; [| apply nth_error_upd_same; lia]. rewrite Z_to_bv_unsigned. cbn. unfold bv_wrap.
          change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. exact NC.
        - destruct (nth_error_lt_some nb j ltac:(lia)) as [b Hb].
          erewrite nth_error_nth; [| rewrite nth_error_upd_other by lia; exact Hb].
          specialize (NUMCH j ltac:(lia)). erewrite nth_error_nth in NUMCH; [exact NUMCH| exact Hb]. }
      zstep. if_cases K63; zify_cond K63.
      - eapply (EXIT true (Z_to_bv 64 0)); [exact BUF| rewrite upd_length; exact BL| lia| lia| intros j Hj; apply NUMCH'; lia| exact MU| exact WM| exact MI].
      - eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [exact GE| exact TSH| exact BY1| lia| lia| lia| exact BUF| rewrite upd_length; exact BL| exact NUMCH'| exact MU| exact WM| exact MI]. }
    zstep. zstep. zstep.
    pose proof (TSH (CA + off + i) ltac:(lia)) as CK. replace (CA + off + i) with (CA + off + i) in CK by lia. sepM. asan_chk CK.
    zstep. zstep. zstep. if_cases Kdig; zify_cond Kdig.
    { (* [comment removed for export] *) apply STORE; [apply digit_numch; clear -Rc Kdig; Z.div_mod_to_equations; lia| lia]. }
    zstep. zstep. if_cases Kbig; zify_cond Kbig.
    { (* [comment removed for export] *) eapply (EXIT false _ (Z_to_bv 64 0)); try eassumption; try lia. }
    zstep. zstep. zstep. if_cases Kmask; zify_cond Kmask.
    { (* [comment removed for export] *)
      assert (R43 : 0 <= bv_unsigned c + -43 <= 58) by (clear -Rc Kbig Kdig; Z.div_mod_to_equations; lia).
      apply STORE; [| lia]. replace (bv_unsigned c) with ((bv_unsigned c + -43) + 43) by lia.
      apply num_mask_numch; [lia|]. unfold NUM_MASK. rewrite Z.mod_small in Kmask by lia. exact Kmask. }
    zstep. sepM. sepM. if_cases Kdot; zify_cond Kdot.
    { (* [comment removed for export] *) zstep. apply STORE; [apply dot_numch| lia]. }
    (* [comment removed for export] *)
    zstep. eapply (EXIT false _ (Z_to_bv 64 0)); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma num_fin : forall (SA Fr : Z) mm mo1 g1 TRS1 errv1 Fy fcy (h : word) cs08 lj (r off' : Z)
      y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 x23 y28 y29 y30 y31,
    VGEOMx SA Fr -> MID SA Fr mm mo1 g1 LB TRS1 B errv1 ->
    SHCW mm Fr NUM_SHV -> rw_cells asegs mm Fr [C8 h] ->
    rw_cells asegs mm SA cs08 -> cells_size cs08 = 16%nat -> rw_cells asegs mm (SA + 16) (LOCSV U P Fr lj) ->
    stk asegs mm (SA + 88) (SP + -104) -> rw_cells asegs mm (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at mm P CA blen off' depth -> VRESx mm r LB B off' depth -> Fagree F Fy -> frm0 fcy ->
    LSCPS asegs POST (VSTx SA Fr 0x83390 y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (SHV (P + 16)) (Z_to_bv 64 U)
                        (Z_to_bv 64 (Fr + 64)) (Z_to_bv 64 (Fr + 32)) x23 (Z_to_bv 64 off) y28 y29 y30 y31 Fy fcy mm) mo1 g1.
  Proof.
    intros until y31. intros GE MDm SHCm HDRm L0m S0 L16m STPm SAVWm PBm RESm FAm FRMy. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    (nelimp MDm 10%nat; intros HLm BYm ERRm MIm STm PRm GMm TVm PSHm CCm). unfold AERRNO, ATP in ERRm.
    pose proof (bytes_at_bound _ _ _ _ BYm) as BYB. pose proof (pbuf_at_bound _ _ _ _ _ _ PBm) as PBB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INLR : forall b', In b' LR -> In b' LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    unfold SHCW, NUM_SHV in SHCm. cbn [map] in SHCm.
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold pbuf_at, pbuf_cells, wz in PBm.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. sepM. do 9 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (HL6 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m6 mo1 g1).
    { eapply (art_frame AI); [exact HLm| exact MU| exact WM|]. constructor; [| constructor].
      do 9 right. exists Fr, 2. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 2) with 256. lia. }
    assert (PR6 : ppres sp0 LR LF SP P m m6).
    { eapply ppres_trans; [exact PRm|]. eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_not_frsh AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB mm mo1 g1 TRS1 B SA a GE HLm INLR Ha Hp) as N2.
      rewrite SHFR. unfold SH, SHADOW_OFFSET in N2. split; [lia| exact I]. }
    assert (PSH6 : pbuf_sh m6 P).
    { eapply pbuf_sh_munch; [exact PSHm| exact MU| lia| lia|]. cbn [disjoint_from].
      pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 55) ltac:(lia)).
      pose proof (SH_mono (P - 32) P ltac:(lia)). pose proof (SH_mono (P + 55) (P - 32 + 127) ltac:(lia)).
      rewrite (SH_aligned_add (P - 32) 127) in * by first [mod8 | (Z.div_mod_to_equations; lia)]. change (127 / 8) with 15 in *.
      destruct PFR as [PF|PF].
      - pose proof (SH_mono (Fr + 256) (P - 32) ltac:(lia)) as M1. rewrite (SH_aligned_add Fr 256) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (256 / 8) with 32 in M1.
        rewrite SHFR. unfold SH, SHADOW_OFFSET in *. split; [lia| exact I].
      - pose proof (SH_mono (P - 32 + 128) Fr ltac:(lia)) as M1. rewrite (SH_aligned_add (P - 32) 128) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (128 / 8) with 16 in M1.
        rewrite SHFR. unfold SH, SHADOW_OFFSET in *. split; [lia| exact I]. }
    assert (CC6 : chain_cells m6 CH).
    { eapply chain_cells_munch; [exact CCm| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. unfold SH, SHADOW_OFFSET in *. lia. }
    assert (MAB : magree (in_cblock LB) mm m6).
    { eapply magree_blocks_of_munch; [exact MU| exact WM|]. intros A' n0 Hin. cbn.
      (* [comment removed for export] *)
      pose_blk_band HLm Hin. (nelimp GE 6%nat; intros _ _ FALx FLOx FHIx _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLOx. bandM. sepM.
      pose proof (frame2_sh_band Fr FALx ltac:(lia) FHIx) as (FB1 & FB2). split; [lia| exact I]. }
    assert (J : rw_cells asegs m6 SA (cs08 ++ LOCSV U P Fr lj)) by (apply (proj2 (rw_cells_split_app _ _ _ _)); split; [exact L0m| rewrite S0; exact L16m]).
    (nelim (frame_join m6 SA _ (SP + -104) J ltac:(rewrite cells_size_app, S0, LOCSV_size; change (Z.of_nat (16 + 72)) with 88; exact STPm) ltac:(rewrite cells_size_app, S0, LOCSV_size; change (Z.of_nat (16 + 72)) with 88; lia)) 3%nat; intros locs FRL SZL)
.
    apply evt_done. eapply (MAGIC_EXIT 0x833b8 SA Fr r m6 mo1 g1 LB TRS1 B errv1 Fy fcy PRO_SHV_N h locs off' depth);
      [cbn; (cut_on [OFF DEP SPR TOPR BOTE RAR S0R BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO BMf2 SMf2 BYB PBB] tauto)| exact GE| | unfold SHCW, PRO_SHV_N; cbn [map]; exact SHCm| reflexivity| exact HDRm| exact FRL| lia| exact SAVWm| exact FAm| exact FRMy
      | unfold pbuf_at; exact PBm| eapply (VRES_magree LR B U blen off depth nx pv ty p1 vi p2 vd ky); [exact RESm| exact MAB]].
    split; [exact HL6|]. split; [exact BYm|]. split; [unfold AERRNO, ATP; exact ERRm|]. split; [exact MIm|]. split; [exact STm|].
    split; [exact PR6|]. split; [exact GMm|]. split; [exact TVm|]. split; [exact PSH6| exact CC6].
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
