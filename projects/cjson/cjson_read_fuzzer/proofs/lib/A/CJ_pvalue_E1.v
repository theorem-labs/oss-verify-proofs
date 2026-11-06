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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit.
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

Section PVE1.
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
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.


  (* [comment removed for export] *)
  Definition LOCSE (Fr : Z) (j0 : list byte) (t56 : list cell) : list cell :=
    [CB 16 j0; C8 (SHV (P + 8)); C8 (Z_to_bv 64 (P + 8)); C8 (SHV P); C8 (Z_to_bv 64 (P + 16)); C8 (SHV (P + 16))] ++ t56 ++ [C8 (Z_to_bv 64 Fr)].

  (* [comment removed for export] *)
  Lemma lit_exit : forall (pc SA Fr off' ty' : Z) (vi' : word) m3 mo1 g1 TRS1 errv1 Fx fcx shb h (locs : list cell)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    In pc MAGIC_SITES ->
    VGEOMx SA Fr -> MID SA Fr m3 mo1 g1 LB TRS1 B errv1 ->
    SHCW m3 Fr shb -> length shb = 32%nat -> rw_cells asegs m3 Fr [C8 h] ->
    rw_cells asegs m3 SA locs -> SA + Z.of_nat (cells_size locs) = SP - 104 ->
    rw_cells asegs m3 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m3 P CA blen off' depth -> off <= off' <= blen -> off' - off >= 1 ->
    rw_cells asegs m3 U (node_cells nx pv 0 ty' p1 0 vi' p2 vd ky) -> CJ_PRINTABLE ty' ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr pc x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m3) mo1 g1.
  Proof.
    intros until x31. intros HPC GE MD SHC L32 HDR FRL SZL SAVW PB Ho Ho1 ND HT FA FRM. lits. bandM. sepM.
    eapply (MAGIC_EXIT pc SA Fr 1 m3 mo1 g1 LB TRS1 B errv1 Fx fcx shb h locs off' depth);
      [exact HPC| exact GE| exact MD| exact SHC| exact L32| exact HDR| exact FRL| exact SZL| exact SAVW| exact FA| exact FRM| exact PB|].
    exists []. split; [exact HPU|]. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold PV_RATE; lia|]. split; [cbn; lia|].
    exists 0, ty', 0, vi', vd, 0%nat, [], []. split; [reflexivity|]. split; [exact ND|]. split; [exact HT|].
    split; [apply cj_str_null|]. split; [apply cj_chain_nil| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma item_store : forall SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2 shb (h : word),
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 -> munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 -> U <= lo' -> hi' <= U + 64 ->
    mem_inv asegs m2 -> SHCW m1 Fr shb -> length shb = 32%nat ->
    MID SA Fr m2 mo1 g1 LB TRS1 B errv1 /\ SHCW m2 Fr shb.
  Proof.
    intros SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2 shb h GE MD MU WM Hlo Hhi MI2 SHC L32. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU). pose proof (FBLK U 64 INU) as FUU.
    pose proof (SH_bounds Fr ltac:(lia)) as SB. pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (255 / 8) with 31 in SB2.
    split.
    - split; [eapply (art_block_store AI); [exact HL| exact INU| exact MU| exact WM| lia| lia]|].
      split; [eapply bytes_at_transport; [exact BY| exact MU| dj]|].
      split; [eapply rw_cells_transport; [exact ERR| exact MU| exact WM| unfold AERRNO, ATP; dj]|].
      split; [exact MI2|]. split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj]|].
      split. { eapply ppres_trans; [exact PR|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf].
               eapply (ppres_block_store AI); [exact HL| exact HPU| intros b Hb; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
      split; [exact GM|]. split; [exact TV|]. split; [eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]|].
      eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo2 hi2 [E|[]]. inversion E; subst. left. lia.
    - unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, L32, SH_shiftr. dj.
  Qed.

  (* [comment removed for export] *)
  Lemma pbuf_store : forall SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2 shb,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 -> munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 -> P <= lo' -> hi' <= P + 56 ->
    mem_inv asegs m2 -> SHCW m1 Fr shb -> length shb = 32%nat ->
    MID SA Fr m2 mo1 g1 LB TRS1 B errv1 /\ SHCW m2 Fr shb.
  Proof.
    intros SA Fr m1 mo1 g1 TRS1 errv1 lo' hi' m2 shb GE MD MU WM Hlo Hhi MI2 SHC L32. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (SH_bounds Fr ltac:(lia)) as SB. pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (255 / 8) with 31 in SB2.
    pose proof (SH_bounds P ltac:(lia)) as SBP. pose proof (SH_bounds (P + 55) ltac:(lia)) as SBP2.
    split.
    - split; [eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]|].
      split; [eapply bytes_at_transport; [exact BY| exact MU| dj]|].
      split; [eapply rw_cells_transport; [exact ERR| exact MU| exact WM| unfold AERRNO, ATP; dj]|].
      split; [exact MI2|]. split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj]|].
      split; [eapply ppres_trans; [exact PR| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]|].
      split; [exact GM|]. split; [exact TV|]. split; [eapply pbuf_sh_munch; [exact PSH| exact MU| lia| lia| cbn; unfold SH, SHADOW_OFFSET in *; split; [lia| exact I]]|].
      eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo2 hi2 [E|[]]. inversion E; subst. left. lia.
    - unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, L32, SH_shiftr. dj.
  Qed.

  Ltac lit_prelude GE MD :=
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR); (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC);
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO; try rewrite alloc_ceiling_eq in FHI; unfold AERRNO, ATP in ERR.

  (* [comment removed for export] *)
  Lemma tail_null : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h (j0 j56 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr shb -> length shb = 32%nat -> rw_cells asegs m1 Fr [C8 h] ->
    rw_cells asegs m1 SA (LOCSE Fr j0 [CB 24 j56]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off + 4 <= blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82ef0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (off + 4)) (Z_to_bv 64 P) x22 (Z_to_bv 64 U) x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC L32 HDR L STP SAVW PB ND Ho FA FRM. lits. bandM. sepM. lit_prelude GE MD.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU). pose proof (FBLK U 64 INU) as FUU.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    pose proof (shadow_ok_sh_zero m1 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6 SOU BY ERR ST CC.
    unfold LOCSE in L. cbn [app] in L. unfold SHV in L. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 28)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. pose proof (sh_zero_shb m1 U (U + 64) (U + 24) SZU ltac:(lia)) as CK4. asan_chk CK4. clear CK4.
    zstep. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    destruct (item_store SA Fr m1 mo1 g1 TRS1 errv1 _ _ m2 shb h GE MD MU WM ltac:(lia) ltac:(lia) MI2 SHC L32) as [MD2 SHC2].
    (nelimp MD2 10%nat; intros _ _ _ _ _ _ _ _ PSH2 _). clear MU WM MD SHC PSH SZU.
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    destruct (pbuf_store SA Fr m2 mo1 g1 TRS1 errv1 _ _ m3 shb GE MD2 MU WM ltac:(lia) ltac:(lia) MI3 SHC2 L32) as [MD3 SHC3].
    clear MU WM MD2 SHC2.
    zstep.
    (nelim (frame_join m3 SA _ (SP + -104) L ltac:(cbn [cells_size Cells.csize Nat.add length]; exact STP) ltac:(cbn; lia)) 3%nat; intros locs FRL SZL).
    apply evt_done. eapply (lit_exit 0x82f24 SA Fr (off + 4) 4 vi m3 mo1 g1 TRS1 errv1 Fx fcx shb h locs);
      [cbn; (cut_on [OFF DEP SPR TOPR BOTE BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO PFR BYB PBB NDB FUU] tauto)| exact GE| exact MD3| exact SHC3| exact L32| exact HDR| exact FRL| exact SZL| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| lia| lia| eqcells ND| cbn; auto 10| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma tail_false : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h (j0 j64 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr shb -> length shb = 32%nat -> rw_cells asegs m1 Fr [C8 h] ->
    rw_cells asegs m1 SA (LOCSE Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off + 5 <= blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82f38 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 P) x22 (Z_to_bv 64 (off + 5)) x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC L32 HDR L STP SAVW PB ND Ho FA FRM. lits. bandM. sepM. lit_prelude GE MD.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU). pose proof (FBLK U 64 INU) as FUU.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    pose proof (shadow_ok_sh_zero m1 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6 SOU BY ERR ST CC.
    unfold LOCSE in L. cbn [app] in L. unfold SHV in L. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 28)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. zstep. pose proof (sh_zero_shb m1 U (U + 64) (U + 24) SZU ltac:(lia)) as CK4. asan_chk CK4. clear CK4.
    zstep. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    destruct (item_store SA Fr m1 mo1 g1 TRS1 errv1 _ _ m2 shb h GE MD MU WM ltac:(lia) ltac:(lia) MI2 SHC L32) as [MD2 SHC2].
    (nelimp MD2 10%nat; intros _ _ _ _ _ _ _ _ PSH2 _). clear MU WM MD SHC PSH SZU.
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    destruct (pbuf_store SA Fr m2 mo1 g1 TRS1 errv1 _ _ m3 shb GE MD2 MU WM ltac:(lia) ltac:(lia) MI3 SHC2 L32) as [MD3 SHC3].
    clear MU WM MD2 SHC2.
    (nelim (frame_join m3 SA _ (SP + -104) L ltac:(cbn [cells_size Cells.csize Nat.add length]; exact STP) ltac:(cbn; lia)) 3%nat; intros locs FRL SZL).
    apply evt_done. eapply (lit_exit 0x82f6c SA Fr (off + 5) 1 vi m3 mo1 g1 TRS1 errv1 Fx fcx shb h locs);
      [cbn; (cut_on [OFF DEP SPR TOPR BOTE BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO PFR BYB PBB NDB FUU] tauto)| exact GE| exact MD3| exact SHC3| exact L32| exact HDR| exact FRL| exact SZL| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| lia| lia| eqcells ND| cbn; auto 10| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma tail_true : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h (j0 j64 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    SHCW m1 Fr shb -> length shb = 32%nat -> rw_cells asegs m1 Fr [C8 h] ->
    rw_cells asegs m1 SA (LOCSE Fr j0 [C8 (Z_to_bv 64 U); CB 16 j64]) -> stk asegs m1 (SA + 88) (SP + -104) ->
    rw_cells asegs m1 (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off + 4 <= blen -> Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x830f0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (off + 4)) (Z_to_bv 64 P) x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC L32 HDR L STP SAVW PB ND Ho FA FRM. lits. bandM. sepM. lit_prelude GE MD.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU). pose proof (FBLK U 64 INU) as FUU.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    pose proof (shadow_ok_sh_zero m1 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW GAL SP6 SOU BY ERR ST CC.
    unfold LOCSE in L. cbn [app] in L. unfold SHV in L. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 44)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. zstep. pose proof (sh_zero_shb m1 U (U + 64) (U + 24) SZU ltac:(lia)) as CK4. asan_chk CK4. clear CK4.
    zstep. zstep. fix_lit_store.
    zstep. zstep. zstep. pose proof (sh_zero_shb m1 U (U + 64) (U + 40) SZU ltac:(lia)) as CK40. asan_chk CK40. clear CK40.
    zstep. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    destruct (item_store SA Fr m1 mo1 g1 TRS1 errv1 _ _ m2 shb h GE MD MU WM ltac:(lia) ltac:(lia) MI2 SHC L32) as [MD2 SHC2].
    (nelimp MD2 10%nat; intros _ _ _ _ _ _ _ _ PSH2 _). clear MU WM MD SHC PSH SZU.
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    destruct (pbuf_store SA Fr m2 mo1 g1 TRS1 errv1 _ _ m3 shb GE MD2 MU WM ltac:(lia) ltac:(lia) MI3 SHC2 L32) as [MD3 SHC3].
    clear MU WM MD2 SHC2.
    (nelim (frame_join m3 SA _ (SP + -104) L ltac:(cbn [cells_size Cells.csize Nat.add length]; exact STP) ltac:(cbn; lia)) 3%nat; intros locs FRL SZL).
    apply evt_done. eapply (lit_exit 0x83140 SA Fr (off + 4) 2 (Z_to_bv 64 1) m3 mo1 g1 TRS1 errv1 Fx fcx shb h locs);
      [cbn; (cut_on [OFF DEP SPR TOPR BOTE BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO PFR BYB PBB NDB FUU] (cut_on [OFF DEP SPR TOPR BOTE BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO PFR BYB PBB NDB FUU] tauto))| exact GE| exact MD3| exact SHC3| exact L32| exact HDR| exact FRL| exact SZL| exact SAVW| unfold pbuf_at, pbuf_cells, wz; eqcells PB| lia| lia| eqcells ND| cbn; auto 10| exact FA| exact FRM].
  Qed.
End PVE1.


End CeilWrap.
