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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits ICPT_iface.
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

Section LITF.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Ltac steq := unfold CASE_ST, mkR, SHR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.

  (* [comment removed for export] *)
  Lemma litF_copy : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx
      (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) -> off + 7 <= len ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84dcc) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX L4 ROOM. lits. bandM. sepM. unfold SHR.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN ERR MI _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L4. cbn in L4.
    injection L4 as E4. subst w4. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (pvx_memcpy_lit Q PVL MEMCPY) with (lit := lit_false);
        [exact CTXX| exact (proj1 (proj2 lit_slots))| apply lit_false_at; exact MI| reflexivity| lia| unfold LIT_FALSE; lia| unfold LIT_FALSE; lia| reflexivity| lia]. }
    cbv beta. intros ms' PO.
    (nelim PO 19%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' bs' -> CTX2 NUL).
    replace (ret_pc (Z_to_bv 64 0x84de4)) with (Z_to_bv 64 0x84de4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof CTX2 as [(_ & _ & _ & _ & _ & _ & _ & MI2 & _) _].
    zstep. apply evt_done. cbv beta.
    eapply (pv_ret1 Q PVL FLAGLOW). eapply (pvx_exit1 Q PVL); [exact CTX2| exact NUL].
  Qed.

  (* [comment removed for export] *)
  Lemma litF_commit : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len Bn ns off bs loc jb shp Fx fcx
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31 : word),
    PVMs Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len Bn ns off bs -> PVFR Q mm loc jb shp Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) -> off + 7 <= ns ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 Bn) x11 x12 x13 x14 x15 x16 x17
              (SHR PB) (Z_to_bv 64 PB) x20 (Z_to_bv 64 (PB + 16)) (Z_to_bv 64 ns) (SHR (PB + 8)) (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84da8) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTX FRX L4 ROOM. lits. bandM. sepM. unfold SHR.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(PB, PB + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (stack_shb0 mm (PB + 8) SSZ ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep.
    pose proof (stack_shb0 mm PB SSZ ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (stack_shb0 mm (PB + 16) SSZ ltac:(lia)) as Z16.
    assert (Z16' : shb m2 (PB + 16) 0).
    { unfold shb in *. rewrite <- Z16. apply MU. rewrite wa_unsigned by (unfold SH, SHADOW_OFFSET; lia). cbn. unfold SH, SHADOW_OFFSET. split; [lia| exact I]. }
    asan_chk Z16'. clear Z16 Z16'.
    zstep. apply evt_done. cbv beta.
    assert (CTX2 : PVX Q dep m2 mo1 g1 LB1 TRS1 B1 np1 errv1 Bn ns off bs loc jb shp Fx fcx).
    { eapply (pvx_commit Q PVL); [exact CTX| exact FRX| exact MU| exact WM| | ].
      - lazymatch goal with H : mem_inv asegs m2 |- _ => exact H end.
      - unfold PBS. lazymatch goal with H : rw_cells asegs m2 PB _ |- _ => exact H end. }
    eapply litF_copy; [exact CTX2| exact L4| exact ROOM].
  Qed.

  (* [comment removed for export] *)
  Lemma litF_grow : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ns
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) ->
    len < ns <= INT_MAX -> (2 * len + 2 <= ns \/ ns = INT_MAX) -> off + 7 <= ns ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) x11 x12 x13 x14 x15 x16 x17
              (SHR PB) (Z_to_bv 64 PB) x20 (Z_to_bv 64 (PB + 16)) (Z_to_bv 64 ns) (SHR (PB + 8)) (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr)
              (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84b20) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX L4 NS HG ROOM. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    pose proof INT_MAX_eq as IME.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (stack_shb0 mm (PB + 56) SSZ ltac:(lia)) as Z56. asan_chk Z56. clear Z56.
    zstep. zstep. sepM. if_cases Kd; zify_cond Kd; [exfalso; unfold AREALLOC in Kd; lia|]. clear Kd.
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AREALLOC)) with (wz AREALLOC) by (unfold wz, AREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_realloc Q PVL); [exact CTXX| exact NS| exact HG| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> RES).
    replace (ret_pc (Z_to_bv 64 0x84b44)) with (Z_to_bv 64 0x84b44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RES as [[-> FF] | (Bn & bs' & -> & BLO & BHI & CTX2 & FRX2)].
    - (* [comment removed for export] *)
      (nelimp FF 15%nat; intros FRX2 HL2 ERR2 MI2 PVA2 CHN2 CC2 GM2 TV2 SSZ2 HP2 PBS2 HB2 HNP2 NPX2).
      (nelimp FRX2 3%nat; intros SAVW2 LOC2 _).
      (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC2, L4. cbn in L4.
      injection L4 as E4. subst w4. cbn [map] in LOC2.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
      zstep. zstep. zstep.
      pose proof (stack_shb0 m2 (PB + 48) SSZ2 ltac:(lia)) as Z48. asan_chk Z48. clear Z48.
      pose proof (stack_shb0 m2 PB SSZ2 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
      apply evt_done. cbv beta.
      eapply (pv_fail_free' Q PVL FLAGLOW MEMSET). exact FF.
    - (* [comment removed for export] *)
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BLO. bandM. sepM.
      (nelimp CTX2 9%nat; intros _ _ _ _ _ _ _ MI2 _).
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
      apply evt_done. cbv beta.
      eapply litF_commit; [exact CTX2| exact FRX2| exact L4| exact ROOM].
  Qed.

  (* [comment removed for export] *)
  Lemma litF_mid : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx
      (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    (len = 0 \/ off < len) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) x11 (Z_to_bv 64 len) x13 x14 x15 x16 x17
              (SHR PB) (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 8)) x21 x22 (SHR (PB + 8)) (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr)
              (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x83e18) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX OFFLEN. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    pose proof INT_MAX_eq as IME.
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(SA, SA + 72)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    destruct (pvx_loc_store Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 [w0; w1; w2; w3; Z_to_bv 64 Fr; w5; w6; w7; w8] CTX FRX MU WM
                ltac:(lazymatch goal with H : mem_inv asegs m2 |- _ => exact H end)
                ltac:(cbn [map]; lazymatch goal with H : rw_cells asegs m2 SA _ |- _ => exact H end) eq_refl) as [CTX2 FRX2].
    assert (L4 : nth_error [w0; w1; w2; w3; Z_to_bv 64 Fr; w5; w6; w7; w8] 4 = Some (Z_to_bv 64 Fr)) by reflexivity.
    assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX2)))))))))))).
    clear MU WM.
    zstep. zstep. zstep.
    pose proof (stack_shb0 m2 (PB + 16) SSZ2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep.
    zstep. if_cases Kr; zify_cond Kr.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (stack_shchk m2 (PB + 32) 4 SSZ2 ltac:(lia)) as CK4. asan_chk CK4.
      zstep. rewrite (sx32_lit 0) by lia. zstep. if_false.
      zstep. zstep. if_cases K30; zify_cond K30.
      + (* [comment removed for export] *)
        rewrite Z.shiftr_div_pow2 in K30 by lia. change (2^30) with 1073741824 in K30.
        zstep. apply evt_done. cbv beta.
        eapply lscps_eq; [| eapply (litF_grow m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb shp Fx fcx (2 * (off + 7)));
                            [split; [exact CTX2| exact FRX2]| exact L4| lia| lia| lia]].
        steq.
      + zstep. zstep. if_cases K31; zify_cond K31.
        * (* [comment removed for export] *)
          apply evt_done. cbv beta. eapply (pv_ret0_924 Q PVL FLAGLOW); [eapply (pvx_exit0 Q PVL); split; [exact CTX2| exact FRX2]| exact L4].
        * rewrite Z.shiftr_div_pow2 in K30, K31 by lia. change (2^30) with 1073741824 in K30. change (2^31) with 2147483648 in K31.
          zstep. zstep. zstep. apply evt_done. cbv beta.
          eapply lscps_eq; [| eapply (litF_grow m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb shp Fx fcx INT_MAX);
                              [split; [exact CTX2| exact FRX2]| exact L4| lia| lia| lia]].
          steq.
    - (* [comment removed for export] *)
      zstep. apply evt_done. cbv beta.
      eapply litF_copy; [split; [exact CTX2| exact FRX2]| exact L4| lia].
  Qed.

  (* [comment removed for export] *)
  Theorem pv_false_case : pv_case_at PV_FALSE_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros CTXX. lits. bandM. sepM. unfold CASE_ST, PVPOST, PV_FALSE_ENTRY, ASHBASE, SHR.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep.
    pose proof (stack_shb0 mm PB SSZ ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
    zstep. zstep. zstep.
    pose proof (stack_shb0 mm (PB + 8) SSZ ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta. eapply lscps_eq; [| eapply litF_mid; [exact CTXX| left; exact Kl]]. steq.
    - zstep. zstep. zstep.
      pose proof (stack_shb0 mm (PB + 16) SSZ ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep. if_cases Ko; zify_cond Ko.
      + (* [comment removed for export] *)
        apply evt_done. cbv beta. eapply (pv_ret0_930 Q PVL FLAGLOW). eapply (pvx_exit0 Q PVL). exact CTXX.
      + apply evt_done. cbv beta. eapply lscps_eq; [| eapply litF_mid; [exact CTXX| right; lia]]. steq.
  Qed.
End LITF.


End CeilWrap.
