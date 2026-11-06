(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv ICPT_iface ICPT_musl ICPT_pcdefs ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fmt_glue.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue.ICPT_fmt_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK CJ_pv_numC CJ_pv_numB1.
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
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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

Section NUMB.
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
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis FMTF : fmt_facts_stmt AI.
  Hypothesis FMTL : fmt_lits_stmt AI.
  Hypothesis SPRD : asprintf_d_stmt_b.
  Hypothesis SPRG15 : asprintf_g_stmt_b 15.
  Hypothesis SPRG17 : asprintf_g_stmt_b 17.
  Hypothesis SSC : asscanf_lg_stmt_b.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.
  Local Notation ASHBASE := CJ_pv_cases.ASHBASE.

  (* [comment removed for export] *)
  Definition BST (pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) x21 (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Lemma num_AF8 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx -> 0 <= r < 2^63 ->
    LSCPS asegs POST (BST 0x8488c x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX Hr. lits. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [(_ & _ & _ & _ & _ & _ & _ & MI & _) _].
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
    eapply (num_L Q PVL ENS FLAGLOW); [exact CTXX| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G17 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (vd : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    LSCPS asegs POST (BST 0x84878 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 vd x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX DFIN. lits. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [(_ & _ & _ & _ & _ & _ & _ & MI & _) _].
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 135808) with (Z_to_bv 64 (if 17 =? 15 then A_FMT_g15 else A_FMT_g17)).
    eapply evt_cut. { eapply (num_call_g Q PVL FMTF FMTL SPRG15 SPRG17 GRET GLEN25 GFACTS GTOT 17); [exact CTXX| right; reflexivity| exact DFIN]. }
    cbv beta. intros ms' PO.
    (nelim PO 25%nat; intros o r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> CTX2 Er Hr OG HF).
    replace (ret_pc (Z_to_bv 64 0x8488c)) with (Z_to_bv 64 0x8488c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta. eapply num_AF8; [exact CTX2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma numx_fp : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx Fy fcy,
    NUMX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx ->
    frm0 fcy -> FAG18 F Fy ->
    NUMX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fy fcy.
  Proof.
    intros until fcy. intros [CTX FRX] FRM' FA'. split; [exact CTX|].
    (nelim FRX 16%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 _ _).
    unfold NFR. repeat (split; [assumption|]). exact FA'.
  Qed.

  (* [comment removed for export] *)
  Lemma num_C : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (vd : word) (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> 0 <= r <= 25 ->
    LSCPS asegs POST (BST 0x84848 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) vd x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX DFIN Hr. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros _ _ _ _ _ _ _ MI _).
    (nelimp FRX 16%nat; intros SAVW LOC LL PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    (* [comment removed for export] *)
    assert (TAIL : forall (Fy : bvmap 5 word) (fcy : bv 32) (x10' : word), frm0 fcy -> FAG18 F Fy ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo1 g1)
        (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10' x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) vd (Z_to_bv 64 Fr) (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            Fy (Z_to_bv 64 0x8485c) fcy None mm (seg_rom asegs))).
    { intros Fy fcy x10' FRMy FAy.
      step. step. step. step. step. step.
      step; rewrite bword_nez; if_cases K.
      - (* [comment removed for export] *)
        apply evt_done. cbv beta. eapply (num_L Q PVL ENS FLAGLOW); [| lia].
        eapply numx_fp; [exact CTXX| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FAy].
      - apply evt_done. cbv beta. eapply num_G17; [| exact DFIN].
        eapply numx_fp; [exact CTXX| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FAy]. }
    clear SAVW LOC PAD ST HDR P0 P1 P2 P3 P5 SHC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    step. step. step.
    step; rewrite bword_nez; if_cases K.
    - eapply TAIL; [assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA].
    - step. eapply TAIL; [assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA].
  Qed.

  (* [comment removed for export] *)
  Lemma num_S : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 (o : list Z) (rest : list byte) j1 j2 t j3 Fx fcx (vd : word) (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: rest) j1 j2 t j3 SHP_NUM Fx fcx ->
    Forall num_gch o -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> 0 <= r <= 25 ->
    LSCPS asegs POST (BST 0x84828 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x21 vd x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX OG DFIN Hr. lits. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [(_ & _ & _ & _ & _ & _ & _ & MI & _) _].
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 271620) with (Z_to_bv 64 ASSCANF_T). change (Z_to_bv 64 135776) with (Z_to_bv 64 A_FMT_lg).
    eapply evt_cut. { eapply (num_call_scan Q PVL FMTF FMTL SSC SJUNK); [exact CTXX| exact OG| reflexivity]. }
    cbv beta. intros ms' PO.
    (nelim PO 23%nat; intros rr tw errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' -> CTX2 HF).
    replace (ret_pc (Z_to_bv 64 0x84840)) with (Z_to_bv 64 0x84840) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof CTX2 as [(_ & _ & _ & _ & _ & _ & _ & MI2 & _) _].
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta. eapply num_G17; [exact CTX2| exact DFIN].
    - apply evt_done. cbv beta. eapply num_C; [exact CTX2| exact DFIN| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G15 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (vd : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    (forall r : bv 5, bv_unsigned r = 8 -> reg_get Fx r = vd) -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    LSCPS asegs POST (BST 0x84810 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX F8 DFIN. lits. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [(_ & _ & _ & _ & _ & _ & _ & MI & _) _].
    eapply lscps_step_evt. cbv beta delta [mkR]. step.
    match goal with |- context [reg_get Fx ?r] => rewrite (F8 r ltac:(reflexivity)) end.
    zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 135744) with (Z_to_bv 64 (if 15 =? 15 then A_FMT_g15 else A_FMT_g17)).
    eapply evt_cut. { eapply (num_call_g Q PVL FMTF FMTL SPRG15 SPRG17 GRET GLEN25 GFACTS GTOT 15); [exact CTXX| left; reflexivity| exact DFIN]. }
    cbv beta. intros ms' PO.
    (nelim PO 25%nat; intros o r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> CTX2 Er Hr OG HF).
    replace (ret_pc (Z_to_bv 64 0x84828)) with (Z_to_bv 64 0x84828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    assert (L26 : length (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: skipn (S (length o)) nb) = 26%nat)
      by (destruct CTX2 as [_ (_ & _ & _ & _ & _ & _ & _ & P1 & _)]; destruct P1 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    eapply num_S; [exact CTX2| exact OG| exact DFIN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_D : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    LSCPS asegs POST (BST 0x847d4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31 Fx fcx mm) mo1 g1.
  Proof.
    intros until x31. intros CTXX. lits. bandM. sepM. unfold BST, SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [(_ & _ & _ & _ & _ & _ & _ & MI & _) _].
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 135712) with (Z_to_bv 64 A_FMT_d).
    eapply evt_cut. { eapply (num_call_d Q PVL FMTF FMTL SPRD DTOT); exact CTXX. }
    cbv beta. intros ms' PO.
    (nelim PO 25%nat; intros o r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> CTX2 Er Hr OG HF).
    replace (ret_pc (Z_to_bv 64 0x8488c)) with (Z_to_bv 64 0x8488c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta. eapply num_AF8; [exact CTX2| lia].
  Qed.

  (* [comment removed for export] *)
  Definition num_fin_stmt : Prop :=
    forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx
           (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
      rw_cells asegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (p, 64) B ->
      (forall r : bv 5, bv_unsigned r = 8 -> reg_get Fx r = vd) -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
      LSCPS asegs POST
        (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 CJ_pv_cases.ASHBASE) x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x847b0) fcx None mm (seg_rom asegs)) mo1 g1.

  (* [comment removed for export] *)
  Theorem num_B : num_fin_stmt.
  Proof.
    unfold num_fin_stmt. intros until x31. intros CTXX ND0 PINB F8 DFIN. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP _ _ _ _ _ MI _).
    (nelimp FRX 16%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRM FA).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (PIN : In (p, 64) LB1) by (apply HLR, BLR, PINB).
    assert (CTXd : PVM Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs) by exact CTX.
    pose proof (pvm_node Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTXd ND0 (node_cells_size _ _ _ _ _ _ _ _ _ _) PINB) as ND.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL PIN) 4%nat; intros Q1 Q2 _ Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
    unfold node_cells, wz in ND.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ p 40 HL PIN ltac:(lia) ltac:(lia) ltac:(reflexivity)) as Z40. asan_chk Z40. clear Z40.
    zstep. step. step.
    step; if_cases K.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta. eapply num_G15; [| | exact DFIN].
      + eapply numx_fp; [exact CTXX| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA].
      + intros r Hr. rewrite freg_get_other; [apply F8; exact Hr| unfold bv_eqb; rewrite Hr; reflexivity].
    - apply evt_done. cbv beta. eapply num_D.
      eapply numx_fp; [exact CTXX| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA].
  Qed.
End NUMB.


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
