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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_cases.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_lits.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_numK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_numC.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_numB1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_numB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fmt_glue.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pv_numA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_lits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numK OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numC OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numB1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue.ICPT_fmt_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.NumFacts_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

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
Lemma dfin_of_test : forall vd : word,
  Z.shiftr (bv_unsigned (fabs_d vd)) 52 < 2047 -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047.
Proof.
  intros vd H. unfold fabs_d in H. rewrite Z_to_bv_unsigned in H.
  pose proof (bv_unsigned_in_range 64 vd) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite Z.land_ones in H by lia. unfold bv_wrap in H. change (bv_modulus 64) with (2^64) in H.
  rewrite (Z.mod_small (bv_unsigned vd mod 2^63) (2^64)) in H by (pose proof (Z.mod_pos_bound (bv_unsigned vd) (2^63)); lia).
  rewrite Z.shiftr_div_pow2 in H by lia. rewrite (Z.mod_small (bv_unsigned vd) (2^64)) by lia.
  Z.div_mod_to_equations. lia.
Qed.

Section NUMA.
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
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.

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

  Theorem pv_num_case : pv_case_at PV_NUM_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros [CTX FRX]. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold CASE_ST, PVPOST, PV_NUM_ENTRY, CJ_pv_cases.ASHBASE, SHR.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHN0 PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND0 TY PT SV SK CHC CHN' EB).
    assert (PINB : In (p, 64) B) by (rewrite EB; left; reflexivity).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (PIN : In (p, 64) LB1) by (apply HLR, BLR, PINB).
    pose proof (pvm_node Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND0 (node_cells_size _ _ _ _ _ _ _ _ _ _) PINB) as ND.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL PIN) 4%nat; intros Q1 Q2 _ Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
    unfold node_cells, wz in ND.
    (* [comment removed for export] *)
    (nelim (nfr_of_pvfr Q _ _ _ _ _ _ FRX) 8%nat; intros j0 nb j1 j2 t j3 NF _).
    (nelimp NF 16%nat; intros SAVW LOC LL PAD ST HDR P0 P1' P2 P3 P4 P5 SHC L16 FRM FA).
    unfold SHCV, SHCW, SHP_IDLE in SHC. cbn [map] in SHC. unfold FHDR in HDR.
    clear FRX ERR PBS1 ARR.
    pose_blk_band HL PIN.   (* [comment removed for export] *)
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ p 48 HL PIN ltac:(lia) ltac:(lia) ltac:(reflexivity)) as Z48. asan_chk Z48. clear Z48.
    zstep. step. zstep.
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    sepM. do 4 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
    zstep. zstep. zstep. replace (bv_unsigned (zb 0)) with 0 by reflexivity.
    change (Z_to_bv 64 341468) with (Z_to_bv 64 AASANMEMSET).
    assert (OWN : Forall (pv_own_iv Q) [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)])
      by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    assert (CTX1 : NUMX Q dep m1 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM0 (bvmap_set 8 vd Fx) fcx).
    { split.
      - eapply (pvm_wext0 Q PVL); [exact CTX| exact MU| exact WM| exact MI1|].
        constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
      - unfold NFR, FHDR, SHCV, SHCW, SHP_NUM0. cbn [map].
        split; [exact SAVW|]. split; [exact LOC|]. split; [exact LL|]. split; [exact PAD|]. split; [exact ST|]. split; [exact HDR|].
        split; [exact P0|]. split; [exact P1'|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
        split; [exact SHC|]. split; [reflexivity|]. split; [exact FRM|]. apply FAG18_set; [exact FA| cbv; first [reflexivity| lia]]. }
    clear MU WM OWN SAVW LOC PAD ST HDR P0 P1' P2 P3 P4 P5 SHC ND.
    eapply evt_cut. { eapply (num_memset26 Q PVL MEMSET); [exact CTX1| reflexivity]. }
    cbv beta. intros ms' PO.
    (nelim PO 17%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> [CTX2 FRX2]).
    replace (ret_pc (Z_to_bv 64 0x844c8)) with (Z_to_bv 64 0x844c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelimp CTX2 9%nat; intros HL2 _ _ _ _ _ _ MI2 _).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x844cc)) with (Z_to_bv 64 0x844cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL2 (SH ALCONV) ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, ALCONV; cbn; lia)) as LSH.
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL2 (SH ADOTSTR) ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, ADOTSTR; cbn; lia)) as DSH.
    change (SH ALCONV) with 2147533763 in LSH. change (SH ADOTSTR) with 2147461204 in DSH. unfold zb in LSH, DSH.
    replace (RT_data.alowsh 2147533763) with 0 in LSH by (vm_compute; reflexivity).
    replace (RT_data.alowsh 2147461204) with 0 in DSH by (vm_compute; reflexivity).
    (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL2) 4%nat; intros _ _ _ LCV).
    change (cells_at asegs m2 ALCONV [C8 (wz ADOTSTR)]) with (ro_cells asegs m2 ALCONV [C8 (wz ADOTSTR)]) in LCV. unfold ALCONV, ADOTSTR, wz in LCV.
    zstep. zstep. zstep. zstep. if_false.
    zstep.
    zstep. zstep. zstep. try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
    zstep. zstep.
    (* [comment removed for export] *)
    (nelimp FRX2 16%nat; intros SAVW LOC _ PAD ST HDR P0 P1' P2 P3 P4 P5 SHC _ _ FA2).
    unfold SHCV, SHCW, SHP_NUM0 in SHC. cbn [map] in SHC. unfold FHDR in HDR.
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16); (Fr + 96, Fr + 104)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    sbstep.
    step. step. zstep. zstep.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
    assert (CTX4 : NUMX Q dep m4 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 (repeat (Z_to_bv 8 0) 26) j1 j2 (Z_to_bv 64 0) j3 SHP_NUM
                     (bvmap_set 8 vd (bvmap_set 9 (fabs_d vd) Fx)) fcx).
    { split.
      - eapply (pvm_wext0 Q PVL); [exact CTX2| exact MU| exact WM| exact MI4|].
        constructor; [unfold pv_wiv0; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
      - unfold NFR, FHDR, SHCV, SHCW, SHP_NUM. cbn [map].
        split; [exact SAVW|]. split; [exact LOC|]. split; [exact LL|]. split; [exact PAD|]. split; [exact ST|]. split; [exact HDR|].
        split; [exact P0|]. split; [exact P1'|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
        split; [exact SHC|]. split; [reflexivity|]. split; [exact FRM|].
        apply FAG18_set; [apply FAG18_set; [exact FA| cbv; first [reflexivity| lia]]| cbv; first [reflexivity| lia]]. }
    clear MU WM SAVW LOC PAD ST HDR P0 P1' P2 P3 P4 P5 SHC LSH DSH LCV.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta.
      eapply (num_B Q PVL ENS FLAGLOW FMTF FMTL SPRD SPRG15 SPRG17 SSC GRET GLEN25 GFACTS GTOT DTOT SJUNK); [exact CTX4| exact ND0| exact PINB| intros r Hr; apply freg_get_same; rewrite Hr; reflexivity| exact (dfin_of_test vd K0)].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      change (Z_to_bv 64 340288) with (Z_to_bv 64 AASANMEMCPY). change (Z_to_bv 64 135616) with (Z_to_bv 64 LIT_NULL).
      eapply evt_cut. { eapply (num_memcpy_null Q PVL MEMCPY); [exact CTX4| reflexivity]. }
      cbv beta. intros ms' PO.
      (nelim PO 17%nat; intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 -> CTX5).
      replace (ret_pc (Z_to_bv 64 0x84528)) with (Z_to_bv 64 0x84528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof CTX5 as [(_ & _ & _ & _ & _ & _ & _ & MI5 & _) _].
      zstep. zstep. apply evt_done. cbv beta.
      eapply (num_E Q PVL ENS FLAGLOW); [exact CTX5| lia].
  Qed.
End NUMA.


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
End CJ_pv_numA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_str.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_str.CJ_pv_pro.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_litF CJ_pv_litT CJ_pv_litN CJ_pv_str CJ_pv_numK CJ_pv_numC CJ_pv_numB1 CJ_pv_numB.
Import CJ_pv_numA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Section TOP.
  Variables (AI : art_iface) (TI : trs_iface).
  (* [comment removed for export] *)
  Definition CASEH (E : Z) : Prop :=
    forall Q, q_ai Q = AI -> q_ti Q = TI -> pvl Q -> (forall d, (d < q_n Q)%nat -> print_value_at AI TI d) -> pv_case_at E Q.

  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis PSTR : pstr_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.
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
  (* [comment removed for export] *)
  Hypothesis ARR : CASEH PV_ARR_ENTRY.
  Hypothesis OBJ : CASEH PV_OBJ_ENTRY.

  Lemma case_false : CASEH PV_FALSE_ENTRY.
  Proof. intros Q EA ET PVL REC. apply (pv_false_case Q PVL); [rewrite EA; exact FLAGLOW| exact MEMSET| exact MEMCPY]. Qed.
  Lemma case_true : CASEH PV_TRUE_ENTRY.
  Proof. intros Q EA ET PVL REC. apply (pv_true_case Q PVL); [rewrite EA; exact FLAGLOW| exact MEMSET| exact MEMCPY]. Qed.
  Lemma case_null : CASEH PV_NULL_ENTRY.
  Proof. intros Q EA ET PVL REC. apply (pv_null_case Q PVL); [rewrite EA; exact FLAGLOW| exact MEMSET| exact MEMCPY]. Qed.
  Lemma case_str : CASEH PV_STR_ENTRY.
  Proof. intros Q EA ET PVL REC. apply (pv_str_case Q PVL); [rewrite EA, ET; exact PSTR| rewrite EA; exact FLAGLOW]. Qed.
  Lemma case_num : CASEH PV_NUM_ENTRY.
  Proof.
    intros Q EA ET PVL REC.
    apply (pv_num_case Q PVL); rewrite ?EA, ?ET;
      first [ exact ENS | exact FLAGLOW | exact MEMSET | exact MEMCPY | exact FMTF | exact FMTL | exact SPRD | exact SPRG15 | exact SPRG17
            | exact SSC | exact GRET | exact GLEN25 | exact GFACTS | exact GTOT | exact DTOT | exact SJUNK ].
  Qed.

  Theorem print_value_spec : print_value_stmt AI TI.
  Proof.
    unfold print_value_stmt. intros n. induction n as [n IH] using lt_wf_ind.
    apply (pv_entry AI TI case_false case_true case_null case_num case_str ARR OBJ n). exact IH.
  Qed.
End TOP.


End CeilWrap.
