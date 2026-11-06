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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_arr.CJ_pv_arrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_arr.CJ_pv_arrB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_objC.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_objC.CJ_pv_objA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_objC.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_objC.CJ_pv_objB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_objC ICPT_iface.
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
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr bsegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section OBJ.
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
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis REC : forall d, (d < n)%nat -> print_value_at AI TI d.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.


  Hypothesis PSTR : pstr_stmt AI TI.


  Ltac steq := unfold CASE_ST, OST, mkR, SHR, ASHBASE; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac land7 x := replace (Z.land x 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  Ltac uguard := let G := fresh "G" in zstep; if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|]; clear G.

  Theorem pv_obj_case : pv_case_at PV_OBJ_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros CTXX. lits. bandM. sepM. unfold CASE_ST, PVPOST, PV_OBJ_ENTRY, ASHBASE, SHR.
    assert (FZR : 0 <= Z.b2z (fz Q) <= 1) by (destruct (fz Q); cbn; lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHN0 PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn En ND TY _ SV SK CHC CHNX EB).
    assert (PIN : In (p, 64) B) by (rewrite EB; left; reflexivity).
    assert (SUBC : forall b, In b Bcc -> In b B). { intros b Hb. rewrite EB. right. rewrite !in_app_iff. right; right; left. exact Hb. }
    destruct (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND PIN) as (NDm & _ & (C1 & C2 & _ & C4) & PIN1).
    unfold node_cells, wz in NDm. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CH0 _ CH2).
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA, SA + 72)] mm) as MU. pose proof (wmono_refl bsegs mm) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    destruct (pvx_loc_store Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 [w0; w1; Z_to_bv 64 Fr; w3; w4; w5; w6; w7; w8] CTX FRX MU WM
                ltac:(lazymatch goal with H : mem_inv bsegs m0 |- _ => exact H end)
                ltac:(cbn [map]; lazymatch goal with H : rw_cells bsegs m0 SA _ |- _ => exact H end) eq_refl) as [CTX0 FRX0].
    clear MU WM LOC PBS1 ARR.
    (nelimp CTX0 13%nat; intros HL0 HP0 PBS0 _ _ _ _ MI0 _ _ _ SSZ0 _). unfold PBS, wz in PBS0.
    (nelimp FRX0 3%nat; intros _ LOC0 _). cbn [map] in LOC0.
    destruct (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 ND PIN) as (ND0 & _).
    unfold node_cells, wz in ND0.
    pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ p 16 HL0 (proj2 (proj2 (proj2 (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 ND PIN)))) ltac:(lia) ltac:(lia) eq_refl) as SH16.
    (* [comment removed for export] *)
    zstep. zstep. zstep. asan_chk SH16.
    zstep. land7 (q_PB Q). zstep. if_cases G; zify_cond G; [exfalso; lia|]. clear G.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA, SA + 72)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    zstep. zstep. zstep. zstep. zstep.
    pose proof (stack_shb0 m0 (PB + 36) SSZ0 ltac:(lia)) as Z36. asan_chk Z36.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (pvx_loc_store Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8] CTX0 FRX0 MU WM
                ltac:(lazymatch goal with H : mem_inv bsegs m1 |- _ => exact H end)
                ltac:(unfold SHR; cbn [map]; lazymatch goal with H : rw_cells bsegs m1 SA _ |- _ => exact H end) eq_refl) as [CTX1 FRX1].
    assert (OLC1 : OBJ_LOCC Q [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8]) by (split; [reflexivity| split; reflexivity]).
    clear MU WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    fold (fz Q).
    replace (Z.lxor (Z.b2z (fz Q)) 3) with (3 - Z.b2z (fz Q)) by (destruct (fz Q); reflexivity).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [split; [exact CTX1| exact FRX1]| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO. clear NDm ND0 SH16 Z36 SSZ SSZ0 MI PVA CC CTX0 FRX0 PBS0 MI0 HL0 HP0. try clear ERR.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84198)) with (Z_to_bv 64 0x84198) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    { eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_ret0_c2c Q PVL FLAGLOW); [exact EX| reflexivity]. }
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 9%nat; intros HLb HPb PBSb ARRb LENb PNb _ MIb _). (nelimp FRXb 3%nat; intros _ LOC _).
    (nelimp PNb 3%nat; intros PNb1 PNb2 PNb3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros Y1 Y2 Y3 Y4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) as [_ SOB].
    pose proof (shadow_ok_shchk1 m2 buf' len' (buf' + off) SOB ltac:(lia)) as CK0.
    cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSb.
    (* [comment removed for export] *)
    pose proof (munch_refl [(buf' + off, buf' + off + 1)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    zstep. uguard.
    zstep. zstep. sepM. asan_chk CK0.
    zstep. zstep. sepM. ustore_at buf' off (buf' + off) 0 (wb 123) ltac:(reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    assert (CTX3 : PVX Q dep m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd bs' (Z.to_nat (off + 0)) (wb 123)) [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8] jb SHP_IDLE Fx fcx).
    { eapply (pvx_out_store Q PVL) with (W := [(buf' + off, buf' + off + 1)]);
        [exact CTX2| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRb| rewrite upd_length; reflexivity]. }
    clear MU WM CTX2 CTXb FRXb HLb SSZb SOB. try clear CK0.
    pose proof CTX3 as [CTXc FRXc]. (nelimp CTXc 9%nat; intros HLc HPc PBSc ARRc LENc _ _ MIc _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
    unfold PBS, wz in PBSc.
    (* [comment removed for export] *)
    pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
    zstep. zstep.
    pose proof (stack_shb0 m3 (PB + 24) SSZc ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. sepM. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    assert (CTX4 : PVX Q (dep + 1) m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd bs' (Z.to_nat (off + 0)) (wb 123)) [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8] jb SHP_IDLE Fx fcx).
    { split.
      - eapply (pvm_dep_store Q PVL dep (dep + 1)); [exact CTXc| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. lazymatch goal with H : rw_cells bsegs m4 PB _ |- _ => exact H end.
      - eapply (pvfr_wext Q PVL); [exact FRXc| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
    clear MU WM CTX3 CTXc FRXc HLc PBSc SSZc Z24.
    pose proof CTX4 as [CTXd FRXd]. (nelimp CTXd 9%nat; intros HLd HPd PBSd ARRd LENd _ _ MId _). (nelimp FRXd 3%nat; intros _ LOCd _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXd)))))))))))) as SSZd.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLd (perm_in_head _ _ _ HPd)) as [_ SOBd].
    cbn [map] in LOCd. unfold SHR, ASHBASE in LOCd. unfold PBS, wz in PBSd.
    (* [comment removed for export] *)
    zstep. pose proof (stack_shb0 m4 (PB + 36) SSZd ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep.
    assert (JN : forall mq bsq (x10q x11q x12q : word),
      PVX Q (dep + 1) mq mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bsq [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8] jb SHP_IDLE Fx fcx ->
      LSCPS bsegs POST
        (MS (mkR (Z_to_bv 64 0x84198) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) x10q x11q x12q a3' a4' a5' a6' a7'
                (Z_to_bv 64 (Z.b2z (fz Q))) (Z_to_bv 64 PB) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (PB + 24) 3 + 2147450880)) (Z_to_bv 64 ch) x23 x24 (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 (PB + 24)) t3' t4' t5' t6')
            Fx (Z_to_bv 64 0x84218) fcx None mq (seg_rom bsegs)) mo2 g2).
    { intros mq bsq x10q x11q x12q CTXq. clear ARRd PBSd LOCd SSZd Z36 SOBd MId.
      pose proof CTXq as [CTXe FRXe]. (nelimp CTXe 9%nat; intros HLe HPe PBSe _ _ PNe _ MIe _). (nelimp FRXe 3%nat; intros _ LOCe _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXe)))))))))))) as SSZe.
      cbn [map] in LOCe. unfold SHR, ASHBASE in LOCe. unfold PBS, wz in PBSe.
      pose proof (munch_refl [(PB, PB + 32); (SA, SA + 72)] mq) as MU. pose proof (wmono_refl bsegs mq) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep. zstep.
      pose proof (stack_shb0 mq (PB + 16) SSZe ltac:(lia)) as Z16. asan_chk Z16.
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
      assert (CTX5 : PVX Q (dep + 1) m5 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' (off + (2 - Z.b2z (fz Q))) bsq
                         [w0; w1; Z_to_bv 64 Fr; w3; Z_to_bv 64 (PB + 16); Z_to_bv 64 (PB + 36); SHR (PB + 16); SHR (PB + 36); w8] jb SHP_IDLE Fx fcx).
      { eapply (pvx_sl_store Q PVL (dep + 1) (dep + 1)) with (W := [(PB, PB + 32); (SA, SA + 72)]);
          [exact CTXq| exact MU| exact WM| assumption| | | lia| lia| | reflexivity].
        - constructor; [unfold sl_wiv; cbn [fst snd]; lia|]. constructor; [unfold sl_wiv; cbn [fst snd]; lia| constructor].
        - unfold PBS, wz. lazymatch goal with H : rw_cells bsegs m5 PB _ |- _ => exact H end.
        - unfold SHR. cbn [map]. lazymatch goal with H : rw_cells bsegs m5 SA _ |- _ => exact H end. }
      clear MU WM CTXq CTXe FRXe HLe PBSe SSZe Z16.
      (* [comment removed for export] *)
      zstep. if_cases Kch; zify_cond Kch.
      { assert (E0 : ch = 0) by lia. rewrite E0 in *.
        apply evt_done. cbv beta. eapply (obj_close Q PVL ENS FLAGLOW); [exact CTX5| split; [reflexivity| split; reflexivity]]. }
      assert (CHNZ : ch <> 0) by lia.
      pose proof CTX5 as [CTXf FRXf]. (nelimp CTXf 9%nat; intros _ _ PBSf _ _ _ _ MIf _). (nelimp FRXf 3%nat; intros _ LOCf _).
      cbn [map] in LOCf. unfold SHR, ASHBASE in LOCf. unfold PBS, wz in PBSf.
      pose proof (munch_refl [(SA, SA + 72)] m5) as MU. pose proof (wmono_refl bsegs m5) as WM.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
      lazymatch goal with H : rw_cells bsegs m6 SA ?cs |- _ => rename H into LOC6 end.
      apply evt_done. cbv beta.
      lazymatch type of LOC6 with rw_cells _ _ _ [C8 ?v0; C8 ?v1; C8 ?v2; C8 ?v3; C8 ?v4; C8 ?v5; C8 ?v6; C8 ?v7; C8 ?v8] =>
        assert (CTX6 : PVX Q (dep + 1) m6 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' (off + (2 - Z.b2z (fz Q))) bsq [v0; v1; v2; v3; v4; v5; v6; v7; v8] jb SHP_IDLE Fx fcx)
      end.
      { eapply (pvx_sl_store Q PVL (dep + 1) (dep + 1)) with (W := [(SA, SA + 72)]);
          [exact CTX5| exact MU| exact WM| assumption| | | lia| lia| cbn [map]; exact LOC6| reflexivity].
        - constructor; [unfold sl_wiv; cbn [fst snd]; lia| constructor].
        - unfold PBS, wz. lazymatch goal with H : rw_cells bsegs m6 PB _ |- _ => exact H end. }
      pose proof (obj_iter Q PVL ENS STRLEN REC FLAGLOW PSTR (length Bcc) d0 ch Bcc ltac:(lia) ltac:(lia) CHC CHNZ SUBC) as K.
      unfold OKAT, OST, SHR, ASHBASE in K. eapply K; [exact CTX6|].
      unfold OBJ_LOC. unfold SHR, ASHBASE. repeat split; reflexivity. }
    zstep. if_cases Kf; zify_cond Kf.
    - (* [comment removed for export] *)
      assert (Efz : fz Q = true) by (unfold fz; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia).
      rewrite Efz in *. cbn [Z.b2z] in *.
      apply evt_done. cbv beta. eapply JN. exact CTX4.
    - assert (Efz : fz Q = false) by (unfold fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia).
      rewrite Efz in *. cbn [Z.b2z] in *.
      pose proof (shadow_ok_shchk1 m4 buf' len' (buf' + off + 1) SOBd ltac:(lia)) as CK1.
      pose proof (munch_refl [(buf' + off + 1, buf' + off + 2)] m4) as MU. pose proof (wmono_refl bsegs m4) as WM.
      zstep. zstep. uguard.
      zstep. zstep. sepM. asan_chk CK1.
      zstep. sepM. ustore_at buf' off (buf' + off + 1) 1 (wb 10) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
      assert (CTX5 : PVX Q (dep + 1) m5 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd (upd bs' (Z.to_nat (off + 0)) (wb 123)) (Z.to_nat (off + 1)) (wb 10))
                       [w0; w1; Z_to_bv 64 Fr; w3; w4; Z_to_bv 64 (PB + 36); w6; SHR (PB + 36); w8] jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf' + off + 1, buf' + off + 2)]);
          [exact CTX4| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRd| rewrite !upd_length; reflexivity]. }
      apply evt_done. cbv beta. eapply JN. exact CTX5.
  Qed.
End OBJ.

(* [comment removed for export] *)
Theorem case_obj : forall (AI : art_iface) (TI : trs_iface),
  ensure_stmt AI TI -> strlen_icpt_spec -> art_flag_low_stmt AI -> asan_memset_spec -> pstr_stmt AI TI ->
  forall Q, q_ai Q = AI -> q_ti Q = TI -> pvl Q -> (forall d, (d < q_n Q)%nat -> print_value_at AI TI d) -> pv_case_at PV_OBJ_ENTRY Q.
Proof.
  intros AI TI ENS STRLEN FL MS PSTR Q EA ET PVL REC.
  apply (pv_obj_case Q PVL); rewrite ?EA, ?ET; first [exact ENS| exact STRLEN| exact REC| exact FL| exact MS| exact PSTR].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr bsegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
