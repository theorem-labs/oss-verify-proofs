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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pv_arrA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_lits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numK OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
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
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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

Section ARRA.
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ARR_LOC (loc : list word) : Prop :=
    nth_error loc 3 = Some (SHR (PB + 24)) /\ nth_error loc 4 = Some (Z_to_bv 64 Fr) /\ nth_error loc 5 = Some (Z_to_bv 64 (PB + 24))
    /\ nth_error loc 6 = Some (Z_to_bv 64 (PB + 36)) /\ nth_error loc 7 = Some (SHR PB).

  (* [comment removed for export] *)
  Definition ARR_LOCC (loc : list word) : Prop :=
    nth_error loc 3 = Some (SHR (PB + 24)) /\ nth_error loc 4 = Some (Z_to_bv 64 Fr) /\ nth_error loc 5 = Some (Z_to_bv 64 (PB + 24)).
  Lemma arr_locc_of : forall loc, ARR_LOC loc -> ARR_LOCC loc.
  Proof. intros loc nelH_; (nelim nelH_ 4%nat; intros A3 A4 A5 _). split; [exact A3| split; [exact A4| exact A5]]. Qed.
  Lemma arr_loc9c : forall loc, length loc = 9%nat -> ARR_LOCC loc ->
    exists w0 w1 w2 w6 w7 w8, loc = [w0; w1; w2; SHR (PB + 24); Z_to_bv 64 Fr; Z_to_bv 64 (PB + 24); w6; w7; w8].
  Proof.
    intros loc LL nelH_; (nelim nelH_ 3%nat; intros A3 A4 A5). (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 ->).
    cbn in A3, A4, A5. injection A3 as ->. injection A4 as ->. injection A5 as ->.
    exists w0, w1, w2, w6, w7, w8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_loc9 : forall loc, length loc = 9%nat -> ARR_LOC loc ->
    exists w0 w1 w2 w8, loc = [w0; w1; w2; SHR (PB + 24); Z_to_bv 64 Fr; Z_to_bv 64 (PB + 24); Z_to_bv 64 (PB + 36); SHR PB; w8].
  Proof.
    intros loc LL nelH_; (nelim nelH_ 5%nat; intros A3 A4 A5 A6 A7). (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 ->).
    cbn in A3, A4, A5, A6, A7. injection A3 as ->. injection A4 as ->. injection A5 as ->. injection A6 as ->. injection A7 as ->.
    exists w0, w1, w2, w8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_dep_store : forall depc depc' mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs mm',
    PVM Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    munch [(PB, PB + 32)] mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
    PBS Q mm' buf len off depc' -> 0 <= depc' ->
    PVM Q depc' mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs.
  Proof.
    intros until mm'. intros CTX MU WM MI' PBS2 HD. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (OWN : Forall (pv_own_iv Q) [(PB, PB + 32)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    unfold AERRNO, ATP in ERR. unfold PVM, PVMs.
    split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|]. split; [exact PBS2|].
    split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; dj]|]. split; [exact LEN|]. split; [unfold pb_nums; lia|].
    split; [eapply (rw_cells_transport asegs); [exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
    split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
    split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. cbn.
             (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
    split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
    split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
    destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
    split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
  Qed.

  (* [comment removed for export] *)
  Definition fr_wiv (iv : Z * Z) : Prop :=
    (PB <= fst iv /\ snd iv <= PB + 64)
    \/ (AIMG_HI <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv + 16 <= Fr \/ Fr + 128 <= fst iv - 16)
        /\ (snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv)).      (* [comment removed for export] *)

  Lemma pvfr_wext : forall mm loc jb shp Fx fcx W mm',
    PVFR Q mm loc jb shp Fx fcx -> munch W mm mm' -> wmono asegs mm mm' -> Forall fr_wiv W ->
    PVFR Q mm' loc jb shp Fx fcx.
  Proof.
    intros until mm'. intros FRX MU WM HW. lits. bandM. sepM.
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    assert (DJ : forall A k, (lo <= A /\ A + k <= SP) \/ (Fr <= A /\ A + k <= Fr + 128) \/ (KLOWSHADOW_BEG <= A /\ A + k <= KHIGHMEM_BEG) -> disjoint_from W A k).   (* [comment removed for export] *)
    { intros A k HA. apply disjoint_from_forall. eapply Forall_impl; [| exact HW]. intros [u v] Hiv. unfold fr_wiv in Hiv. cbn [fst snd] in *.
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. rewrite ?alloc_ceiling_eq in *. lia. }
    unfold PVFR. unfold SAVEDV, FHDR, FBODY, SHCV, SHCW in *.
    split; [eapply (rw_cells_transport asegs); [exact SAVW| exact MU| exact WM| apply DJ; cbn; lia]|].
    split; [eapply (rw_cells_transport asegs); [exact LOC| exact MU| exact WM| apply DJ; rewrite cells_size_mapC8, LL9; cbn; lia]|]. split; [exact LL9|].
    split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| apply DJ; lia]|].
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; lia]|].
    split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| apply DJ; cbn; lia]|].
    split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| apply DJ; cbn; lia]|].
    split; [eapply (rw_cells_transport asegs); [exact SHC| exact MU| exact WM| apply DJ; rewrite cells_size_mapC1, length_map, L16; pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; cbn; lia]|].   (* [comment removed for export] *)
    split; [exact L16|]. split; [exact FRM| exact FA].
  Qed.

  (* [comment removed for export] *)
  Lemma pvx_out_store : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx mm' bs' W,
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    munch W mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
    Forall (fun iv => buf <= fst iv /\ snd iv <= buf + len) W ->
    u8arr asegs mm' buf bs' -> length bs' = length bs ->
    PVX Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs' loc jb shp Fx fcx.
  Proof.
    intros until W. intros [CTX FRX] MU WM MI' HW ARR' LBS. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD buf len (perm_in_head _ _ _ HP)) as FDB.
    assert (DJ : forall A k, (A + k <= buf \/ buf + len <= A) -> disjoint_from W A k).
    { intros A k HA. apply disjoint_from_forall. eapply Forall_impl; [| exact HW]. intros [u v] [H1 H2]. cbn [fst snd] in *. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR R1 HA H1 H2). }
    unfold AERRNO, ATP in ERR.
    split.
    - eapply (pvm_wext Q PVL); [exact CTX| exact MU| exact WM| exact MI'| | | exact ARR'| exact LBS].
      + eapply Forall_impl; [| exact HW]. intros iv Hiv. unfold pv_wiv. do 4 right. exact Hiv.
      + eapply (rw_cells_transport asegs); [exact ERR| exact MU| exact WM|]. apply DJ. unfold AERRNO, ATP. cbn. lia.
    - eapply pvfr_wext; [exact FRX| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. intros [u v] [H1 H2]. unfold fr_wiv. cbn [fst snd] in *.
      right. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG. try rewrite alloc_ceiling_eq. (lia_on LBS PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO FHI SPR LEN R1 BR BMf0 FDB H1 H2).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_close : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> ARR_LOCC loc ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) x20 x21 x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x85064) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX ALC. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x85070)) with (Z_to_bv 64 0x85070) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    - (* [comment removed for export] *)
      pose proof EX as (FRX2 & _). (nelimp FRX2 4%nat; intros SAVW LOC LL _).
      (nelim (arr_loc9c loc LL ALC) 7%nat; intros w0 w1 w2 w6 w7 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR in LOC.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      apply evt_done. cbv beta.
      eapply (pv_epi' Q PVL FLAGLOW). exact EX.
    - (* [comment removed for export] *)
      pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 9%nat; intros HLb HPb _ ARRb LENb PNb _ MIb _).
      (nelimp FRXb 4%nat; intros _ LOC LL _).
      (nelim (arr_loc9c loc LL ALC) 7%nat; intros w0 w1 w2 w6 w7 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR in LOC.
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) as [_ SOB].
      pose proof (shadow_ok_shchk1 m2 buf' len' (buf' + off) SOB ltac:(lia)) as CK0.
      pose proof (shadow_ok_shchk1 m2 buf' len' (buf' + off + 1) SOB ltac:(lia)) as CK1.
      pose proof (munch_refl [(buf' + off, buf' + off + 2)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      zstep. zstep. asan_chk CK0.
      zstep. zstep.
      ustore_at buf' off (buf' + off) 0 (wb 93) ltac:(reflexivity).
      zstep. zstep. asan_chk CK1.
      ustore_at buf' off (buf' + off + 1) 1 (wb 0) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd (upd bs' (Z.to_nat (off + 0)) (wb 93)) (Z.to_nat (off + 1)) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(buf' + off, buf' + off + 2)]);
          [exact CTX2| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRb| rewrite !upd_length; reflexivity]. }
      clear MU WM CTXb FRXb HLb MIb CTX2 SOB.
      pose proof CTX3 as [CTXc FRXc]. (nelimp CTXc 13%nat; intros HLc HPc PBSc ARRc LENc PNc ERRc MIc PVAc CHNc CCc SSZc _).
      unfold PBS, wz in PBSc.
      pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      (* [comment removed for export] *)
      zstep.
      pose proof (stack_shb0 m3 (PB + 24) SSZc ltac:(lia)) as Z24. asan_chk Z24.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      apply evt_done. cbv beta.
      assert (CTX4 : PVM Q dep m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd (upd bs' (Z.to_nat (off + 0)) (wb 93)) (Z.to_nat (off + 1)) (wb 0))).
      { eapply (pvm_dep_store (dep + 1) dep); [exact CTXc| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. replace (dep + 1 - 1) with dep in * by lia. assumption. }
      eapply (pv_ret1 Q PVL FLAGLOW). eapply (pvx_exit1 Q PVL).
      + split; [exact CTX4|]. eapply pvfr_wext; [exact FRXc| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor].
      + exists 1. split; [lia|]. split; [lia|]. rewrite nth_error_upd_same by (rewrite upd_length; lia). reflexivity.
  Qed.
End ARRA.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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
End CJ_pv_arrA.

(* [comment removed for export] *)
Module CJ_pv_arrB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_lits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numK CJ_pv_arrA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
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
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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

Section ARRB.
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


  (* [comment removed for export] *)
  Definition fz : bool := bv_unsigned (sx32 fw) <? 1.

  (* [comment removed for export] *)
  Definition AHEAD (c : Z) (mm : word -> option byte) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 PB) (Z_to_bv 64 c) (Z_to_bv 64 (PB + 16)) (SHR (PB + 36)) x23 (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
       Fx (Z_to_bv 64 0x84f00) fcx None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition AK (c : Z) : Prop :=
    forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31 : word),
      PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> ARR_LOC Q loc ->
      LSCPS asegs POST (AHEAD c mm Fx fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31) mo1 g1.

  (* [comment removed for export] *)
  Lemma arr_node_now : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs c nx pv ch ty p1 vs vi p2 vd ky,
    PVM Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    rw_cells asegs m c (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (c, 64) B ->
    rw_cells asegs mm c (node_cells nx pv ch ty p1 vs vi p2 vd ky) /\ shb mm c 0 /\ ablock_range c 64 /\ In (c, 64) LB1.
  Proof.
    intros until ky. intros CTX ND CIN. lits. bandM. sepM.
    (nelimp CTX 3%nat; intros HL HP _).
    assert (CIN1 : In (c, 64) LB1). { eapply Permutation_in; [exact HP|]. right. apply BLR. exact CIN. }
    split; [eapply (pvm_node Q PVL); [exact CTX| exact ND| apply node_cells_size| exact CIN]|].
    split; [pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ c 0 HL CIN1 ltac:(lia) ltac:(lia) eq_refl) as X; rewrite Z.add_0_r in X; exact X|].
    split; [exact (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL CIN1)| exact CIN1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_sep : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx c nx pv ch ty p1 vs vi p2 vd ky
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> ARR_LOC Q loc ->
    (3 - Z.b2z fz) + off + 1 <= len ->
    rw_cells asegs m c (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (c, 64) B -> nx <> 0 -> 0 <= nx < 2^64 ->
    AK nx ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11 x12 x13 x14 x15 x16 x17
              (SHR c) (Z_to_bv 64 (Z.b2z fz)) (Z_to_bv 64 c) (Z_to_bv 64 (PB + 16)) (SHR (PB + 36)) (Z_to_bv 64 PB) (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84f84) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX ALC ROOM ND CIN NXNZ NXR K. lits. bandM. sepM. unfold SHR, ASHBASE.
    assert (FZR : 0 <= Z.b2z fz <= 1) by (destruct fz; cbn; lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN _ MI _).
    (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelim (arr_loc9 Q loc LL ALC) 5%nat; intros w0 w1 w2 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR in LOC.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as [_ SOB].
    pose proof (shadow_ok_shchk1 mm buf len (buf + off) SOB ltac:(lia)) as CK0.
    pose proof (shadow_ok_shchk1 mm buf len (buf + off + 1) SOB ltac:(lia)) as CK1.
    assert (CK2 : fz = false -> shchk mm (buf + off + 2) 1) by (intros E; eapply shadow_ok_shchk1; [exact SOB| rewrite E in ROOM; cbn in ROOM; lia]).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    pose proof (stack_shb0 mm (PB + 36) SSZ ltac:(lia)) as Z36.
    unfold PBS, wz in PBS1.
    pose proof (munch_refl [(buf + off, buf + off + 3)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. zstep. sepM. asan_chk CK0.
    zstep. ustore_at buf off (buf + off) 0 (wb 44) ltac:(reflexivity).
    (* [comment removed for export] *)
    asan_chk Z36.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (JN : forall mq (bsq : list byte) x10q x12q x13q,
      u8arr asegs mq buf bsq -> length bsq = length bs ->
      munch [(buf + off, buf + off + 3)] mm mq -> wmono asegs mm mq -> mem_inv asegs mq ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo1 g1)
        (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10q (Z_to_bv 64 (buf + off + (2 - Z.b2z fz))) x12q x13q x14 x15 x16 x17
                (Z_to_bv 64 (Z.shiftr c 3 + 2147450880)) (Z_to_bv 64 (Z.b2z fz)) (Z_to_bv 64 c) (Z_to_bv 64 (PB + 16)) (Z_to_bv 64 (Z.shiftr (PB + 36) 3 + 2147450880)) (Z_to_bv 64 PB)
                (Z_to_bv 64 (Z.shiftr (PB + 16) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x84fd4) fcx None mq (seg_rom asegs))).
    { intros mq bsq x10q x12q x13q ARRq LBS MUq WMq MIq. clear ARR MU WM.
      pose proof (shadow_ok_shchk1 mm buf len (buf + off + (2 - Z.b2z fz)) SOB ltac:(lia)) as CKn.
      zstep. zstep. sepM. asan_chk CKn.
      ustore_at buf off (buf + off + (2 - Z.b2z fz)) (2 - Z.b2z fz) (wb 0) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
      assert (CTX2 : PVX Q (dep + 1) m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off (upd bsq (Z.to_nat (off + (2 - Z.b2z fz))) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf + off, buf + off + 3)]);
          [exact CTXX| exact MUq| exact WMq| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRq| rewrite upd_length; exact LBS]. }
      pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 4%nat; intros HLb _ PBSb _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
      unfold PBS, wz in PBSb.
      destruct (arr_node_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTXb ND CIN) as (NDb & SHc & (C1 & _ & _ & C4) & _).
      unfold node_cells, wz in NDb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
      clear MUq WMq ARRq.
      pose proof (munch_refl [(PB, PB + 32)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
      (* [comment removed for export] *)
      pose proof (stack_shb0 m2 (PB + 16) SSZb ltac:(lia)) as Z16. asan_chk Z16.
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (CTX3 : PVX Q (dep + 1) m3 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len (off + (2 - Z.b2z fz)) (upd bsq (Z.to_nat (off + (2 - Z.b2z fz))) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { split.
        - eapply (pvm_off_store Q PVL); [exact CTXb| exact MU2| exact WM2| assumption| | lia].
          unfold PBS, wz. lazymatch goal with H : rw_cells asegs m3 PB _ |- _ => exact H end.
        - eapply (pvfr_wext Q PVL); [exact FRXb| exact MU2| exact WM2|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
      (* [comment removed for export] *)
      asan_chk SHc.
      zstep. zstep. zstep. if_cases Knx; zify_cond Knx; [| exfalso; lia]. clear Knx.
      apply evt_done. cbv beta.
      unfold AK, AHEAD in K. unfold SHR, ASHBASE in K. eapply K; [exact CTX3| exact ALC]. }
    zstep. if_cases Kf; zify_cond Kf.
    - (* [comment removed for export] *)
      assert (Efz : fz = true) by (unfold fz; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in *. cbn [Z.b2z] in *.
      replace (buf + off + 1) with (buf + off + (2 - 1)) by lia.
      eapply JN; [exact ARR| rewrite upd_length; reflexivity| exact MU| exact WM| assumption].
    - (* [comment removed for export] *)
      assert (Efz : fz = false) by (unfold fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in *. cbn [Z.b2z] in *.
      specialize (CK2 eq_refl).
      zstep. zstep. sepM. asan_chk CK1.
      zstep. zstep.
      ustore_at buf off (buf + off + 1) 1 (wb 32) ltac:(reflexivity).
      zstep.
      replace (buf + off + 2) with (buf + off + (2 - 0)) by lia.
      eapply JN; [exact ARR| rewrite !upd_length; reflexivity| exact MU| exact WM| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_update : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx c nx pv ch ty p1 vs vi p2 vd ky
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31 : word),
    PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> ARR_LOC Q loc -> pb_nul bs len off ->
    rw_cells asegs m c (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (c, 64) B -> 0 <= nx < 2^64 ->
    (nx <> 0 -> AK nx) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) (Z_to_bv 64 c) (Z_to_bv 64 (PB + 16)) (SHR (PB + 36)) x23 (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84f10) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX ALC NUL ND CIN NXR K. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN _ MI _).
    (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelim (arr_loc9 Q loc LL ALC) 5%nat; intros w0 w1 w2 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR in LOC.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    unfold PBS, wz in PBS1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. pose proof (stack_shb0 mm PB SSZ ltac:(lia)) as Z0. asan_chk Z0.
    zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
    pose proof (stack_shb0 mm (PB + 16) SSZ ltac:(lia)) as Z16. asan_chk Z16.
    zstep. zstep. zstep.
    eapply evt_cut. { eapply (pvx_strlen_off Q PVL STRLEN); [exact CTXX| exact NUL]. }
    cbv beta. intros ms' PO. clear Z0 Z16 PBS1 ARR LOC.
    (nelim PO 21%nat; intros k t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 -> CTX1 K0 K1 KN).
    replace (ret_pc (Z_to_bv 64 0x84f38)) with (Z_to_bv 64 0x84f38) by (symmetry; apply ret_pc_even; [lia| reflexivity]). cbv beta delta [mkR].
    pose proof CTX1 as [CTXa FRXa]. (nelimp CTXa 9%nat; intros HLa _ PBSa _ _ _ _ MIa _). (nelimp FRXa 3%nat; intros _ LOCa _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXa)))))))))))) as SSZa.
    rewrite EL in LOCa. cbn [map] in LOCa. unfold SHR in LOCa. unfold PBS, wz in PBSa.
    pose proof (stack_shb0 m1 (PB + 16) SSZa ltac:(lia)) as Z16. asan_chk Z16.
    pose proof (munch_refl [(PB, PB + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    assert (CTX2 : PVX Q (dep + 1) m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len (k + off) bs loc jb SHP_IDLE Fx fcx).
    { split.
      - eapply (pvm_off_store Q PVL); [exact CTXa| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. lazymatch goal with H : rw_cells asegs m2 PB _ |- _ => exact H end.
      - eapply (pvfr_wext Q PVL); [exact FRXa| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
    clear MU WM CTXa FRXa HLa MIa SSZa CTX1.
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 4%nat; intros HLb HPb PBSb _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    destruct (arr_node_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTXb ND CIN) as (NDb & SHc & (C1 & _ & _ & C4) & _).
    unfold node_cells, wz in NDb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
    (* [comment removed for export] *)
    zstep. zstep. asan_chk SHc.
    zstep. zstep. if_cases Knx; zify_cond Knx.
    { (* [comment removed for export] *)
      assert (E0 : nx = 0) by lia. rewrite E0.
      apply evt_done. cbv beta. eapply (arr_close Q PVL ENS FLAGLOW); [exact CTX2| apply arr_locc_of; exact ALC]. }
    assert (NXNZ : nx <> 0) by lia. specialize (K NXNZ).
    (* [comment removed for export] *)
    pose proof (stack_shb0 m2 (PB + 36) SSZb ltac:(lia)) as Z36. asan_chk Z36.
    unfold PBS, wz in PBSb.
    zstep. zstep. zstep. zstep. zstep. zstep.
    fold fz.
    assert (FZR : 0 <= Z.b2z fz <= 1) by (destruct fz; cbn; lia).
    replace (Z.lxor (Z.b2z fz) 3) with (3 - Z.b2z fz) by (destruct fz; reflexivity).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTX2| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms3 mo3 g3 PO.
    (nelim PO 23%nat; intros u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' m3 LB3 TRS3 B3 np3 errv3 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84f80)) with (Z_to_bv 64 0x84f80) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX3 & ROOM & L31)].
    - (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases Kq; zify_cond Kq; [| exfalso; apply Kq; reflexivity]. clear Kq.
      apply evt_done. cbv beta.
      eapply (pv_ret0_2c8 Q PVL FLAGLOW); [exact EX| (nelim ALC 3%nat; intros _ A4 _); exact A4].
    - (* [comment removed for export] *)
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj1 CTX3)) (perm_in_head _ _ _ (proj1 (proj2 (proj1 CTX3))))) 4%nat; intros Y1 _ _ Y4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases Kq; zify_cond Kq; [exfalso; lia|]. clear Kq.
      apply evt_done. cbv beta.
      eapply (arr_sep); [exact CTX3| exact ALC| lia| exact ND| exact CIN| exact NXNZ| exact NXR| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_iter : forall (kk : nat) (d : nat) (c : Z) (Bc : list cblock),
    (length Bc <= kk)%nat -> (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) -> AK c.
  Proof.
    induction kk as [|kk IH]; intros d c Bc LENB Dlt CHc CNZ SUB.
    { exfalso. pose proof (cj_chain_head_block _ _ _ _ _ CHc CNZ) as HIN. destruct Bc; [destruct HIN| cbn in LENB; lia]. }
    unfold AK. intros until x31. intros CTXX ALC. lits. bandM. sepM. unfold AHEAD, SHR, ASHBASE.
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHc CNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY _ SV SK CHC CHN EBc).
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros NX0 _ NX2).
    assert (CIN : In (c, 64) B) by (apply SUB; rewrite EBc; left; reflexivity).
    (* [comment removed for export] *)
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_rec Q PVL REC); [exact CTXX| exact Dlt| exact CHc| exact CNZ| exact SUB| lia| lia| rewrite unsigned_lit by lia; unfold AIMG_HI; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fx' fcx' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84f0c)) with (Z_to_bv 64 0x84f0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt. cbv beta delta [mkR].
    destruct OUT as [(-> & EX) | (-> & buf2 & len2 & off2 & bs2 & CTX2 & NUL2)].
    - zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta.
      eapply (pv_ret0_2c8 Q PVL FLAGLOW); [exact EX| (nelim ALC 3%nat; intros _ A4 _); exact A4].
    - zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      apply evt_done. cbv beta.
      eapply arr_update; [exact CTX2| exact ALC| exact NUL2| exact ND| exact CIN| lia|].
      intros NXNZ. eapply (IH d nx Bn); [| lia| rewrite <- Ed in CHN; exact CHN| exact NXNZ|].
      + rewrite EBc in LENB. cbn in LENB. rewrite !length_app in LENB. lia.
      + intros b Hb. apply SUB. rewrite EBc. right. rewrite !in_app_iff. right; right; right. exact Hb.
  Qed.
End ARRB.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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
End CJ_pv_arrB.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK.
Import CJ_pv_arrA.
Import CJ_pv_arrB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_iface.
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
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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

Section ARR.
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



  Ltac steq := unfold CASE_ST, AHEAD, mkR, SHR, ASHBASE; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sl_wiv (iv : Z * Z) : Prop := (SA <= fst iv /\ snd iv <= SA + 72) \/ (PB <= fst iv /\ snd iv <= PB + 32).

  Lemma pvx_sl_store : forall depc depc' mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off off' bs loc loc' jb shp Fx fcx W mm',
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    munch W mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' -> Forall sl_wiv W ->
    PBS Q mm' buf len off' depc' -> 0 <= off' <= len -> 0 <= depc' ->
    rw_cells asegs mm' SA (map C8 loc') -> length loc' = 9%nat ->
    PVX Q depc' mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off' bs loc' jb shp Fx fcx.
  Proof.
    intros until mm'. intros [CTX FRX] MU WM MI' HW PBS2 HO HD LOC' LL'. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (OWN : Forall (pv_own_iv Q) W).
    { eapply Forall_impl; [| exact HW]. intros [u v] Hiv. unfold sl_wiv in Hiv. unfold pv_own_iv. cbn [fst snd] in *. sepM. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO FHI SPR SHFR R1 Hiv). }
    assert (DJ : forall A k, (A + k <= SA \/ (SA + 72 <= A /\ A + k <= PB) \/ PB + 32 <= A) -> disjoint_from W A k).
    { intros A k HA. apply disjoint_from_forall. eapply Forall_impl; [| exact HW]. intros [u v] Hiv. unfold sl_wiv in Hiv. cbn [fst snd] in *. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR R1 HA Hiv). }
    unfold AERRNO, ATP in ERR.
    split.
    - unfold PVM, PVMs.
      split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|]. split; [exact PBS2|].
      split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; apply DJ; lia]|]. split; [exact LEN|]. split; [unfold pb_nums; lia|].
      split; [eapply (rw_cells_transport asegs); [exact ERR| exact MU| exact WM| apply DJ; unfold AERRNO, ATP; cbn; lia]|]. split; [exact MI'|].
      split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
      split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. apply DJ.
               (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
      split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
      split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
      destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
    - unfold PVFR. unfold SAVEDV, FHDR, FBODY, SHCV, SHCW in *.
      split; [eapply (rw_cells_transport asegs); [exact SAVW| exact MU| exact WM| apply DJ; cbn; lia]|].
      split; [exact LOC'|]. split; [exact LL'|].
      split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| apply DJ; lia]|].
      split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; lia]|].
      split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| apply DJ; cbn; lia]|].
      split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| apply DJ; cbn; lia]|].
      split; [eapply (rw_cells_transport asegs); [exact SHC| exact MU| exact WM| apply DJ; rewrite cells_size_mapC1, length_map, L16, ?SHFR; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]|].
      split; [exact L16|]. split; [exact FRM| exact FA].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_open : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx (d0 : nat) (ch : Z) (Bcc : list cblock)
      (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) -> nth_error loc 7 = Some (SHR PB) -> off + 2 <= len ->
    n = S d0 -> cj_chain CJ_PRINTABLE m d0 ch Bcc -> (forall b, In b Bcc -> In b B) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 (PB + 16)) x22 x23 (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84e88) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX L4 L7 ROOM En CHC SUBC. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP _ ARR LEN PN _ MI _).
    (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as [_ SOB].
    pose proof (shadow_ok_shchk1 mm buf len (buf + off) SOB ltac:(lia)) as CK0.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CH0 _ CH2).
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L4, L7. cbn in L4, L7.
    injection L4 as E4. injection L7 as E7. subst w4 w7. cbn [map] in LOC.
    pose proof (munch_refl [(buf + off, buf + off + 1)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. zstep. zstep. sepM. asan_chk CK0.
    zstep. ustore_at buf off (buf + off) 0 (wb 91) ltac:(reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    assert (CTX1 : PVX Q dep m1 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off (upd bs (Z.to_nat (off + 0)) (wb 91)) loc jb SHP_IDLE Fx fcx).
    { eapply (pvx_out_store Q PVL) with (W := [(buf + off, buf + off + 1)]);
        [exact CTXX| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARR| rewrite upd_length; reflexivity]. }
    clear MU WM LOC.
    pose proof CTX1 as [CTXa FRXa]. (nelimp CTXa 4%nat; intros HLa _ PBSa _). (nelimp FRXa 3%nat; intros _ LOCa _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXa)))))))))))) as SSZa.
    rewrite EL in LOCa. cbn [map] in LOCa. unfold PBS, wz in PBSa.
    (* [comment removed for export] *)
    pose proof (stack_shb0 m1 (PB + 16) SSZa ltac:(lia)) as Z16. asan_chk Z16.
    pose proof (munch_refl [(PB, PB + 32); (SA, SA + 72)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (stack_shb0 m1 (PB + 24) SSZa ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    assert (CTX2 : PVX Q (dep + 1) m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len (off + 1) (upd bs (Z.to_nat (off + 0)) (wb 91))
                       [w0; w1; w2; SHR (PB + 24); Z_to_bv 64 Fr; Z_to_bv 64 (PB + 24); w6; SHR PB; w8] jb SHP_IDLE Fx fcx).
    { eapply (pvx_sl_store dep (dep + 1)) with (W := [(PB, PB + 32); (SA, SA + 72)]);
        [exact CTX1| exact MU| exact WM| assumption| | | lia| lia| | reflexivity].
      - constructor; [unfold sl_wiv; cbn [fst snd]; lia|]. constructor; [unfold sl_wiv; cbn [fst snd]; lia| constructor].
      - unfold PBS, wz. lazymatch goal with H : rw_cells asegs m2 PB _ |- _ => exact H end.
      - unfold SHR. cbn [map]. lazymatch goal with H : rw_cells asegs m2 SA _ |- _ => exact H end. }
    clear MU WM CTX1 CTXa FRXa HLa SSZa Z16 Z24.
    (* [comment removed for export] *)
    zstep. if_cases Kch; zify_cond Kch.
    { (* [comment removed for export] *)
      assert (E0 : ch = 0) by lia. rewrite E0 in *.
      apply evt_done. cbv beta.
      eapply (arr_close Q PVL ENS FLAGLOW); [exact CTX2|]. split; [reflexivity|]. split; reflexivity. }
    assert (CHNZ : ch <> 0) by lia.
    (* [comment removed for export] *)
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 4%nat; intros HLb _ PBSb _).
    unfold PBS, wz in PBSb.
    pose proof (munch_refl [(SA, SA + 72)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    lazymatch goal with H : rw_cells asegs m3 SA (map C8 ?l) |- _ => rename H into LOC3 | H : rw_cells asegs m3 SA ?cs |- _ => rename H into LOC3 end.
    apply evt_done. cbv beta.
    lazymatch type of LOC3 with rw_cells _ _ _ [C8 ?v0; C8 ?v1; C8 ?v2; C8 ?v3; C8 ?v4; C8 ?v5; C8 ?v6; C8 ?v7; C8 ?v8] =>
      assert (CTX3 : PVX Q (dep + 1) m3 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len (off + 1) (upd bs (Z.to_nat (off + 0)) (wb 91))
                         [v0; v1; v2; v3; v4; v5; v6; v7; v8] jb SHP_IDLE Fx fcx)
    end.
    { eapply (pvx_sl_store (dep + 1) (dep + 1)) with (W := [(SA, SA + 72)]);
        [exact CTX2| exact MU| exact WM| assumption| | | lia| lia| cbn [map]; exact LOC3| reflexivity].
      - constructor; [unfold sl_wiv; cbn [fst snd]; lia| constructor].
      - unfold PBS, wz. lazymatch goal with H : rw_cells asegs m3 PB _ |- _ => exact H end. }
    pose proof (arr_iter Q PVL ENS STRLEN REC FLAGLOW (length Bcc) d0 ch Bcc ltac:(lia) ltac:(lia) CHC CHNZ SUBC) as K.
    unfold AK, AHEAD, SHR, ASHBASE in K. eapply K; [exact CTX3|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma arr_commit : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len Bn ns off bs loc jb Fx fcx (d0 : nat) (ch : Z) (Bcc : list cblock)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    PVMs Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len Bn ns off bs -> PVFR Q mm loc jb SHP_IDLE Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) -> nth_error loc 7 = Some (SHR PB) -> off + 2 <= ns ->
    n = S d0 -> cj_chain CJ_PRINTABLE m d0 ch Bcc -> (forall b, In b Bcc -> In b B) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 Bn) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 ns) (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 (PB + 16)) x22 (SHR (PB + 8)) (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84e60) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTX FRX L4 L7 ROOM En CHC SUBC. lits. bandM. sepM. unfold SHR, ASHBASE.
    (nelimp CTX 13%nat; intros HL HP PBS1 _ LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L4, L7. cbn in L4, L7.
    injection L4 as E4. injection L7 as E7. subst w4 w7. cbn [map] in LOC. unfold SHR in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(PB, PB + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (stack_shb0 mm (PB + 8) SSZ ltac:(lia)) as Z8. asan_chk Z8.
    zstep. zstep.
    pose proof (stack_shb0 mm PB SSZ ltac:(lia)) as Z0. asan_chk Z0.
    zstep.
    pose proof (stack_shb0 mm (PB + 16) SSZ ltac:(lia)) as Z16. asan_chk Z16.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (CTX2 : PVX Q dep m2 mo1 g1 LB1 TRS1 B1 np1 errv1 Bn ns off bs loc jb SHP_IDLE Fx fcx).
    { eapply (pvx_commit Q PVL); [exact CTX| exact FRX| exact MU| exact WM| | ].
      - lazymatch goal with H : mem_inv asegs m2 |- _ => exact H end.
      - unfold PBS. lazymatch goal with H : rw_cells asegs m2 PB _ |- _ => exact H end. }
    zstep. apply evt_done. cbv beta.
    eapply lscps_eq; [| eapply (arr_open m2 mo1 g1 LB1 TRS1 B1 np1 errv1 Bn ns off bs loc jb Fx fcx d0 ch Bcc);
                        [exact CTX2| rewrite EL; reflexivity| rewrite EL; reflexivity| exact ROOM| exact En| exact CHC| exact SUBC]].
    steq.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_grow : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx ns (d0 : nat) (ch : Z) (Bcc : list cblock)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    nth_error loc 4 = Some (Z_to_bv 64 Fr) -> nth_error loc 7 = Some (SHR PB) ->
    len < ns <= INT_MAX -> (2 * len + 2 <= ns \/ ns = INT_MAX) -> off + 2 <= ns ->
    n = S d0 -> cj_chain CJ_PRINTABLE m d0 ch Bcc -> (forall b, In b Bcc -> In b B) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 ns) (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 (PB + 16)) x22 (SHR (PB + 8)) (SHR (PB + 16)) (SHR Fr) (Z_to_bv 64 Fr)
              (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84b74) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX L4 L7 NS HG ROOM En CHC SUBC. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    pose proof INT_MAX_eq as IME.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (stack_shb0 mm (PB + 56) SSZ ltac:(lia)) as Z56. asan_chk Z56. clear Z56.
    zstep. zstep. sepM. sepM. if_cases Kd; zify_cond Kd; [exfalso; unfold AREALLOC in Kd; lia|]. clear Kd.
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AREALLOC)) with (wz AREALLOC) by (unfold wz, AREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_realloc Q PVL); [exact CTXX| exact NS| exact HG| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> RES).
    replace (ret_pc (Z_to_bv 64 0x84b98)) with (Z_to_bv 64 0x84b98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RES as [[-> FF] | (Bn & bs' & -> & BLO & BHI & CTX2 & FRX2)].
    - (* [comment removed for export] *)
      (nelimp FF 15%nat; intros FRX2 HL2 ERR2 MI2 PVA2 CHN2 CC2 GM2 TV2 SSZ2 HP2 PBS2 HB2 HNP2 NPX2).
      (nelimp FRX2 3%nat; intros SAVW2 LOC2 _).
      (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC2, L4, L7. cbn in L4, L7.
      injection L4 as E4. injection L7 as E7. subst w4 w7. cbn [map] in LOC2. unfold SHR in LOC2.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
      zstep. zstep. zstep.
      pose proof (stack_shb0 m2 (PB + 48) SSZ2 ltac:(lia)) as Z48. asan_chk Z48. clear Z48.
      zstep.
      pose proof (stack_shb0 m2 PB SSZ2 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
      apply evt_done. cbv beta.
      eapply (pv_fail_free' Q PVL FLAGLOW MEMSET). exact FF.
    - (* [comment removed for export] *)
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BLO. bandM. sepM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
      apply evt_done. cbv beta.
      eapply arr_commit; [exact CTX2| exact FRX2| exact L4| exact L7| exact ROOM| exact En| exact CHC| exact SUBC].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_mid : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx (d0 : nat) (ch : Z) (Bcc : list cblock)
      (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31 : word),
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    nth_error loc 7 = Some (SHR PB) -> (len = 0 \/ off < len) ->
    n = S d0 -> cj_chain CJ_PRINTABLE m d0 ch Bcc -> (forall b, In b Bcc -> In b B) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 buf) x11 x12 (Z_to_bv 64 len) x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) (Z_to_bv 64 ch) x21 (Z_to_bv 64 (PB + 8)) (SHR (PB + 8)) (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr)
              (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84678) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX L7 OFFLEN En CHC SUBC. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PBS, wz in PBS1.
    pose proof INT_MAX_eq as IME.
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L7. cbn in L7. injection L7 as E7. subst w7. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(SA, SA + 72)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    destruct (pvx_loc_store Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 [w0; w1; w2; w3; Z_to_bv 64 Fr; w5; w6; SHR PB; w8] CTX FRX MU WM
                ltac:(lazymatch goal with H : mem_inv asegs m2 |- _ => exact H end)
                ltac:(unfold SHR; cbn [map]; lazymatch goal with H : rw_cells asegs m2 SA _ |- _ => exact H end) eq_refl) as [CTX2 FRX2].
    assert (L4 : nth_error [w0; w1; w2; w3; Z_to_bv 64 Fr; w5; w6; SHR PB; w8] 4 = Some (Z_to_bv 64 Fr)) by reflexivity.
    assert (L7' : nth_error [w0; w1; w2; w3; Z_to_bv 64 Fr; w5; w6; SHR PB; w8] 7 = Some (SHR PB)) by reflexivity.
    assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX2)))))))))))).
    clear MU WM.
    zstep. zstep. zstep.
    pose proof (stack_shb0 m2 (PB + 16) SSZ2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep.
    zstep. if_cases Kr; zify_cond Kr.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta.
      eapply lscps_eq; [| eapply (arr_open m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb Fx fcx d0 ch Bcc);
                          [split; [exact CTX2| exact FRX2]| exact L4| exact L7'| lia| exact En| exact CHC| exact SUBC]].
      steq.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (stack_shchk m2 (PB + 32) 4 SSZ2 ltac:(lia)) as CK4. sepM. asan_chk CK4.
      zstep. rewrite (sx32_lit 0) by lia. zstep. if_true.
      zstep. zstep. if_cases K30; zify_cond K30.
      + (* [comment removed for export] *)
        rewrite Z.shiftr_div_pow2 in K30 by lia. change (2^30) with 1073741824 in K30.
        zstep. apply evt_done. cbv beta.
        eapply lscps_eq; [| eapply (arr_grow m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb Fx fcx (2 * (off + 2)) d0 ch Bcc);
                            [split; [exact CTX2| exact FRX2]| exact L4| exact L7'| lia| lia| lia| exact En| exact CHC| exact SUBC]].
        steq.
      + zstep. zstep. if_cases K31; zify_cond K31.
        * (* [comment removed for export] *)
          apply evt_done. cbv beta. eapply (pv_ret0_924 Q PVL FLAGLOW); [eapply (pvx_exit0 Q PVL); split; [exact CTX2| exact FRX2]| exact L4].
        * rewrite Z.shiftr_div_pow2 in K30, K31 by lia. change (2^30) with 1073741824 in K30. change (2^31) with 2147483648 in K31.
          zstep. zstep. zstep. apply evt_done. cbv beta.
          eapply lscps_eq; [| eapply (arr_grow m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb Fx fcx INT_MAX d0 ch Bcc);
                              [split; [exact CTX2| exact FRX2]| exact L4| exact L7'| lia| lia| lia| exact En| exact CHC| exact SUBC]].
          steq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem pv_arr_case : pv_case_at PV_ARR_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros CTXX. lits. bandM. sepM. unfold CASE_ST, PVPOST, PV_ARR_ENTRY, ASHBASE, SHR.
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
    pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ p 16 HL PIN1 ltac:(lia) ltac:(lia) eq_refl) as SH16.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CH0 _ CH2).
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. zstep. zstep. asan_chk SH16.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA, SA + 72)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (pvx_loc_store Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 [w0; w1; w2; w3; w4; w5; w6; SHR PB; w8] CTX FRX MU WM
                ltac:(lazymatch goal with H : mem_inv asegs m1 |- _ => exact H end)
                ltac:(unfold SHR; cbn [map]; lazymatch goal with H : rw_cells asegs m1 SA _ |- _ => exact H end) eq_refl) as [CTX1 FRX1].
    assert (L7 : nth_error [w0; w1; w2; w3; w4; w5; w6; SHR PB; w8] 7 = Some (SHR PB)) by reflexivity.
    pose proof (stack_shb0 mm PB SSZ ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    assert (SSZ1 : sh_zero m1 alloc_ceiling (2^47)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX1)))))))))))).
    (nelimp CTX1 4%nat; intros _ _ PBSa _). unfold PBS, wz in PBSa.
    destruct (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX1 ND PIN) as (NDa & _).
    unfold node_cells, wz in NDa.
    clear MU WM PBS1 NDm LOC.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
    zstep. zstep. zstep.
    pose proof (stack_shb0 m1 (PB + 8) SSZ1 ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep.
    zstep. if_cases Kl; zify_cond Kl.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta.
      eapply lscps_eq; [| eapply (arr_mid m1 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb Fx fcx d0 ch Bcc);
                          [split; [exact CTX1| exact FRX1]| exact L7| left; exact Kl| exact En| exact CHC| exact SUBC]].
      steq.
    - zstep. zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 16) SSZ1 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep. if_cases Ko; zify_cond Ko.
      + (* [comment removed for export] *)
        apply evt_done. cbv beta. eapply (pv_ret0_930 Q PVL FLAGLOW). eapply (pvx_exit0 Q PVL). split; [exact CTX1| exact FRX1].
      + apply evt_done. cbv beta.
        eapply lscps_eq; [| eapply (arr_mid m1 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs _ jb Fx fcx d0 ch Bcc);
                            [split; [exact CTX1| exact FRX1]| exact L7| right; lia| exact En| exact CHC| exact SUBC]].
        steq.
  Qed.
End ARR.

(* [comment removed for export] *)
Theorem case_arr : forall (AI : art_iface) (TI : trs_iface),
  ensure_stmt AI TI -> strlen_icpt_spec -> art_flag_low_stmt AI -> asan_memset_spec ->
  forall Q, q_ai Q = AI -> q_ti Q = TI -> pvl Q -> (forall d, (d < q_n Q)%nat -> print_value_at AI TI d) -> pv_case_at PV_ARR_ENTRY Q.
Proof.
  intros AI TI ENS STRLEN FL MS Q EA ET PVL REC.
  apply (pv_arr_case Q PVL); rewrite ?EA, ?ET; first [exact ENS| exact STRLEN| exact REC| exact FL| exact MS].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
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
