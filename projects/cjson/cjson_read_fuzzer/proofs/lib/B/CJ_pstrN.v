(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_tree CJ_conv CJ_traces ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_ensure.
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
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].

(* [comment removed for export] *)
Definition AQQ : Z := 0x212c0.
Definition qq_bytes : list byte := [wb 34; wb 34; wb 0].
Lemma qq_bytes_at : forall m, mem_inv bsegs m -> bytes_at bsegs m AQQ qq_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image bsegs m AQQ qq_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold AQQ; lia) ltac:(cbn; unfold AQQ; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis MEMCPY : asan_memcpy_spec.

  (* [comment removed for export] *)
  Lemma art_qq_shadow : forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> shadow_ok m AQQ 3.
  Proof.
    intros until g. intros HL. destruct (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL) as [G _].
    rewrite Forall_forall in G. exact (G (AQQ, 3) ltac:(unfold AGLOB_STRS, AQQ; cbn; tauto)).
  Qed.

  Section Call.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte) (g : lghost)
              (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np BB : Z)
              (PB buf len off dep : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word).
    Hypothesis HP : Permutation ((buf, len) :: LR) LB.
    Hypothesis PN : pb_nums len off dep.
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis PAL : PB mod 8 = 0.
    Hypothesis SP16 : bv_unsigned sp + 16 <= PB.
    Hypothesis P80 : PB + 80 <= 2^47.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 < ASTACK_TOP sp0.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - APSTR_STACK.
    Hypothesis TP : tp = wz ATP.
    Hypothesis LEN : Z.of_nat (length bs) = len.
    Hypothesis NPR : np + pb_npallow len <= NPMAX TI.
    Hypothesis HB : pb_allow len <= BB.
    Hypothesis R : ablock_range buf len.

    Notation POST := (pstr_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np BB PB len dep fw lo m g).
    Notation SPF := (bv_unsigned sp + -128).
    (* [comment removed for export] *)
    Notation FRAME mm c0 c1 c2 := (rw_cells bsegs mm (bv_unsigned sp + -128)
       [c0; c1; c2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells bsegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                              C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)]).

    (* [comment removed for export] *)
    Definition ninv (mm : word -> option byte) (mo : Model) (gg : lghost) (LBX : list cblock) (TRSX : list (list Z)) (BX npX : Z) : Prop :=
      ART AI sp0 SPB LBX LF TRSX BX mm mo gg /\ stk bsegs mm lo SPF /\ mem_inv bsegs mm
      /\ (exists e, rw_cells bsegs mm AERRNO [C4 e]) /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m mm
      /\ sh_zero mm alloc_ceiling (2^47) /\ pb_below mm PB /\ gmono g gg /\ TINV TI npX TRSX.

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma SPtop : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.
    Lemma PBS_fold : forall mm b l, PBS mm b l -> pb_struct mm PB b l off dep fw.
    Proof. intros mm b l H. exact H. Qed.

    (* [comment removed for export] *)
    Lemma frame_drop_slots : forall mm (c0 c1 c2 : cell) cs A, Cells.csize c0 = 8%nat -> Cells.csize c1 = 8%nat -> Cells.csize c2 = 8%nat ->
      rw_cells bsegs mm A (c0 :: c1 :: c2 :: cs) -> stk bsegs mm lo A -> lo <= A ->
      rw_cells bsegs mm (A + 24) cs /\ stk bsegs mm lo (A + 24).
    Proof.
      intros mm c0 c1 c2 cs A C0 C1 C2 FR ST HA. destruct (rw_cells_app_split mm A [c0; c1; c2] cs FR) as [F1 F2].
      cbn [cells_size] in F2. rewrite C0, C1, C2 in F2. cbn in F2. split; [exact F2|].
      pose proof (stk_release bsegs mm lo A [c0; c1; c2] ST F1 HA) as S. cbn [cells_size] in S. rewrite C0, C1, C2 in S. cbn in S. exact S.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_epi : forall mm mo' g' (c0 c1 c2 : cell) (Fc : bvmap 5 word) (fcc : bv 32)
        (x1 x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 c1 c2 -> Cells.csize c0 = 8%nat -> Cells.csize c1 = 8%nat -> Cells.csize c2 = 8%nat ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      print_outcome AI TI sp0 SPB LR LF np BB PB len dep fw r mm mo' g' ->
      LSCPS bsegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x86d14) fcc None mm (seg_rom bsegs)) mo' g'.
    Proof.
      intros until e'. intros FR C0 C1 C2 ST MI ERR FRM FA PVA GM OUT.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      destruct (frame_drop_slots mm c0 c1 c2 _ _ C0 C1 C2 FR ST ltac:(lia)) as [FR' ST']. clear FR ST.
      replace (bv_unsigned sp + -128 + 24) with (bv_unsigned sp + -104) in FR', ST' by lia.
      eapply lscps_step_evt. cbv beta delta [mkR].
      do 14 zstep. release_frame FR' ST' (bv_unsigned sp). zstep.
      apply evt_done. apply lscps_done. unfold pstr_post.
      do 19 eexists. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split; [exact FA|]. split; [exact ST'|].
      split; [exact ERR|]. split; [exact PVA|]. split; [exact GM| exact OUT].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_ret1 : forall mm mo' g' (c0 c1 c2 : cell) (Fc : bvmap 5 word) (fcc : bv 32) LB' TRS' B' np' buf' len' bs'
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 c1 c2 -> Cells.csize c0 = 8%nat -> Cells.csize c1 = 8%nat -> Cells.csize c2 = 8%nat ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> len' < 2^31 -> len <= len' -> pb_nul bs' len' off ->
      BB - (pb_pot len' - pb_pot len) <= B' -> np' <= np + (pb_npot len' - pb_npot len) ->
      LSCPS bsegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x86d10) fcc None mm (seg_rom bsegs)) mo' g'.
    Proof.
      intros until e'. intros FR C0 C1 C2 ST MI ERR FRM FA PVA GM HL' TV' HP' PBS' PD' L31 LL NUL HB' HN'.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      destruct PN as (PN1 & PN2 & PN3).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
      eapply pstr_epi; [exact FR| exact C0| exact C1| exact C2| exact ST| exact MI| exact ERR| exact FRM| exact FA| exact PVA| exact GM|].
      exists LB', TRS', B', np', buf', len', off. split; [exact HL'|]. split; [exact TV'|]. right. split; [reflexivity|].
      split. { exists bs'. split; [exact HP'|]. split; [exact (PBS_fold _ _ _ PBS')|]. split; [exact PD'|]. split; [| exact NUL].
               destruct NUL as (K & K0 & K1 & _). split; [lia|]. split; [exact L31| exact PN3]. }
      split; [exact LL|]. split; [exact HB'| exact HN'].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_ret0 : forall mm mo' g' (c0 c1 c2 : cell) (Fc : bvmap 5 word) (fcc : bv 32) LB' TRS' B' np' buf' len'
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 c1 c2 -> Cells.csize c0 = 8%nat -> Cells.csize c1 = 8%nat -> Cells.csize c2 = 8%nat ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' ->
      PBS mm buf' len' ->
      ( (buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB') ) ->
      BB - pb_allow len <= B' -> np' <= np + pb_npallow len ->
      LSCPS bsegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x86d14) fcc None mm (seg_rom bsegs)) mo' g'.
    Proof.
      intros until e'. intros FR C0 C1 C2 ST MI ERR FRM FA PVA GM HL' TV' PBS' HB0 HB' HN'.
      eapply pstr_epi; [exact FR| exact C0| exact C1| exact C2| exact ST| exact MI| exact ERR| exact FRM| exact FA| exact PVA| exact GM|].
      exists LB', TRS', B', np', buf', len', off. split; [exact HL'|]. split; [exact TV'|]. left. split; [reflexivity|].
      split; [exists dep; exact (PBS_fold _ _ _ PBS')|]. split; [exact HB0|]. split; [exact HB'| exact HN'].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_qq : forall mm mo' g' (c0 c1 c2 : cell) (fcc : bv 32) LB' TRS' B' np' buf' len' bs'
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 c1 c2 -> Cells.csize c0 = 8%nat -> Cells.csize c1 = 8%nat -> Cells.csize c2 = 8%nat ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] -> frm0 fcc ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> 3 + off + 1 <= len' -> len' < 2^31 -> len <= len' ->
      BB - (pb_pot len' - pb_pot len) <= B' -> np' <= np + (pb_npot len' - pb_npot len) ->
      LSCPS bsegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (buf' + off)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86c20) fcc None mm (seg_rom bsegs)) mo' g'.
    Proof.
      intros until e'. intros FR C0 C1 C2 ST MI ERR FRM PVA GM HL' TV' HP' PBS' [ARR LEN'] ROOM L31 LL HB' HN'.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      destruct PN as (PN1 & PN2 & PN3). destruct PL as (PL1 & PL2 & PL3).
      pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) as (Y1 & Y2 & Y3 & Y4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) as [_ SOB].
      pose proof (art_qq_shadow _ _ _ _ _ _ _ _ _ HL') as SOQ.
      destruct (u8arr_split3 mm buf' bs' (Z.to_nat off) 3 ARR ltac:(lia)) as (A1 & A2 & A3).
      rewrite (Z2Nat.id off) in A2, A3 by lia.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep. zstep.
      replace (ret_pc (Z_to_bv 64 AASANMEMCPY)) with (wz AASANMEMCPY) by (unfold wz, AASANMEMCPY; symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold wz.
      eapply evt_cut.
      { pose proof MEMCPY as MCX. unfold asan_memcpy_spec, memcpy_contract in MCX.
        eapply MCX with (lo := lo) (d := buf' + off) (s := AQQ) (n := 3) (src := qq_bytes); clear MCX; rewrite ?unsigned_lit by lia;
          first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL' end | exact MI | exact ST | apply qq_bytes_at; exact MI | exact A2 | reflexivity
                | unfold AQQ; lia
                | left; unfold lowmem_range, AQQ, KLOWSHADOW_BEG; cbn; lia
                | lazymatch goal with |- app_range _ _ => app_rng0 end
                | apply wr_range_ok_high; lia
                | intros _; exact SOQ
                | intros _; eapply shadow_ok_sub; [exact SOB| lia| lia| lia]
                | alia | lia ]. }
      cbv beta. intros ms2 PO.
      destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & DST & _ & ST2).
      rewrite SPFeq in MU2, ST2. unfold AINTRIN_STACK in MU2.
      replace (ret_pc (Z_to_bv 64 0x86c30)) with (Z_to_bv 64 0x86c30) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport bsegs) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size]; rewrite C0, C1, C2; cbn; lia].
      eapply (rw_cells_transport bsegs) in ERR; [| exact MU2| exact WM2| cbn; unfold AERRNO, ATP; lia].
      eapply (rw_cells_transport bsegs) in PBS'; [| exact MU2| exact WM2| cbn; lia].
      apply (u8arr_transport bsegs _ _ m2 _ _ A1) in MU2 as A1'; [| exact WM2| cbn [disjoint_from]; rewrite firstn_length_le by lia; lia].
      apply (u8arr_transport bsegs _ _ m2 _ _ A3) in MU2 as A3'; [| exact WM2| cbn [disjoint_from]; rewrite length_skipn; lia].
      change (Z.to_nat 3) with 3%nat in DST.
      destruct (u8arr_join3' m2 buf' _ off _ _ _ A1' ltac:(rewrite firstn_length_le by lia; lia) DST A3') as [ARR2 _].
      assert (HL2 : ART AI sp0 SPB LB' LF TRS' B' m2 mo' g').
      { eapply (art_frame AI); [exact HL'| exact MU2| exact WM2|]. constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists buf', len'. split; [eapply perm_in_head; exact HP'| cbn; lia].
        - right; left. cbn. lia. }
      assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA|].
        eapply (pv_agree_of_munchW AI); [exact HL'| exact HP'| exact MU2| exact WM2| | lia| lia| lia].
        constructor; [do 3 right; cbn; lia|]. constructor; [right; right; left; cbn; lia| constructor]. }
      zstep. apply evt_done. cbv beta.
      eapply pstr_ret1; [exact FR| exact C0| exact C1| exact C2| exact ST2| exact MI2| exact ERR| exact FRM| intros k Hk; reflexivity| exact PVA2| exact GM| exact HL2| exact TV'| exact HP'| exact PBS'| | exact L31| exact LL| | exact HB'| exact HN'].
      - split; [exact ARR2| rewrite !length_app, firstn_length_le, length_skipn by lia; cbn; lia].
      - exists 2. split; [lia|]. split; [lia|].
        rewrite nth_error_app2 by (rewrite firstn_length_le by lia; lia). rewrite firstn_length_le by lia.
        replace (Z.to_nat (off + 2) - Z.to_nat off)%nat with 2%nat by lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_null : forall (m1 : word -> option byte) (mo1 : Model) fc j0 j1 j2 (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      ninv m1 mo1 g LB TRS BB np -> FRAME m1 (CB 8 j0) (CB 8 j1) (CB 8 j2) -> PBS m1 buf len -> u8arr bsegs m1 buf bs -> frm0 fc ->
      LSCPS bsegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 PB) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86c10) fc None m1 (seg_rom bsegs)) mo1 g.
    Proof.
      intros until x31. intros NI FR PBS1 ARR FRM. pose proof NI as (HL & ST1 & MI1 & [e ERR] & PVA & SSZ1 & PBW1 & GM1 & TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPtop as SPT.
      pose proof R as (R1 & R2 & R3 & R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      destruct PL as (PL1 & PL2 & PL3). destruct PN as (PN1 & PN2 & PN3). unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep.
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { eapply (ensure_ok AI TI) with (lo := lo) (LR := LR) (bs := bs) (needed := 3); rewrite ?E1;
          first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | exact PN | exact ST1 | exact ERR | exact MI1 | exact TP | reflexivity
                | exact PAL | exact PBW1 | exact SSZ1 | exact TV1
                | split; [lia| split; [lia| lia]]
                | apply Z.mod_divide; [lia|]; apply Z.mod_divide in SPAL; [| lia]; destruct SPAL as [q Hq]; exists (q - 8); lia
                | pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)); lia
                | unfold AENSURE_STACK, AMALLOC_STACK; lia | alia | lia ]. }
      cbv beta. intros ms2 mo2 g2 PO.
      destruct PO as (t0' & t1' & t2' & a0'' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & LB2 & TRS2 & B2 & np2
                      & -> & MI2 & ST2 & ERR2 & PVE & HL2 & TV2 & GM2 & OUT).
      rewrite E1 in ST2, PVE. unfold AERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x86c1c)) with (Z_to_bv 64 0x86c1c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply (pv_agree_rw_cells_stack _ _ _ _ _ _ _ _ _ PVE) in FR; [| lia| cbn; lia| cbn; lia].
      assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
      assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM1| exact GM2]).
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct OUT as [(-> & HPn & PBSn & HBn & HNn) | [(-> & HPn & PBSn & PDn & -> & ->) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31 & LL & HBn & HNn)]].
      - (* [comment removed for export] *)
        unfold wz. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_ret0; try eassumption; [reflexivity| reflexivity| reflexivity| intros k Hk; reflexivity| left; split; [reflexivity| exact HPn]| |].
        + unfold pb_allow. pose proof (pb_pot_mono len INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)). lia.
        + pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        unfold wz. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_ret0; try eassumption; [reflexivity| reflexivity| reflexivity| intros k Hk; reflexivity| right; split; [lia| exact HPn]| |].
        + pose proof (pb_allow_ge_fail len ltac:(rewrite INT_MAX_eq; lia)). rewrite PB_FAIL_eq in *. lia.
        + pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _ & _ & Y4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
        unfold wz. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_qq; try eassumption; try reflexivity; lia.
    Qed.
  End Call.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].
