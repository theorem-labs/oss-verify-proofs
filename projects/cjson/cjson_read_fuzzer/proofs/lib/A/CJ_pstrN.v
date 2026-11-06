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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_tree CJ_conv CJ_traces ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_ensure.
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
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].

(* [comment removed for export] *)
Definition AQQ : Z := 0x212a0.
Definition qq_bytes : list byte := [wb 34; wb 34; wb 0].
Lemma qq_bytes_at : forall m, mem_inv asegs m -> bytes_at asegs m AQQ qq_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image asegs m AQQ qq_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold AQQ; lia) ltac:(cbn; unfold AQQ; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis MEMSET : asan_memset_spec.
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
    Notation SPF := (bv_unsigned sp + -112).
    Notation FRAME mm c0 := (rw_cells asegs mm (bv_unsigned sp + -112)
       [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells asegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                              C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)]).
    Notation SHB := (Z_to_bv 64 0x7fff8000).
    Notation SHA a := (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)).

    (* [comment removed for export] *)
    Definition ninv (mm : word -> option byte) (mo : Model) (gg : lghost) (LBX : list cblock) (TRSX : list (list Z)) (BX npX : Z) : Prop :=
      ART AI sp0 SPB LBX LF TRSX BX mm mo gg /\ stk asegs mm lo SPF /\ mem_inv asegs mm
      /\ (exists e, rw_cells asegs mm AERRNO [C4 e]) /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m mm
      /\ sh_zero mm alloc_ceiling (2^47) /\ pb_below mm PB /\ gmono g gg /\ TINV TI npX TRSX.

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma SPtop : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.
    Lemma PBS_fold : forall mm b l, PBS mm b l -> pb_struct mm PB b l off dep fw.
    Proof. intros mm b l H. exact H. Qed.

    (* [comment removed for export] *)
    Lemma frame_drop_slot : forall mm (c0 : cell) cs A, Cells.csize c0 = 8%nat ->
      rw_cells asegs mm A (c0 :: cs) -> stk asegs mm lo A -> lo <= A ->
      rw_cells asegs mm (A + 8) cs /\ stk asegs mm lo (A + 8).
    Proof.
      intros mm c0 cs A C8 FR ST HA. destruct (rw_cells_app_split mm A [c0] cs FR) as [F1 F2].
      cbn [cells_size] in F2. rewrite C8, Nat.add_0_r in F2. split; [exact F2|].
      pose proof (stk_release asegs mm lo A [c0] ST F1 HA) as S. cbn [cells_size] in S. rewrite C8, Nat.add_0_r in S. exact S.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_epi : forall mm mo' g' (c0 : cell) (Fc : bvmap 5 word) (fcc : bv 32)
        (x1 x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 -> Cells.csize c0 = 8%nat -> stk asegs mm lo SPF -> mem_inv asegs mm -> rw_cells asegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      print_outcome AI TI sp0 SPB LR LF np BB PB len dep fw r mm mo' g' ->
      LSCPS asegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x873b4) fcc None mm (seg_rom asegs)) mo' g'.
    Proof.
      intros until e'. intros FR C8 ST MI ERR FRM FA PVA GM OUT.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      destruct (frame_drop_slot mm c0 _ _ C8 FR ST ltac:(lia)) as [FR' ST']. clear FR ST.
      replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in FR', ST' by lia.
      eapply lscps_step_evt. cbv beta delta [mkR].
      do 14 zstep. release_frame FR' ST' (bv_unsigned sp). zstep.
      apply evt_done. apply lscps_done. unfold pstr_post.
      nexists 19%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split; [exact FA|]. split; [exact ST'|].
      split; [exact ERR|]. split; [exact PVA|]. split; [exact GM| exact OUT].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_ret1 : forall mm mo' g' (c0 : cell) (Fc : bvmap 5 word) (fcc : bv 32) LB' TRS' B' np' buf' len' bs'
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 -> Cells.csize c0 = 8%nat -> stk asegs mm lo SPF -> mem_inv asegs mm -> rw_cells asegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> len' < 2^31 -> len <= len' -> pb_nul bs' len' off ->
      BB - (pb_pot len' - pb_pot len) <= B' -> np' <= np + (pb_npot len' - pb_npot len) ->
      LSCPS asegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x873b0) fcc None mm (seg_rom asegs)) mo' g'.
    Proof.
      intros until e'. intros FR C8 ST MI ERR FRM FA PVA GM HL' TV' HP' PBS' PD' L31 LL NUL HB' HN'.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      (nelimp PN 3%nat; intros PN1 PN2 PN3).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
      eapply pstr_epi; [exact FR| exact C8| exact ST| exact MI| exact ERR| exact FRM| exact FA| exact PVA| exact GM|].
      exists LB', TRS', B', np', buf', len', off. split; [exact HL'|]. split; [exact TV'|]. right. split; [reflexivity|].
      split. { exists bs'. split; [exact HP'|]. split; [exact (PBS_fold _ _ _ PBS')|]. split; [exact PD'|]. split; [| exact NUL].
               (nelim NUL 4%nat; intros K K0 K1 _). split; [lia|]. split; [exact L31| exact PN3]. }
      split; [exact LL|]. split; [exact HB'| exact HN'].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_ret0 : forall mm mo' g' (c0 : cell) (Fc : bvmap 5 word) (fcc : bv 32) LB' TRS' B' np' buf' len'
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 -> Cells.csize c0 = 8%nat -> stk asegs mm lo SPF -> mem_inv asegs mm -> rw_cells asegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' ->
      PBS mm buf' len' ->
      ( (buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB') ) ->
      BB - pb_allow len <= B' -> np' <= np + pb_npallow len ->
      LSCPS asegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x873b4) fcc None mm (seg_rom asegs)) mo' g'.
    Proof.
      intros until e'. intros FR C8 ST MI ERR FRM FA PVA GM HL' TV' PBS' HB0 HB' HN'.
      eapply pstr_epi; [exact FR| exact C8| exact ST| exact MI| exact ERR| exact FRM| exact FA| exact PVA| exact GM|].
      exists LB', TRS', B', np', buf', len', off. split; [exact HL'|]. split; [exact TV'|]. left. split; [reflexivity|].
      split; [exists dep; exact (PBS_fold _ _ _ PBS')|]. split; [exact HB0|]. split; [exact HB'| exact HN'].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_qq : forall mm mo' g' (c0 : cell) (fcc : bv 32) LB' TRS' B' np' buf' len' bs'
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) e',
      FRAME mm c0 -> Cells.csize c0 = 8%nat -> stk asegs mm lo SPF -> mem_inv asegs mm -> rw_cells asegs mm AERRNO [C4 e'] -> frm0 fcc ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm -> gmono g g' ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> 3 + off + 1 <= len' -> len' < 2^31 -> len <= len' ->
      BB - (pb_pot len' - pb_pot len) <= B' -> np' <= np + (pb_npot len' - pb_npot len) ->
      LSCPS asegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (buf' + off)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x873f4) fcc None mm (seg_rom asegs)) mo' g'.
    Proof.
      intros until e'. intros FR C8 ST MI ERR FRM PVA GM HL' TV' HP' PBS' [ARR LEN'] ROOM L31 LL HB' HN'.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      (nelimp PN 3%nat; intros PN1 PN2 PN3). (nelimp PL 3%nat; intros PL1 PL2 PL3).
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) 4%nat; intros Y1 Y2 Y3 Y4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) as [_ SOB].
      pose proof (art_qq_shadow _ _ _ _ _ _ _ _ _ HL') as SOQ.
      (nelim (u8arr_split3 mm buf' bs' (Z.to_nat off) 3 ARR ltac:(lia)) 3%nat; intros A1 A2 A3).
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
      (nelim PO 22%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 DST _ ST2).
      rewrite SPFeq in MU2, ST2. unfold AINTRIN_STACK in MU2.
      replace (ret_pc (Z_to_bv 64 0x87404)) with (Z_to_bv 64 0x87404) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport asegs) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size]; rewrite C8; cbn; lia].
      eapply (rw_cells_transport asegs) in ERR; [| exact MU2| exact WM2| cbn; unfold AERRNO, ATP; lia].
      eapply (rw_cells_transport asegs) in PBS'; [| exact MU2| exact WM2| cbn; lia].
      apply (u8arr_transport asegs _ _ m2 _ _ A1) in MU2 as A1'; [| exact WM2| cbn [disjoint_from]; rewrite firstn_length_le by lia; lia].
      apply (u8arr_transport asegs _ _ m2 _ _ A3) in MU2 as A3'; [| exact WM2| cbn [disjoint_from]; rewrite length_skipn; lia].
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
      eapply pstr_ret1; [exact FR| exact C8| exact ST2| exact MI2| exact ERR| exact FRM| intros k Hk; reflexivity| exact PVA2| exact GM| exact HL2| exact TV'| exact HP'| exact PBS'| | exact L31| exact LL| | exact HB'| exact HN'].
      - split; [exact ARR2| rewrite !length_app, firstn_length_le, length_skipn by lia; cbn; lia].
      - exists 2. split; [lia|]. split; [lia|].
        rewrite nth_error_app2 by (rewrite firstn_length_le by lia; lia). rewrite firstn_length_le by lia.
        replace (Z.to_nat (off + 2) - Z.to_nat off)%nat with 2%nat by lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Notation LSTN pc mm fcv rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 SHB x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fcv None mm (seg_rom asegs)).

    (* [comment removed for export] *)
    Lemma n_584 : forall m1 mo1 fc j0 rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
      ninv m1 mo1 g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> frm0 fc ->
      LSCPS asegs POST (LSTN 0x87318 m1 fc rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros (HL & ST1 & MI1 & [e ERR] & PVA & SSZ1 & PBW1 & GM1 & TV1) FR PBS1 FRM.
      pose proof CEIL as CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'. try rewrite alloc_ceiling_eq in CEIL'.
      pose proof R as (R1 & _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta.
      eapply pstr_ret0; [exact FR| reflexivity| exact ST1| exact MI1| exact ERR| exact FRM| intros k Hk; reflexivity| exact PVA| exact GM1| exact HL| exact TV1| exact PBS1| right; split; [lia| exact HP]| |].
      - pose proof (pb_allow_ge_fail len ltac:((nelimp PN 3%nat; intros ? ? ?); rewrite INT_MAX_eq; lia)). rewrite PB_FAIL_eq in *. lia.
      - pose proof (pb_npallow_ge2 len ltac:((nelimp PN 3%nat; intros ? ? ?); rewrite INT_MAX_eq; lia)). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma n_grow : forall (m1 : word -> option byte) (mo1 : Model) fc (ns : Z) j0 (rav x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      ninv m1 mo1 g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> u8arr asegs m1 buf bs -> frm0 fc ->
      3 + off + 1 <= ns -> ns <= INT_MAX -> len < 3 + off + 1 -> (2 * len + 2 <= ns \/ ns = INT_MAX) ->
      LSCPS asegs POST (LSTN 0x87428 m1 fc rav x5 x6 x7 (Z_to_bv 64 (PB + 16)) x9 (Z_to_bv 64 buf) (Z_to_bv 64 PB) x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 ns) (SHA PB) (SHA (PB + 8)) (SHA (PB + 16)) x23 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros (HL & ST1 & MI1 & [e ERR] & PVA & SSZ1 & PBW1 & GM1 & TV1) FR PBS1 ARR FRM NS1 NS2 NR HG.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPtop as SPT. rewrite INT_MAX_eq in NS2, HG.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      assert (HBB : cost_realloc ns + cost_free <= BB).
      { pose proof (cost_realloc_le ns ltac:(lia)). pose proof (pb_allow_ge_fail len ltac:(rewrite INT_MAX_eq; lia)). rewrite PB_FAIL_eq, KRE_eq in *. rewrite cost_free_eq in *. lia. }
      pose proof cost_free_eq as CF.
      assert (NP2 : np + 2 <= NPMAX TI) by (pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)); lia).
      (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 56) SSZ1 ltac:(alia)) as Z56. asan_chk Z56. clear Z56.
      zstep. zstep. zstep. if_cases Kd; zify_cond Kd; [exfalso; unfold AREALLOC in Kd; lia|]. clear Kd.
      zstep. zstep.
      replace (ret_pc (Z_to_bv 64 AREALLOC)) with (wz AREALLOC) by (unfold wz, AREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      (* [comment removed for export] *)
      destruct (pb_head_CB _ _ _ _ _ PBS1) as [HD16 _].
      destruct (uwt_hook_frame16 m1 SPF (ASTACK_TOP sp0) PC0_REALLOC (PB + 16) (Z_to_bv 64 buf) (Z_to_bv 64 len)) as [tl UW].
      { replace (PB + 16 - 16) with PB by lia. exact (proj2 (proj1 HD16)). }
      { rewrite unsigned_lit by lia. lia. }
      { lia. }
      eapply lscps_bind.
      { eapply (art_realloc_ok AI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs) (tl := tl); rewrite ?unsigned_lit by lia;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact LEN | exact ST1 | exact ERR | exact MI1 | exact TP | reflexivity
                | exact UW
                | eapply (tinv_room_paid TI); [exact TV1| lia]
                | split; [lia| unfold PC0_REALLOC; lia]
                | alia | lia ]. }
      cbv beta. intros ms2 mo2 g2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 e2 TRS2 -> MI2 ST2 ERR2 GM2 TP2 RES)
.
      rewrite ?E1 in ST2. unfold AERRNO, ATP in ERR2.
      replace (ret_pc (Z_to_bv 64 0x87450)) with (Z_to_bv 64 0x87450) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TV2 : TINV TI (np + 1) TRS2) by (eapply (tinv_put_paid_or TI); [exact TV1| lia| exact TP2]).
      assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM1| exact GM2]).
      destruct RES as [(-> & HL2 & PR2) | (Bn & junk & -> & CR & NIN & _ & HL2 & PR2 & BLK)].
      - (* [comment removed for export] *)
        rewrite ?E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PBS1; [| left; cbn; lia].
        assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]]. }
        assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR2| exact SSZ1]).
        assert (PBW2 : pb_below m2 PB).
        { eapply (pb_below_pv_agree sp0 LB LF SPF); [eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; exact Hb]| exact PBW1| lia| lia]. }
        clear PVA PR2 MI1 ST1 ERR HL ARR SSZ1 PBW1 HD16 UW.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
        zstep. zstep. zstep.
        pose proof (stack_shb0 m2 (PB + 48) SSZ2 ltac:(alia)) as Z48. asan_chk Z48. clear Z48.
        zstep.
        pose proof (stack_shb0 m2 PB SSZ2 ltac:(alia)) as Z0. asan_chk Z0. clear Z0.
        zstep. zstep. zstep.
        replace (ret_pc (Z_to_bv 64 AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        (nelim PBW2 4%nat; intros w1 w2 BY16 Hw1).
        destruct (uwt_hook_frame16 m2 SPF (ASTACK_TOP sp0) PC0_FREE PB w1 w2 BY16 Hw1 ltac:(lia)) as [tl2 UW2].
        eapply lscps_bind.
        { eapply (art_free_ok AI) with (lo := lo) (A := buf) (n := len) (tl := tl2); rewrite ?unsigned_lit by lia;
            first [ exact HL2 | eapply perm_in_head; exact HP | exact ST2 | exact ERR2 | exact MI2 | exact TP | reflexivity
                  | exact UW2
                  | eapply (tinv_room_paid TI); [exact TV2| lia]
                  | split; [lia| unfold PC0_FREE; lia]
                  | rewrite cost_free_eq in *; lia
                  | alia | lia ]. }
        cbv beta. intros ms3 mo3 g3 PO.
        (nelim PO 25%nat; intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 TRS3 -> MI3 ST3 ERR3 PR3 GM3 TP3 HL3)
.
        rewrite ?E1 in ST3, PR3. unfold AERRNO, ATP in ERR3.
        replace (ret_pc (Z_to_bv 64 0x87548)) with (Z_to_bv 64 0x87548) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL2))) as HPr.
        assert (TV3 : TINV TI (np + 1 + 1) TRS3) by (eapply (tinv_put_paid_or TI); [exact TV2| lia| left; exact TP3]).
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FR; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in PBS1; [| left; cbn; lia].
        assert (PVA3 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m3).
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_of_cj_pres; [exact PR3| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]]. }
        assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR3| exact SSZ2]).
        clear PVA2 MI2 ST2 ERR2 HL2 SSZ2 BY16 UW2.
        (* [comment removed for export] *)
        destruct (pb_head_CB _ _ _ _ _ PBS1) as [HD TL].
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
          eapply MSX with (lo := lo) (d := PB) (c := 0) (n := 16); clear MSX; rewrite ?unsigned_lit by lia;
            first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL3 end | exact MI3 | exact ST3 | exact HD | reflexivity
                  | lazymatch goal with |- app_range _ _ => app_rng0 end
                  | apply wr_range_ok_high; lia
                  | intros _; eapply sh_zero_shadow_ok; [exact SSZ3| alia| lia| lia]
                  | alia | lia ]. }
        cbv beta. intros ms4 PO4.
        (nelim PO4 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m4 -> MU4 WM4 MI4 ZB ST4).
        rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
        replace (ret_pc (Z_to_bv 64 0x87558)) with (Z_to_bv 64 0x87558) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply (rw_cells_transport asegs) in FR; [| exact MU4| exact WM4| cbn; lia].
        eapply (rw_cells_transport asegs) in ERR3; [| exact MU4| exact WM4| cbn; lia].
        eapply (rw_cells_transport asegs) in TL; [| exact MU4| exact WM4| cbn; lia].
        pose proof (pb_head_zero _ _ _ ZB TL) as PBS4.
        assert (HL4 : ART AI sp0 SPB (cb_remove buf LB) LF TRS3 (BB - cost_realloc ns - cost_free) m4 mo3 g3).
        { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]]; right; left; cbn; lia. }
        assert (PVA4 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m4).
        { eapply pv_agree_trans; [exact PVA3|]. eapply (pv_agree_of_munch2 AI); [exact HL3| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]| exact MU4| exact WM4| right; left; lia| right; right; try rewrite alloc_ceiling_eq; lia| lia| lia]. }
        clear MU4 WM4.
        zstep. zstep. apply evt_done. cbv beta.
        eapply pstr_ret0; [exact FR| reflexivity| exact ST4| exact MI4| exact ERR3| exact FRM| intros k Hk; reflexivity| exact PVA4| eapply gmono_trans; [exact GM2'| exact GM3]| exact HL4| exact TV3| exact PBS4| left; split; [reflexivity| exact HPr]| |].
        + unfold pb_allow. rewrite PB_FAIL_eq, cost_free_eq. pose proof (cost_realloc_le ns ltac:(lia)). rewrite KRE_eq in *.
          pose proof (pb_pot_mono len INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)). lia.
        + pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        rewrite ?E1 in PR2. unfold wz.
        (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
        pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PBS1; [| left; cbn; lia].
        assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]]. }
        assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR2| exact SSZ1]).
        clear PVA PR2 MI1 ST1 ERR HL ARR SSZ1 PBW1 HD16 UW.
        rewrite (Z.min_l len ns) in BLK by lia.
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        pose proof (stack_shb0 m2 (PB + 8) SSZ2 ltac:(alia)) as Z8. asan_chk Z8. clear Z8.
        zstep. zstep.
        pose proof (stack_shb0 m2 PB SSZ2 ltac:(alia)) as Z0. asan_chk Z0. clear Z0.
        zstep.
        pose proof (stack_shb0 m2 (PB + 16) SSZ2 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. zstep.
        apply evt_done. cbv beta.
        lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mc _) _ _ => rename mc into m3 end.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
        assert (HP2 : Permutation ((Bn, ns) :: LR) ((Bn, ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
        eapply pstr_qq; [exact FR| reflexivity| exact ST2| exact MI2| exact ERR2| exact FRM| | exact GM2'| | exact TV2| exact HP2| exact PBS1| | lia| lia| lia| |].
        + eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia].
        + eapply (art_frame_store AI); [exact HL2| exact MU| exact WM| alia| lia].
        + split; [exact ARR2| rewrite length_app, La, Lb; lia].
        + pose proof (pb_pot_grow len ns ltac:(lia) ltac:(rewrite INT_MAX_eq; lia) ltac:(rewrite INT_MAX_eq; exact HG)). lia.
        + pose proof (pb_npot_grow len ns ltac:(lia) ltac:(rewrite INT_MAX_eq; lia) ltac:(rewrite INT_MAX_eq; exact HG)). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma n_tail4c : forall (m1 : word -> option byte) (mo1 : Model) fc j0 (rav x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
      ninv m1 mo1 g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> u8arr asegs m1 buf bs -> frm0 fc ->
      (len = 0 \/ off < len) ->
      LSCPS asegs POST (LSTN 0x872e0 m1 fc rav x5 x6 x7 (Z_to_bv 64 (PB + 16)) x9 (Z_to_bv 64 buf) (Z_to_bv 64 PB) (Z_to_bv 64 len) x13 x14 x15 x16 x17
                            x18 (SHA PB) (SHA (PB + 8)) x22 x23 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros NI FR PBS1 ARR FRM OFL. (nelimp NI 9%nat; intros HL ST1 MI1 [e ERR] PVA SSZ1 PBW1 GM1 TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPtop as SPT. pose proof INT_MAX_eq as IM.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 16) SSZ1 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep. zstep. if_cases Kroom; zify_cond Kroom.
      - (* [comment removed for export] *)
        zstep. apply evt_done. cbv beta.
        eapply pstr_qq; [exact FR| reflexivity| exact ST1| exact MI1| exact ERR| exact FRM| exact PVA| exact GM1| exact HL| exact TV1| exact HP| exact PBS1| split; [exact ARR| exact LEN]| lia| lia| lia| lia| lia].
      - (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (stack_shchk m1 (PB + 32) 4 SSZ1 ltac:(alia)) as CK32. asan_chk CK32.
        zstep. zstep. if_cases Kna; zify_cond Kna; [| exfalso; apply Kna; reflexivity]. clear Kna.
        zstep. zstep. if_cases K30; zify_cond K30.
        + zstep. apply evt_done. cbv beta.
          rewrite Z.shiftr_div_pow2 in K30 by lia.
          eapply n_grow; [exact NI| exact FR| exact PBS1| exact ARR| exact FRM| rewrite Z.shiftl_mul_pow2 by lia; lia| rewrite Z.shiftl_mul_pow2 by lia; lia| lia| left; rewrite Z.shiftl_mul_pow2 by lia; lia].
        + zstep. zstep. if_cases K31; zify_cond K31.
          * apply evt_done. cbv beta. eapply n_584; [exact NI| exact FR| exact PBS1| exact FRM].
          * zstep. zstep. zstep. apply evt_done. cbv beta.
            rewrite Z.shiftr_div_pow2 in K30, K31 by lia.
            eapply n_grow; [exact NI| exact FR| exact PBS1| exact ARR| exact FRM| lia| lia| lia| right; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_null : forall (m1 : word -> option byte) (mo1 : Model) fc j0 (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ninv m1 mo1 g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> u8arr asegs m1 buf bs -> frm0 fc ->
      LSCPS asegs POST (LSTN 0x87290 m1 fc ra x5 x6 x7 s0 s1 x10 (Z_to_bv 64 PB) x12 x13 x14 x15 x16 x17 s2 s4 s5 s6 s7 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros NI FR PBS1 ARR FRM. (nelimp NI 9%nat; intros HL ST1 MI1 [e ERR] PVA SSZ1 PBW1 GM1 TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPtop as SPT.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof (stack_shb0 m1 PB SSZ1 ltac:(alia)) as Z0. asan_chk Z0. clear Z0.
      zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 8) SSZ1 ltac:(alia)) as Z8. asan_chk Z8. clear Z8.
      zstep. zstep. zstep. if_cases Klen; zify_cond Klen.
      - apply evt_done. cbv beta. eapply n_tail4c; [exact NI| exact FR| exact PBS1| exact ARR| exact FRM| left; exact Klen].
      - (* [comment removed for export] *)
        zstep. zstep.
        pose proof (stack_shb0 m1 (PB + 16) SSZ1 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. if_cases Koff; zify_cond Koff.
        + apply evt_done. cbv beta. eapply n_584; [exact NI| exact FR| exact PBS1| exact FRM].
        + apply evt_done. cbv beta. eapply n_tail4c; [exact NI| exact FR| exact PBS1| exact ARR| exact FRM| right; exact Koff].
    Qed.
  End Call.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].
