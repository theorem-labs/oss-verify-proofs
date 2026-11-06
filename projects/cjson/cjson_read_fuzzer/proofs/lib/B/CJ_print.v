(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APRINT_STACK, APV_STACK, AMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK in *; lia.
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep;
  first [ if_cases G; zify_cond G; [ solve [exfalso; lia] | ]
        | if_cases G; zify_cond G; [ | solve [exfalso; lia] ]
        | if_cases G; zify_cond G; try (exfalso; lia) ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Definition CRMAX : Z := 4 * INT_MAX + KRE.
Lemma print_budget : cost_malloc 256 + pb_allow 256 + CRMAX + cost_free <= PRINT_COST.
Proof. vm_compute. discriminate. Qed.
Lemma pb_allow_256_unfold : pb_allow 256 = PB_FAIL + (pb_pot INT_MAX - pb_pot 256).
Proof. reflexivity. Qed.
Lemma pb_allow_256_val : pb_allow 256 = 34413909176.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_pot_256_val : pb_pot 256 = 17337344.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_pot_IM_val : pb_pot INT_MAX = 25839144952.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_npot_256_val : pb_npot 256 = 8.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_npot_IM_val : pb_npot INT_MAX = 32.
Proof. vm_compute. reflexivity. Qed.
Lemma cm256_eq : cost_malloc 256 = 1344.
Proof. reflexivity. Qed.
Lemma pb_npallow_256 : pb_npallow 256 = 26.
Proof. reflexivity. Qed.
Lemma PRINT_NP_eq : PRINT_NP = 64.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac blia := pose proof print_budget; rewrite ?cm256_eq, ?pb_allow_256_val, ?cost_free_eq in *; unfold CRMAX, pb_allow in *;
             rewrite ?pb_pot_256_val, ?pb_pot_IM_val, ?INT_MAX_eq, ?KRE_eq, ?PB_FAIL_eq, ?cost_free_eq in *; lia.

(* [comment removed for export] *)
Lemma mid_zero_recast : forall m A,
  rw_cells bsegs m A [CB (Z.to_nat 24) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 24))] ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

Definition hooks_bytes : list byte := cells_bytes [C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)].
Lemma hooks_bytes_length : length hooks_bytes = 24%nat.
Proof. reflexivity. Qed.
Lemma hooks_recast : forall m A,
  rw_cells bsegs m A [CB (Z.to_nat 24) hooks_bytes] -> rw_cells bsegs m A [C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity]. Qed.
Lemma hooks_bytes_at : forall m, ACJST m -> bytes_at bsegs m AHOOKS hooks_bytes.
Proof. intros m (HK & _). exact (proj2 HK). Qed.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis PV : print_value_stmt AI TI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.
  Hypothesis STRLEN : strlen_icpt_spec.

  Section Call.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR B : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
              (n : nat) (p lo : Z) (errv : word).
    Hypothesis HP : Permutation (B ++ LR) LB.
    Hypothesis CH : cj_chain CJ_PRINTABLE m n p B.
    Hypothesis PNZ : p <> 0.
    Hypothesis NMAX : (n <= 1001)%nat.
    Hypothesis SPB1 : bv_unsigned sp <= SPB.
    Hypothesis SPB2 : SPB < 2^62.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 < ASTACK_TOP sp0.
    Hypothesis SPS0 : bv_unsigned sp + 16 <= sp0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - APRINT_STACK n.
    Hypothesis TP : tp = wz ATP.
    Hypothesis NPR : np + PRINT_NP <= NPMAX TI.
    Hypothesis SPRINT : Forall (STAT TI) S_PRINT_CONST.
    Hypothesis LFR : lf_room 1 LF (Z.of_nat n).
    Hypothesis HB0 : PRINT_COST <= B0.

    Notation SPF := (bv_unsigned sp + -128).
    Notation PB := (bv_unsigned sp + -120).
    Notation POST := (print_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np B0 n p lo m g).
    Notation J0 mm j0 := (rw_cells bsegs mm (bv_unsigned sp + -128) [CB 8 j0]).
    Notation SAVED mm := (rw_cells bsegs mm (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l o d fw := (rw_cells bsegs mm (bv_unsigned sp + -120)
       [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d); C4 (Z_to_bv 64 0); C4 fw;
        C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)]).
    Notation LST pc Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fv (Z_to_bv 64 pc) fcv None mm (seg_rom bsegs)).

    (* [comment removed for export] *)
    Lemma st_malloc : STAT TI [PC0_MALLOC; 0x83d58].
    Proof. exact (Forall_inv SPRINT). Qed.
    Lemma st_realloc : STAT TI [PC0_REALLOC; 0x83dc8].
    Proof. exact (Forall_inv (Forall_inv_tail SPRINT)). Qed.
    Lemma st_free : STAT TI [PC0_FREE; 0x83e4c].
    Proof. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail SPRINT))))). Qed.

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma N1 : (1 <= n)%nat.
    Proof. destruct n; [| lia]. exfalso. apply PNZ. exact (proj1 (cj_chain_zero_budget _ _ _ _ CH)). Qed.

    (* [comment removed for export] *)
    Lemma print_epi : forall mm mo' g' LB' TRS' B' np' e' j0 SC Fc fcc (r : word)
        rav x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      J0 mm j0 -> rw_cells bsegs mm PB SC -> cells_size SC = 64%nat -> SAVED mm ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> np <= np' <= np + PRINT_NP -> gmono g g' -> B0 - PRINT_COST <= B' ->
      ((r = wz 0 /\ Permutation (B ++ LR) LB') \/ (exists q k, r = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB')) ->
      LSCPS bsegs POST (LST 0x83e50 Fc fcc mm rav x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo' g'.
    Proof.
      intros until x31. intros FJ FS SZ FV ST MI ERR FRM FA PR CHm HL TV NP GM HB OUT.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      assert (F2 : rw_cells bsegs mm PB (SC ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
      { apply rw_cells_app_join; [exact FS|]. rewrite SZ. replace (PB + Z.of_nat 64%nat) with (bv_unsigned sp + -56) by lia. exact FV. }
      assert (FR : rw_cells bsegs mm SPF ([CB 8 j0] ++ SC ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
      { apply rw_cells_app_join; [exact FJ|]. cbn [cells_size Cells.csize Nat.add]. replace (SPF + Z.of_nat 8%nat) with PB by lia. exact F2. }
      clear FJ FS FV F2. cbn [app] in FR.
      pose proof (rw_cells_merge bsegs mm SPF [CB 8 j0] SC [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FR'. clear FR. rewrite SZ in FR'. cbn [app] in FR'.
      eapply lscps_step_evt. cbv beta delta [mkR].
      do 8 zstep.
      release_frame FR' ST (bv_unsigned sp).
      zstep.
      apply evt_done. apply lscps_done. unfold print_post.
      nexists 23%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split; [exact FA|]. split; [exact ST|]. split; [exact ERR|]. split; [exact PR|]. split; [exact CHm|].
      split; [exact HL|]. split; [exact TV|]. split; [exact NP|]. split; [exact GM|]. split; [exact HB|]. exact OUT.
    Qed.
    (* [comment removed for export] *)
    Lemma print_fail : forall mm mo' g' LBX TRSX BX npX e' j0 (b l o d : Z) fw Fc fcc
        rav x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      J0 mm j0 -> PBS mm b l o d fw -> SAVED mm ->
      stk bsegs mm lo SPF -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      ART AI sp0 SPB LBX LF TRSX BX mm mo' g' -> TINV TI npX TRSX -> np <= npX <= np + PRINT_NP -> gmono g g' ->
      B0 - PRINT_COST + cost_free <= BX ->
      ((b = 0 /\ Permutation (B ++ LR) LBX) \/ (b <> 0 /\ Permutation ((b, l) :: B ++ LR) LBX)) ->
      LSCPS bsegs POST (LST 0x83e3c Fc fcc mm rav x5 x6 x7 (Z_to_bv 64 AHOOKS) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo' g'.
    Proof.
      intros until x31. intros FJ FS FV ST MI ERR FRM FA PR CHm HL TV NP GM HB HBUF.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      pose proof SPFeq as E1. pose proof N1 as N1'. pose proof cost_free_eq as CF.
      assert (SPT : bv_unsigned sp + 16 <= sp0 + 4096) by lia.
      pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL) as (HK & _). unfold AHOOKS in HK |- *.
      lazymatch type of HK with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK end.
      unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct HBUF as [[-> HPX]|[BNZ HPX]].
      - zstep. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply print_epi; [exact FJ| exact FS| reflexivity| exact FV| exact ST| exact MI| exact ERR| exact FRM| exact FA| exact PR| exact CHm| exact HL| exact TV| exact NP| exact GM| lia|].
        left. split; [reflexivity| exact HPX].
      - (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
        zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        zstep. zstep.
        replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { eapply (art_free_ok AI) with (lo := lo) (A := b) (n := l) (tl := []); rewrite ?unsigned_lit by (lia_on SP0 SPS0 CEIL' LO');
            first [ exact HL | eapply perm_in_head; exact HPX | exact ST | exact ERR | exact MI | exact TP | reflexivity
                  | rewrite cost_free_eq in *; unfold PRINT_COST in *; (cut_to SPB1 CEIL HB0 HB LO' BOT TOP SPAL; lia)
                  | split; [lia| unfold PC0_FREE; lia]
                  | apply uwt_hook_nonfp; lia
                  | eapply (tinv_room TI); [exact TV| exact st_free]
                  | alia | lia ]. }
        cbv beta. intros ms2 mo2 g2 PO.
        (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
        rewrite ?E1 in ST2, PR2.
        replace (ret_pc (Z_to_bv 64 0x83e4c)) with (Z_to_bv 64 0x83e4c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HPX (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP3.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FJ; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FS; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FV; [| left; cbn; lia].
        assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
        { eapply cj_chain_pres; [exact CHm| exact PR2|]. intros bb Hb. eapply Permutation_in; [exact HP3|]. apply in_or_app; left; exact Hb. }
        assert (PR' : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m2).
        { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia| | intros f Hf; exact Hf]. intros bb Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. apply evt_done. cbv beta.
        eapply print_epi; [exact FJ| exact FS| reflexivity| exact FV| exact ST2| exact MI2| exact ERR2| exact FRM| exact FA| exact PR'| exact CH2| exact HL2
                          | eapply (tinv_put TI); [exact TV| exact st_free| exact TP2] | exact NP| eapply gmono_trans; [exact GM| exact GM2]| lia|].
        left. split; [reflexivity| exact HP3].
    Qed.
    (* [comment removed for export] *)
    Lemma budget_after_pv : forall len5 B5, 0 <= len5 < 2^31 ->
      B0 - cost_malloc 256 - (pb_pot len5 - pb_pot 256) <= B5 -> B0 - PRINT_COST + CRMAX + cost_free <= B5 /\ 0 <= PB_FAIL.
    Proof.
      intros len5 B5 HL HB. pose proof print_budget as PBud. rewrite pb_allow_256_unfold in PBud.
      pose proof (pb_pot_mono len5 INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)). unfold CRMAX in *. rewrite PB_FAIL_eq, INT_MAX_eq, KRE_eq in *. rewrite cost_free_eq in *. lia.
    Qed.

    Lemma cost_realloc_crmax : forall k, 0 <= k <= INT_MAX -> cost_realloc k <= CRMAX.
    Proof. intros k Hk. unfold CRMAX. pose proof (cost_realloc_le k ltac:(lia)). lia. Qed.

    (* [comment removed for export] *)
    Lemma print_ok : forall m5 mo5 g5 LB5 TRS5 B5 np5 e5 j0 (buf5 len5 off5 : Z) (bs5 : list byte) fw Fc fcc
        rav x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      J0 m5 j0 -> PBS m5 buf5 len5 off5 0 fw -> SAVED m5 ->
      pb_data m5 buf5 len5 bs5 -> pb_nums len5 off5 0 -> pb_nul bs5 len5 off5 ->
      Permutation ((buf5, len5) :: B ++ LR) LB5 -> ART AI sp0 SPB LB5 LF TRS5 B5 m5 mo5 g5 -> TINV TI np5 TRS5 -> np <= np5 <= np + PRINT_NP ->
      B0 - cost_malloc 256 - (pb_pot len5 - pb_pot 256) <= B5 ->
      stk bsegs m5 lo SPF -> mem_inv bsegs m5 -> rw_cells bsegs m5 AERRNO [C4 e5] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m5 -> cj_chain CJ_PRINTABLE m5 n p B -> gmono g g5 ->
      LSCPS bsegs POST (LST 0x83d8c Fc fcc m5 rav x5 x6 x7 (Z_to_bv 64 AHOOKS) x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo5 g5.
    Proof.
      intros until x31. intros FJ FS FV PD PN NUL HP5 HL TV NP HB5 ST MI ERR FRM FA PR CHm GM.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      pose proof SPFeq as E1. pose proof N1 as N1'. pose proof cost_free_eq as CF. pose proof cm256_eq as CM.
      assert (SPT : bv_unsigned sp + 16 <= sp0 + 4096) by lia.
      (nelim PN 3%nat; intros PN1 PN2 PN3). destruct (budget_after_pv len5 B5 ltac:(lia) HB5) as [HB5' _].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP5)) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
      assert (BB : forall A' n', In (A', n') LB5 -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros ? _ ? ?). lia. }
      assert (INB : forall b, In b B -> In b LB5). { intros b Hb. eapply Permutation_in; [exact HP5|]. right. apply in_or_app. left. exact Hb. }
      unfold AERRNO, ATP in ERR. unfold AHOOKS.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
      zstep. zstep. rewrite (zb_lxor_ones buf5) by lia. ugd.              (* [comment removed for export] *)
      zstep. zstep.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (strlen_off_ok AI STRLEN) with (lo := lo) (buf := buf5) (len := len5) (off := off5) (bs := bs5); rewrite ?unsigned_lit by lia;
          first [ exact HL | eapply perm_in_head; exact HP5 | exact (proj1 PD) | exact (proj2 PD) | exact NUL | exact MI | exact ST | lia | alia
                | unfold wz; f_equal; lia | reflexivity ]. }
      cbv beta. intros ms7 PO7.
      (nelim PO7 24%nat; intros k t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m7 -> MU7 WM7 MI7 ST7 K0 K1 KN).
      rewrite ?unsigned_lit in MU7, ST7 by lia. unfold ASTRFN_STACK in MU7.
      replace (ret_pc (Z_to_bv 64 0x83da8)) with (Z_to_bv 64 0x83da8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport bsegs) in FJ; [| exact MU7| exact WM7| cbn; lia].
      eapply (rw_cells_transport bsegs) in FS; [| exact MU7| exact WM7| cbn; lia].
      eapply (rw_cells_transport bsegs) in FV; [| exact MU7| exact WM7| cbn; lia].
      eapply (rw_cells_transport bsegs) in ERR; [| exact MU7| exact WM7| cbn; lia].
      assert (PD7 : pb_data m7 buf5 len5 bs5).
      { destruct PD as [[AB AW] L5]. split; [| exact L5]. split; [| eapply wr_at_transport; [exact AW| exact WM7]].
        eapply (bytes_at_transport bsegs); [exact AB| exact MU7| cbn; lia]. }
      assert (HL7 : ART AI sp0 SPB LB5 LF TRS5 B5 m7 mo5 g5) by (eapply (art_frame_store AI); [exact HL| exact MU7| exact WM7| alia| lia]).
      assert (PR7 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m7).
      { eapply cj_pres_trans; [exact PR|]. eapply (cj_pres_munch_below AI); [exact HL| intros b Hb; eapply Permutation_in; [exact HP5| right; exact Hb]| exact MU7| exact WM7| | lia| lia].
        constructor; [cbn; lia| constructor]. }
      pose proof (cj_chain_frame _ _ m7 _ _ _ _ CHm MU7 WM7 ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; lia)) as CH7.
      clear MU7 WM7 MI ST HL PR CHm.
      (* [comment removed for export] *)
      pose proof (munch_refl [(PB + 16, PB + 24)] m7) as MU. pose proof (wmono_refl bsegs m7) as WM.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m8 end.
      assert (HL8 : ART AI sp0 SPB LB5 LF TRS5 B5 m8 mo5 g5) by (eapply (art_frame_store AI); [exact HL7| exact MU| exact WM| alia| lia]).
      assert (PR8 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m8).
      { eapply cj_pres_trans; [exact PR7|]. eapply (cj_pres_munch_below AI); [exact HL7| intros b Hb; eapply Permutation_in; [exact HP5| right; exact Hb]| exact MU| exact WM| | lia| lia].
        constructor; [cbn; lia| constructor]. }
      pose proof (cj_chain_frame _ _ m8 _ _ _ _ CH7 MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; lia)) as CH8.
      assert (PD8 : pb_data m8 buf5 len5 bs5).
      { destruct PD7 as [[AB AW] L5]. split; [| exact L5]. split; [| eapply wr_at_transport; [exact AW| exact WM]].
        eapply (bytes_at_transport bsegs); [exact AB| exact MU| cbn; lia]. }
      pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL8) as (HK & _). unfold AHOOKS in HK.
      lazymatch type of HK with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK end.
      clear MU WM HL7 PR7 CH7 PD7.
      (* [comment removed for export] *)
      zstep. zstep. if_cases Kr; zify_cond Kr; [exfalso; unfold wz, AREALLOC in Kr; rewrite ?unsigned_lit in Kr by lia; lia|]. clear Kr.
      zstep. zstep. zstep. zstep.
      replace (ret_pc (wz AREALLOC)) with (wz AREALLOC) by (unfold wz, AREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { eapply (art_realloc_ok AI) with (lo := lo) (A := buf5) (k := len5) (n := off5 + k + 1) (old := bs5) (tl := []); rewrite ?unsigned_lit by (lia_on SP0 SPS0 CEIL' LO');
          first [ exact HL8 | eapply perm_in_head; exact HP5 | exact (proj1 (proj1 PD8)) | exact (proj2 PD8) | exact ST7 | exact ERR | exact MI7 | exact TP | reflexivity
                | unfold wz; f_equal; (cut_to SPB1 CEIL LO' PN1 PN2 K0 K1 BOT TOP SPAL; lia)
                | pose proof (cost_realloc_crmax (off5 + k + 1) ltac:(rewrite INT_MAX_eq; (lia_on PN1 PN2 K0 K1))); (cut_to HB0 CF HB5' H; lia)
                | split; [lia| unfold PC0_REALLOC; lia]
                | apply uwt_hook_nonfp; lia
                | eapply (tinv_room TI); [exact TV| exact st_realloc]
                | alia | lia ]. }
      cbv beta. intros ms9 mo9 g9 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m9 e9 TRS9 -> MI9 ST9 ERR9 GM9 TP9 RES)
.
      rewrite ?E1 in ST9. unfold AERRNO, ATP in ERR9.
      replace (ret_pc (Z_to_bv 64 0x83dc8)) with (Z_to_bv 64 0x83dc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TV9 : TINV TI np5 TRS9) by (eapply (tinv_put_or TI); [exact TV| exact st_realloc| exact TP9]).
      pose proof (perm_cb_remove _ _ _ _ HP5 (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL8))) as HPr.
      destruct RES as [(-> & HL9 & PR9) | (Bn & junk & -> & CR & NIN & _ & HL9 & PR9 & BLK)].
      - (* [comment removed for export] *)
        rewrite ?E1 in PR9. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FJ; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FS; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FV; [| left; cbn; lia].
        assert (PR10 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m9).
        { eapply cj_pres_trans; [exact PR8|]. eapply cj_pres_weaken; [exact PR9| lia| intros b Hb; eapply Permutation_in; [exact HP5| right; exact Hb]| intros f Hf; exact Hf]. }
        assert (CH9 : cj_chain CJ_PRINTABLE m9 n p B).
        { eapply cj_chain_pres; [exact CH8| exact PR9|]. intros b Hb. apply INB. exact Hb. }
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
        zstep. apply evt_done. cbv beta.
        eapply print_fail; [exact FJ| exact FS| exact FV| exact ST9| exact MI9| exact ERR9| exact FRM| exact FA| exact PR10| exact CH9| exact HL9| exact TV9| exact NP
                           | eapply gmono_trans; [exact GM| exact GM9] | | right; split; [lia| exact HP5]].
        pose proof (cost_realloc_crmax (off5 + k + 1) ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        rewrite ?E1 in PR9. unfold wz.
        (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FJ; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FS; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FV; [| left; cbn; lia].
        assert (PR10 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m9).
        { eapply cj_pres_trans; [exact PR8|]. eapply cj_pres_weaken; [exact PR9| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]| intros f Hf; exact Hf]. }
        assert (CH9 : cj_chain CJ_PRINTABLE m9 n p B).
        { eapply cj_chain_pres; [exact CH8| exact PR9|]. intros b Hb. eapply Permutation_in; [exact HPr|]. apply in_or_app. left. exact Hb. }
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
        apply evt_done. cbv beta.
        eapply print_epi; [exact FJ| exact FS| reflexivity| exact FV| exact ST9| exact MI9| exact ERR9| exact FRM| exact FA| exact PR10| exact CH9| exact HL9| exact TV9| exact NP
                          | eapply gmono_trans; [exact GM| exact GM9] | |].
        + pose proof (cost_realloc_crmax (off5 + k + 1) ltac:(rewrite INT_MAX_eq; lia)). lia.
        + right. exists Bn, (off5 + k + 1). split; [reflexivity|]. split; [lia|]. apply perm_skip. exact HPr.
    Qed.
    (* [comment removed for export] *)
    Lemma print_main : forall (mo : Model) (fc : bv 32) (fw t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g -> TINV TI np TRS ->
      stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m AERRNO [C4 errv] -> mem_inv bsegs m -> frm0 fc ->
      sh_zero m alloc_ceiling (2^47) -> bv_unsigned s0 <= bv_unsigned sp ->
      LSCPS bsegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) fw a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x83cfc) fc None m (seg_rom bsegs)) mo g.
    Proof.
      intros until t6. intros HL TV ST ERR MI FRM SSZ S0LE.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      pose proof SPFeq as E1. pose proof N1 as N1'. pose proof cost_free_eq as CF. pose proof cm256_eq as CM.
      assert (SPT : bv_unsigned sp + 16 <= sp0 + 4096) by lia.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ CH) 3%nat; intros R1 R2 R3).
      assert (BB : forall A' n', In (A', n') LB -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros ? _ ? ?). lia. }
      assert (INB : forall b, In b B -> In b LB). { intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
      assert (INLR : forall b, In b (B ++ LR) -> In b LB). { intros b Hb. eapply Permutation_in; [exact HP| exact Hb]. }
      unfold AERRNO, ATP in ERR. pose proof (conj ERR I) as ERRbox. clear ERR.
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 128%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 24; 24; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 8 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB LF TRS B0 m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]).
      assert (ERR1 : rw_cells bsegs m1 (6146416 - 164) [C4 errv]) by (eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]).
      assert (PR1 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m1).
      { eapply (cj_pres_munch_below AI); [exact HL| exact INLR| exact MU| exact WM| | lia| lia]. constructor; [cbn; lia| constructor]. }
      assert (SSZ1 : sh_zero m1 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
      pose proof (cj_chain_frame _ _ m1 _ _ _ _ CH MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CH1.
      clear MU WM.
      pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL1) as SB. shbase_split SB.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
        destruct (rw_cells_app_split m1 SPF [c0] (c1 :: c2 :: c3 :: c4 :: rest) FR) as [FJ FR1];
        cbn [cells_size Cells.csize Nat.add] in FR1;
        destruct (rw_cells_app_split m1 _ [c1; c2] (c3 :: c4 :: rest) FR1) as [FBL FR2];
        cbn [cells_size Cells.csize Nat.add] in FR2;
        destruct (rw_cells_app_split m1 _ [c3] (c4 :: rest) FR2) as [F3 FR3];
        cbn [cells_size Cells.csize Nat.add] in FR3;
        destruct (rw_cells_app_split m1 _ [c4] rest FR3) as [F4 FV];
        cbn [cells_size Cells.csize Nat.add] in FV
      end.
      clear FR FR1 FR2 FR3.
      replace (SPF + Z.of_nat 8%nat) with PB in FBL by lia.
      replace (SPF + Z.of_nat 8%nat + Z.of_nat 16%nat) with (bv_unsigned sp + -104) in F3 by lia.
      replace (SPF + Z.of_nat 8%nat + Z.of_nat 16%nat + Z.of_nat 24%nat) with (bv_unsigned sp + -80) in F4 by lia.
      replace (SPF + Z.of_nat 8%nat + Z.of_nat 16%nat + Z.of_nat 24%nat + Z.of_nat 24%nat) with (bv_unsigned sp + -56) in FV by lia.
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
        lazymatch type of F3 with rw_cells _ _ _ [CB _ ?j3] =>
        eapply MSX with (lo := lo) (d := bv_unsigned sp + -104) (c := 0) (n := 24) (junk := j3) end; clear MSX; rewrite ?unsigned_lit by lia;
          first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL1 end | exact MI | exact ST | exact F3 | reflexivity
                | app_rng AI
                | apply wr_range_ok_high; lia
                | intros _; eapply sh_zero_shadow_ok; [exact SSZ1| alia| lia| lia]
                | unfold wz; f_equal; lia
                | alia | lia ]. }
      cbv beta. intros ms2 PO2.
      (nelim PO2 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 ZB ST2).
      rewrite ?unsigned_lit in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.
      replace (ret_pc (Z_to_bv 64 0x83d40)) with (Z_to_bv 64 0x83d40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (mid_zero_recast _ _ ZB) as FZ. clear ZB.
      eapply (rw_cells_transport bsegs) in FJ; [| exact MU2| exact WM2| cbn; lia].
      eapply (rw_cells_transport bsegs) in FBL; [| exact MU2| exact WM2| cbn; lia].
      eapply (rw_cells_transport bsegs) in F4; [| exact MU2| exact WM2| cbn; lia].
      eapply (rw_cells_transport bsegs) in FV; [| exact MU2| exact WM2| cbn; lia].
      eapply (rw_cells_transport bsegs) in ERR1; [| exact MU2| exact WM2| cbn; lia].
      assert (HL2 : ART AI sp0 SPB LB LF TRS B0 m2 mo g).
      { eapply (art_frame AI); [exact HL1| exact MU2| exact WM2|]. constructor; [| constructor; [| constructor]]; right; left; cbn; lia. }
      assert (PR2 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m2).
      { eapply cj_pres_trans; [exact PR1|]. eapply (cj_pres_munch_below AI); [exact HL1| exact INLR| exact MU2| exact WM2| | lia| lia].
        constructor; [cbn; lia| constructor; [cbn; lia| constructor]]. }
      assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ1| exact MU2|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]]. }
      pose proof (cj_chain_frame _ _ m2 _ _ _ _ CH1 MU2 WM2 ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CH2.
      pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL2) as (HK & _). unfold AHOOKS in HK.
      lazymatch type of HK with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK end.
      clear MU2 WM2 MI ST HL1 PR1 SSZ1 CH1 F3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      replace (ret_pc (wz AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { sepM. eapply (art_malloc_ok AI) with (lo := lo) (n := 256) (tl := []); rewrite ?unsigned_lit by (lia_on SP0 SPS0 CEIL' LO');
          first [ exact HL2 | exact ST2 | exact ERR1 | exact MI2 | exact TP | reflexivity
                | (cut_to SPB1 CEIL PNZ HB0 CEIL' LO' N1' R1 BOT TOP SPAL; (cut_to SPB1 CEIL HB0 LO' BOT TOP SPAL; blia))
                | split; [lia| unfold PC0_MALLOC; lia]
                | apply uwt_hook_nonfp; lia
                | eapply (tinv_room TI); [exact TV| exact st_malloc]
                | alia | lia ]. }
      cbv beta. intros ms3 mo3 g3 PO.
      (nelim PO 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 e3 TRS3 -> MI3 ST3 ERR3 PR3 GM3 TP3 RES)
.
      rewrite ?E1 in ST3, PR3. unfold AERRNO, ATP in ERR3.
      replace (ret_pc (Z_to_bv 64 0x83d58)) with (Z_to_bv 64 0x83d58) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TV3 : TINV TI np TRS3) by (eapply (tinv_put_or TI); [exact TV| exact st_malloc| exact TP3]).
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FJ; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FBL; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FZ; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in F4; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FV; [| left; cbn; lia].
      assert (PR3' : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m3).
      { eapply cj_pres_trans; [exact PR2|]. eapply cj_pres_weaken; [exact PR3| lia| exact INLR| intros f Hf; exact Hf]. }
      assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR3| exact SSZ2]).
      assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B) by (eapply cj_chain_pres; [exact CH2| exact PR3| exact INB]).
      clear PR2 PR3 SSZ2 CH2 MI2 ST2 ERR1 HL2 HK.
      (* [comment removed for export] *)
      assert (STORES : forall (bufv : Z) (LBX : list cblock) (BX : Z),
        ART AI sp0 SPB LBX LF TRS3 BX m3 mo3 g3 -> (forall b, In b LB -> In b LBX) -> 0 <= bufv < 2^64 ->
        (forall t5 t6' t7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m4,
           J0 m4 ltac:(lazymatch type of FJ with rw_cells _ _ _ [CB _ ?j] => exact j end) ->
           PBS m4 bufv 256 0 0 fw -> SAVED m4 ->
           ART AI sp0 SPB LBX LF TRS3 BX m4 mo3 g3 -> stk bsegs m4 lo SPF -> mem_inv bsegs m4 -> rw_cells bsegs m4 AERRNO [C4 e3] ->
           cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m4 -> sh_zero m4 alloc_ceiling (2^47) -> cj_chain CJ_PRINTABLE m4 n p B ->
           magree (in_cblock LBX) m3 m4 ->
           LSCPS bsegs POST (LST 0x83d78 F fc m4 (Z_to_bv 64 0x83d78) t5 t6' t7 (Z_to_bv 64 AHOOKS) (Z_to_bv 64 p) (Z_to_bv 64 (bv_unsigned sp + -80)) u11 u12 u13 u14 u15 u16 u17
                                 fw (Z_to_bv 64 bufv) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 256) u28 u29 u30 u31) mo3 g3) ->
        LSCPS bsegs POST (LST 0x83d58 F fc m3 (Z_to_bv 64 0x83d58) t0' t1' t2' (Z_to_bv 64 AHOOKS) (Z_to_bv 64 p) (Z_to_bv 64 bufv) a1' a2' a3' a4' a5' a6' a7'
                               fw s3 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 256) t3' t4' t5' t6') mo3 g3).
      { intros bufv LBX BX HLX HLB BV K.
        assert (BBX : forall A' n', In (A', n') LBX -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
        { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLX Hin) 4%nat; intros ? _ ? ?). lia. }
        pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HLX) as CJX. pose proof CJX as (HK & _). unfold AHOOKS in HK |- *.
        lazymatch type of HK with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK end.
        pose proof (munch_refl [(PB, PB + 40)] m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. fix_lit_store. zstep. fix_lit_store. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3s end.
        assert (HLs : ART AI sp0 SPB LBX LF TRS3 BX m3s mo3 g3) by (eapply (art_frame_store AI); [exact HLX| exact MU| exact WM| alia| lia]).
        assert (PRs : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m3s).
        { eapply cj_pres_trans; [exact PR3'|]. eapply (cj_pres_munch_below AI); [exact HLX| intros b Hb; apply HLB; exact (INLR _ Hb)| exact MU| exact WM| | lia| lia]. constructor; [cbn; lia| constructor]. }
        assert (SSZs : sh_zero m3s alloc_ceiling (2^47)).
        { eapply sh_zero_stack_munch; [exact SSZ3| exact MU|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
        pose proof (cj_chain_frame _ _ m3s _ _ _ _ CH3 MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CHs.
        assert (MAs : magree (in_cblock LBX) m3 m3s).
        { eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). cbn. pose proof (BBX A' n' Hin). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in *. lia. }
        clear MU WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { pose proof MEMCPY as MC. unfold asan_memcpy_spec, memcpy_contract in MC.
          sepM. lazymatch type of F4 with rw_cells _ _ _ [CB _ ?j4] =>
          eapply MC with (lo := lo) (d := bv_unsigned sp + -80) (s := 0xa5cc0) (n := 24) (src := hooks_bytes) (junk := j4) end; clear MC; rewrite ?unsigned_lit by lia;
            first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HLs end | exact HLs | exact F4 | reflexivity
                  | exact (hooks_bytes_at _ (art_cjst AI _ _ _ _ _ _ _ _ _ HLs))
                  | left; unfold lowmem_range, KLOWSHADOW_BEG; (cut_to CEIL' LO'; lia)
                  | app_rng AI
                  | apply wr_range_ok_high; lia
                  | intros _; exact (proj1 (proj2 (art_global_shadow AI _ _ _ _ _ _ _ _ _ HLs)))
                  | intros _; eapply sh_zero_shadow_ok; [exact SSZs| alia| lia| lia]
                  | unfold wz; f_equal; (cut_to CEIL; lia)
                  | assumption | alia | lia ]. }
        cbv beta. intros ms4 PO4.
        (nelim PO4 22%nat; intros v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m4 -> MU4 WM4 MI4 BLK4 _ ST4).
        rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
        replace (ret_pc (Z_to_bv 64 0x83d78)) with (Z_to_bv 64 0x83d78) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (hooks_recast _ _ BLK4) as FH. clear BLK4.
        apply evt_done. cbv beta.
        lazymatch goal with FJc : rw_cells bsegs ?mq SPF [CB 8 _], FBLc : rw_cells bsegs _ PB [_; _], FZc : rw_cells bsegs _ (bv_unsigned sp + -104) [_; _; _; _], ERRc : rw_cells bsegs _ (6146416 - 164) _ |- _ =>
          eapply (rw_cells_transport bsegs) in FJc; [| exact MU4| exact WM4| cbn; lia];
          eapply (rw_cells_transport bsegs) in FBLc; [| exact MU4| exact WM4| cbn; lia];
          eapply (rw_cells_transport bsegs) in FZc; [| exact MU4| exact WM4| cbn; lia];
          eapply (rw_cells_transport bsegs) in ERRc; [| exact MU4| exact WM4| cbn; lia];
          eapply (rw_cells_transport bsegs) in FV; [| exact MU4| exact WM4| cbn; lia];
          eapply K;
          [ exact FJc
          | apply (rw_cells_app_join m4 PB [C8 (Z_to_bv 64 bufv); C8 (Z_to_bv 64 256)]); [exact FBLc|];
            cbn [cells_size Cells.csize Nat.add]; replace (PB + Z.of_nat 16%nat) with (bv_unsigned sp + -104) by lia;
            apply (rw_cells_app_join m4 (bv_unsigned sp + -104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 fw]); [exact FZc|];
            cbn [cells_size Cells.csize Nat.add]; replace (bv_unsigned sp + -104 + Z.of_nat 24%nat) with (bv_unsigned sp + -80) by lia; exact FH
          | exact FV
          | eapply (art_frame AI); [exact HLs| exact MU4| exact WM4|]; constructor; [| constructor; [| constructor]]; right; left; cbn; lia
          | exact ST4 | exact MI4 | exact ERRc
          | eapply cj_pres_trans; [exact PRs|]; eapply (cj_pres_munch_below AI); [exact HLs| intros b Hb; apply HLB; exact (INLR _ Hb)| exact MU4| exact WM4| | lia| lia];
            constructor; [cbn; lia| constructor; [cbn; lia| constructor]]
          | eapply sh_zero_stack_munch; [exact SSZs| exact MU4|]; constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]]
          | eapply cj_chain_frame; [exact CHs| exact MU4| exact WM4|]; intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia
          | eapply magree_trans; [exact MAs|]; eapply magree_of_munch; [exact MU4| exact WM4|]; intros a Ha nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr); cbn; pose proof (BBX A' n' Hin); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia ]
        end. }
      destruct RES as [[-> HL3]|(A & junkA & -> & CR & NIN & _ & HL3 & BLK & _)].
      - (* [comment removed for export] *)
        unfold wz. eapply (STORES 0 LB); [exact HL3| intros b Hb; exact Hb| lia|].
        intros until m4. intros FJ4 FS4 FV4 HL4 ST4 MI4 ERR4 PR4 SSZ4 CH4 MA4.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply print_fail; [exact FJ4| exact FS4| exact FV4| exact ST4| exact MI4| exact ERR4| exact FRM| intros; reflexivity| exact PR4| exact CH4| exact HL4| exact TV3| rewrite PRINT_NP_eq; lia| exact GM3
                           | blia
                           | left; split; [reflexivity| exact HP]].
      - (* [comment removed for export] *)
        unfold wz. (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
        eapply (STORES A ((A, 256) :: LB)); [exact HL3| intros b Hb; right; exact Hb| lia|].
        intros until m4. intros FJ4 FS4 FV4 HL4 ST4 MI4 ERR4 PR4 SSZ4 CH4 MA4.
        pose proof (proj1 (proj1 (proj1 BLK))) as LJ. cbn [cells_wf cell_wf] in LJ.
        assert (ARR4 : u8arr bsegs m4 A junkA).
        { pose proof (u8arr_of_rw_cells bsegs _ _ _ _ BLK) as [AB AW]. split.
          - eapply bytes_at_magree; [exact MA4| exact AB|]. intros a Ha. exists A, 256. split; [left; reflexivity| lia].
          - eapply wr_at_magree; [exact MA4| exact AW|]. intros a Ha. exists A, 256. split; [left; reflexivity| lia]. }
        pose proof (proj1 (proj1 (proj1 FJ4))) as L0. cbn [cells_wf cell_wf] in L0.
        clear BLK.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        zstep. zstep. zstep.
        change (Z_to_bv 64 540488) with (wz PVALUE_ENTRY).
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { pose proof (PV n) as X. unfold print_value_at in X.
          sepM. eapply X with (lo := lo) (LR := B ++ LR) (B := B) (bs := junkA) (buf := A) (len := 256) (off := 0) (dep := 0) (CH := []) (PB := PB);
            clear X; rewrite ?E1; rewrite ?unsigned_lit by lia;
            first [ exact HL4 | exact FS4 | exact CH4 | exact PNZ | exact ST4 | exact ERR4 | exact MI4 | exact TP | exact FRM | exact SSZ4 | exact TV3 | exact LFR | exact SP0 | exact BOT
                  | apply perm_skip; exact HP
                  | split; [exact ARR4| rewrite LJ; reflexivity]
                  | unfold pb_nums; (cut_to SP0 SPS0 LO' SPAL TOP CEIL; (cut_to SP0 SPS0 CEIL LO' SPAL TOP; lia))
                  | intros b Hb; apply in_or_app; left; exact Hb
                  | unfold pb_place; (cut_to SPB1 SPB2; lia)
                  | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
                  | intros HH; exfalso; lia
                  | intros _; exists (le_bytes_to_word ltac:(lazymatch type of FJ4 with rw_cells _ _ _ [CB _ ?j] => exact j end));
                    rewrite le8_of_bytes8 by first [exact L0 | exact (proj1 L0)];
                    let BJ := fresh in pose proof (proj2 (proj1 FJ4)) as BJ; cbn [cells_bytes cbytes app] in BJ; rewrite app_nil_r in BJ; exact BJ
                  | rewrite pb_npallow_256; rewrite PRINT_NP_eq in NPR; lia
                  | exact I
                  | unfold chain_link, AHOOKS; rewrite ?unsigned_lit by lia; (cut_to CEIL' LO'; lia)
                  | apply Forall_nil
                  | unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia
                  | (cut_to HB0; blia)
                  | reflexivity | alia | lia ]. }
        cbv beta. intros ms5 mo5 g5 PO.
        (nelim PO 30%nat; intros w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 F5 fc5 m5 e5 -> MI5 FRM5 FA5 ST5 ERR5 PVA CH5 GM5 _ OUT)
.
        rewrite ?E1 in ST5, PVA. unfold AERRNO, ATP in ERR5.
        replace (ret_pc (Z_to_bv 64 0x83d88)) with (Z_to_bv 64 0x83d88) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply (pv_agree_rw_cells_stack _ _ _ _ _ _ _ _ _ PVA) in FJ4; [| lia| cbn; lia| cbn; lia].
        apply (pv_agree_rw_cells_stack _ _ _ _ _ _ _ _ _ PVA) in FV4; [| lia| cbn; lia| cbn; lia].
        assert (PR5 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m5).
        { eapply cj_pres_trans; [exact PR4|]. eapply (cj_pres_of_pv_agree AI); [exact HL4| intros b Hb; right; exact (INLR _ Hb)| exact PVA| lia| lia| alia]. }
        assert (GM5' : gmono g g5) by (eapply gmono_trans; [exact GM3| exact GM5]).
        clear PVA PR4 ST4 MI4 ERR4 HL4 SSZ4 CH4 MA4 ARR4.
        destruct OUT as (LB5 & TRS5 & B5 & np5 & buf5 & len5 & off5 & HL5 & TV5 & [(-> & [dep5 PBS5] & HBUF & HB5 & HN5) | (-> & (bs5 & HP5 & PBS5 & PD5 & PN5 & NUL5) & LEN5 & HB5 & HN5)]).
        + (* [comment removed for export] *)
          unfold pb_struct, wz in PBS5. unfold wz.
          eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
          apply evt_done. cbv beta.
          eapply (print_fail _ _ _ _ _ _ (Z.max np np5)); [exact FJ4| exact PBS5| exact FV4| exact ST5| exact MI5| exact ERR5| exact FRM5| exact FA5| exact PR5| exact CH5| exact HL5
                             | eapply (tinv_mono TI); [exact TV5| lia]
                             | rewrite pb_npallow_256 in HN5; rewrite PRINT_NP_eq; lia| exact GM5' | | exact HBUF].
          (cut_on [PNZ CEIL' LO' N1' R1 C1 HB5] blia).
        + (* [comment removed for export] *)
          unfold pb_struct, wz in PBS5. unfold wz.
          eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          apply evt_done. cbv beta.
          pose proof (pb_npot_mono len5 INT_MAX ltac:((nelim PN5 3%nat; intros ? ? ?); rewrite INT_MAX_eq; lia) ltac:(lia)) as NPM5.
          rewrite pb_npot_IM_val in NPM5. rewrite pb_npot_256_val in HN5.
          eapply (print_ok _ _ _ _ _ _ (Z.max np np5)); [exact FJ4| exact PBS5| exact FV4| exact PD5| exact PN5| exact NUL5| exact HP5| exact HL5
                           | eapply (tinv_mono TI); [exact TV5| lia]
                           | rewrite PRINT_NP_eq; lia| rewrite cm256_eq; lia| exact ST5| exact MI5| exact ERR5| exact FRM5| exact FA5| exact PR5| exact CH5| exact GM5'].
    Qed.
  End Call.

  (* [comment removed for export] *)
  Theorem print_spec : print_pre_stmt AI TI PRINT_ENTRY (fun _ _ => True).
  Proof.
    unfold print_pre_stmt. intros until errv.
    intros HL HP CH PNZ NMAX SPB1 SPB2 SPAL SP0 TOP S0LE SPS0 RA1 RA2 ST CEIL BOT LO ERR MI TP FRM SSZ TV NPR SPRINT LFR HB0 A0 _.
    unfold wz, PRINT_ENTRY in *. subst a0.
    eapply print_main; eassumption.
  Qed.

  Theorem cjprint_spec : cjprint_stmt AI TI.
  Proof.
    unfold cjprint_stmt, print_pre_stmt. intros until errv.
    intros HL HP CH PNZ NMAX SPB1 SPB2 SPAL SP0 TOP S0LE SPS0 RA1 RA2 ST CEIL BOT LO ERR MI TP FRM SSZ TV NPR SPRINT LFR HB0 A0 _.
    unfold wz, CJPRINT_ENTRY in *. subst a0.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta.
    eapply print_main; eassumption.
  Qed.

  Theorem cjprintu_spec : cjprintu_stmt AI TI.
  Proof.
    unfold cjprintu_stmt, print_pre_stmt. intros until errv.
    intros HL HP CH PNZ NMAX SPB1 SPB2 SPAL SP0 TOP S0LE SPS0 RA1 RA2 ST CEIL BOT LO ERR MI TP FRM SSZ TV NPR SPRINT LFR HB0 A0 _.
    unfold wz, CJPRINTU_ENTRY in *. subst a0.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta.
    eapply print_main; eassumption.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APRINT_STACK, APV_STACK, AMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK in *; lia.
Ltac ugd := let G := fresh "G" in zstep;
  first [ if_cases G; zify_cond G; [ solve [exfalso; lia] | ]
        | if_cases G; zify_cond G; [ | solve [exfalso; lia] ]
        | if_cases G; zify_cond G; try (exfalso; lia) ].   (* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac blia := pose proof print_budget; rewrite ?cm256_eq, ?pb_allow_256_val, ?cost_free_eq in *; unfold CRMAX, pb_allow in *;
             rewrite ?pb_pot_256_val, ?pb_pot_IM_val, ?INT_MAX_eq, ?KRE_eq, ?PB_FAIL_eq, ?cost_free_eq in *; lia.
