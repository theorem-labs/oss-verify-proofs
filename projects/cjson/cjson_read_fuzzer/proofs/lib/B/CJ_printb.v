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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_print.
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
Lemma pb_tot_val : PB_FAIL + pb_pot INT_MAX = 34431246520.
Proof. vm_compute. reflexivity. Qed.
Lemma PRINT_COST_val : PRINT_COST = 60129542144.
Proof. reflexivity. Qed.
Lemma pb_npot_IM_val' : pb_npot INT_MAX = 32.
Proof. vm_compute. reflexivity. Qed.

Lemma pbuf_budget : forall pre, 0 <= pre < 2^31 ->
  cost_malloc pre + pb_allow pre + cost_free <= PRINT_COST /\ 0 <= pb_pot pre /\ pb_pot pre <= pb_pot INT_MAX /\ 2 <= pb_npallow pre <= 34.
Proof.
  intros pre H. pose proof (cost_malloc_le4 pre ltac:(lia)). unfold CL24_TAX in *. pose proof (pb_pot_nonneg pre ltac:(lia)).
  pose proof (pb_pot_mono pre INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)).
  pose proof (pb_npot_mono 0 pre ltac:(lia) ltac:(rewrite INT_MAX_eq; lia)). pose proof (pb_npot_mono pre INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)).
  unfold pb_allow, pb_npallow. pose proof pb_tot_val. rewrite PRINT_COST_val, cost_free_eq, pb_npot_IM_val' in *.
  assert (pb_npot 0 = 0) by reflexivity. lia.
Qed.

Ltac blia := unfold pb_allow in *; rewrite ?PRINT_NP_eq, ?PB_FAIL_eq, ?cost_free_eq in *; lia.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis PV : print_value_stmt AI TI.
  Hypothesis MEMCPY : asan_memcpy_spec.

  Section Call.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR B : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
              (n : nat) (p lo pre : Z) (errv : word).
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
    Hypothesis PRE : 0 <= pre < 2^31.

    Notation PB := (bv_unsigned sp + -96).
    Notation POST := (print_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np B0 n p lo m g).
    Notation SAVED mm := (rw_cells bsegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation LST pc Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 PB) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fv (Z_to_bv 64 pc) fcv None mm (seg_rom bsegs)).

    Lemma st_malloc : STAT TI [PC0_MALLOC; 0x83ec4].
    Proof. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail SPRINT)))))). Qed.
    Lemma st_free : STAT TI [PC0_FREE; 0x83f2c].
    Proof. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail SPRINT))))))). Qed.

    Lemma PBeq : bv_unsigned (Z_to_bv 64 PB) = PB.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma N1 : (1 <= n)%nat.
    Proof. destruct n; [| lia]. exfalso. apply PNZ. exact (proj1 (cj_chain_zero_budget _ _ _ _ CH)). Qed.

    (* [comment removed for export] *)
    Lemma pbuf_epi : forall (pc : Z) mm mo' g' LB' TRS' B' np' e' SC Fc fcc (r : word)
        rav x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
      (pc = 0x83f08 \/ pc = 0x83f30) ->
      rw_cells bsegs mm PB SC -> cells_size SC = 64%nat -> SAVED mm ->
      stk bsegs mm lo PB -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B ->
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> np <= np' <= np + PRINT_NP -> gmono g g' -> B0 - PRINT_COST <= B' ->
      ((r = wz 0 /\ Permutation (B ++ LR) LB') \/ (exists q k, r = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB')) ->
      LSCPS bsegs POST (LST pc Fc fcc mm rav x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31) mo' g'.
    Proof.
      intros until x31. intros HPC FS SZ FV ST MI ERR FRM FA PR CHm HL TV NP GM HB OUT.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      assert (FR : rw_cells bsegs mm PB (SC ++ [C8 s2; C8 s1; C8 s0; C8 ra])).
      { apply rw_cells_app_join; [exact FS|]. rewrite SZ. replace (PB + Z.of_nat 64%nat) with (bv_unsigned sp + -32) by lia. exact FV. }
      clear FS FV.
      pose proof (rw_cells_merge bsegs mm PB [] SC [C8 s2; C8 s1; C8 s0; C8 ra] FR) as FR'. clear FR. rewrite SZ in FR'. cbn [app] in FR'.
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct HPC as [-> | ->]; do 5 zstep; release_frame FR' ST (bv_unsigned sp); zstep; apply evt_done; apply lscps_done; unfold print_post;
        nexists 23%nat; (split; [reflexivity|]);
        (split; [exact MI|]); (split; [exact FRM|]); (split; [exact FA|]); (split; [exact ST|]); (split; [exact ERR|]); (split; [exact PR|]); (split; [exact CHm|]);
        (split; [exact HL|]); (split; [exact TV|]); (split; [exact NP|]); (split; [exact GM|]); (split; [exact HB|]); exact OUT.
    Qed.

    (* [comment removed for export] *)
    Lemma pbuf_main : forall (mo : Model) (fc : bv 32) (fw t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g -> TINV TI np TRS ->
      stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m AERRNO [C4 errv] -> mem_inv bsegs m -> frm0 fc ->
      sh_zero m alloc_ceiling (2^47) ->
      LSCPS bsegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 pre) fw a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x83e8c) fc None m (seg_rom bsegs)) mo g.
    Proof.
      intros until t6. intros HL TV ST ERR MI FRM SSZ.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APRINT_STACK, APV_STACK in LO'.
      pose proof PBeq as E1. pose proof N1 as N1'. pose proof cost_free_eq as CF.
      (nelim (pbuf_budget pre PRE) 4%nat; intros BUD POT0 POTM NPA). rewrite PRINT_NP_eq in NPR.
      assert (SPT : bv_unsigned sp + 16 <= sp0 + 4096) by lia.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ CH) 3%nat; intros R1 R2 R3).
      assert (BB : forall A' n', In (A', n') LB -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros ? _ ? ?). lia. }
      assert (INB : forall b, In b B -> In b LB). { intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
      assert (INLR : forall b, In b (B ++ LR) -> In b LB). { intros b Hb. eapply Permutation_in; [exact HP| exact Hb]. }
      (* [comment removed for export] *)
      assert (PLO : p + 64 <= alloc_ceiling).
      { pose proof (BB p 64 (INB _ (cj_chain_head_block _ _ _ _ _ CH PNZ))). lia. }
      try rewrite alloc_ceiling_eq in PLO.
      unfold AERRNO, ATP in ERR. pose proof (conj ERR I) as ERRbox. clear ERR.
      pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 96%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 4; 4; 24; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 5 zstep. zstep. fix_lit_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB LF TRS B0 m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]).
      assert (ERR1 : rw_cells bsegs m1 (6146416 - 164) [C4 errv]) by (eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]).
      assert (PR1 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m1).
      { eapply (cj_pres_munch_below AI); [exact HL| exact INLR| exact MU| exact WM| | lia| lia]. constructor; [cbn; lia| constructor]. }
      assert (SSZ1 : sh_zero m1 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
      pose proof (cj_chain_frame _ _ m1 _ _ _ _ CH MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CH1.
      clear MU WM.
      pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL1) as (HK & _). unfold AHOOKS in HK.
      lazymatch type of HK with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK end.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
        destruct (rw_cells_app_split m1 PB [c0; c1; c2; c3; c4; c5] (c6 :: rest) FR) as [FA0 FR1];
        cbn [cells_size Cells.csize Nat.add] in FR1;
        destruct (rw_cells_app_split m1 _ [c6] rest FR1) as [F6 FV];
        cbn [cells_size Cells.csize Nat.add] in FV
      end.
      clear FR FR1.
      replace (PB + Z.of_nat 40%nat) with (bv_unsigned sp + -56) in F6 by lia.
      replace (PB + Z.of_nat 40%nat + Z.of_nat 24%nat) with (bv_unsigned sp + -32) in FV by lia.
      (* [comment removed for export] *)
      zstep. if_cases Kn; zify_cond Kn; [exfalso; rewrite ?Z_to_bv_signed, ?bv_swrap_small in Kn by (unfold bv_half_modulus, bv_modulus; cbn [Z.of_N]; lia); lia|]. clear Kn.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (ret_pc (wz AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { eapply (art_malloc_ok AI) with (lo := lo) (n := pre) (tl := []); rewrite ?unsigned_lit by lia;
          first [ exact HL1 | exact ST | exact ERR1 | exact MI | exact TP | reflexivity
                | unfold pb_allow in *; rewrite ?PB_FAIL_eq, ?cost_free_eq in *; (cut_to SPB1 CEIL PRE HB0 LO' BUD POTM BOT TOP SPAL; lia)
                | split; [lia| unfold PC0_MALLOC; lia]
                | apply uwt_hook_nonfp; lia
                | eapply (tinv_room TI); [exact TV| exact st_malloc]
                | alia | lia ]. }
      cbv beta. intros ms3 mo3 g3 PO.
      (nelim PO 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 e3 TRS3 -> MI3 ST3 ERR3 PR3 GM3 TP3 RES)
.
      rewrite ?E1 in ST3, PR3. unfold AERRNO, ATP in ERR3.
      replace (ret_pc (Z_to_bv 64 0x83ec4)) with (Z_to_bv 64 0x83ec4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TV3 : TINV TI np TRS3) by (eapply (tinv_put_or TI); [exact TV| exact st_malloc| exact TP3]).
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FA0; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in F6; [| left; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FV; [| left; cbn; lia].
      assert (PR3' : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m3).
      { eapply cj_pres_trans; [exact PR1|]. eapply cj_pres_weaken; [exact PR3| lia| exact INLR| intros f Hf; exact Hf]. }
      assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR3| exact SSZ1]).
      assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B) by (eapply cj_chain_pres; [exact CH1| exact PR3| exact INB]).
      clear PR1 PR3 SSZ1 CH1 MI ST ERR1 HL1 HK.
      destruct RES as [[-> HL3]|(A & junkA & -> & CR & NIN & _ & HL3 & BLK & _)].
      - (* [comment removed for export] *)
        unfold wz. pose proof (munch_refl [(PB, PB + 8)] m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. fix_lit_store. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
        assert (HL4 : ART AI sp0 SPB LB LF TRS3 (B0 - cost_malloc pre) m4 mo3 g3) by (eapply (art_frame_store AI); [exact HL3| exact MU| exact WM| alia| lia]).
        assert (PR4 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m4).
        { eapply cj_pres_trans; [exact PR3'|]. eapply (cj_pres_munch_below AI); [exact HL3| exact INLR| exact MU| exact WM| | lia| lia]. constructor; [cbn; lia| constructor]. }
        pose proof (cj_chain_frame _ _ m4 _ _ _ _ CH3 MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CH4.
        apply evt_done. cbv beta.
        lazymatch goal with FA0c : rw_cells bsegs m4 PB ?cs6 |- _ =>
          pose proof (rw_cells_app_join m4 PB cs6 _ FA0c ltac:(cbn [cells_size Cells.csize Nat.add]; replace (PB + Z.of_nat 40%nat) with (bv_unsigned sp + -56) by lia; exact F6)) as FS
        end.
        eapply (pbuf_epi 0x83f08); [left; reflexivity| exact FS| reflexivity| exact FV| exact ST3| exact MI3| exact ERR3| exact FRM| intros; reflexivity| exact PR4| exact CH4| exact HL4| exact TV3| blia| exact GM3| blia|].
        left. split; [reflexivity| exact HP].
      - (* [comment removed for export] *)
        unfold wz. (nelimp CR 4%nat; intros CR1 CR2 CR3 CR4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in CR1. bandM. sepM. try rewrite alloc_ceiling_eq in CR4.
        pose proof (proj1 (proj1 (proj1 BLK))) as LJ. cbn [cells_wf cell_wf] in LJ.
        assert (BBX : forall A' n', In (A', n') ((A, pre) :: LB) -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
        { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL3 Hin) 4%nat; intros ? _ ? ?). lia. }
        pose proof (munch_refl [(PB, PB + 40)] m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        zstep. zstep. fix_lit_store. zstep. fix_lit_store. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3s end.
        assert (HLs : ART AI sp0 SPB ((A, pre) :: LB) LF TRS3 (B0 - cost_malloc pre) m3s mo3 g3) by (eapply (art_frame_store AI); [exact HL3| exact MU| exact WM| alia| lia]).
        assert (PRs : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m3s).
        { eapply cj_pres_trans; [exact PR3'|]. eapply (cj_pres_munch_below AI); [exact HL3| intros b Hb; right; exact (INLR _ Hb)| exact MU| exact WM| | lia| lia]. constructor; [cbn; lia| constructor]. }
        assert (SSZs : sh_zero m3s alloc_ceiling (2^47)).
        { eapply sh_zero_stack_munch; [exact SSZ3| exact MU|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
        pose proof (cj_chain_frame _ _ m3s _ _ _ _ CH3 MU WM ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CHs.
        assert (MAs : magree (in_cblock ((A, pre) :: LB)) m3 m3s).
        { eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). cbn. pose proof (BBX A' n' Hin). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in *. lia. }
        clear MU WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { pose proof MEMCPY as MC. unfold asan_memcpy_spec, memcpy_contract in MC.
          lazymatch type of F6 with rw_cells _ _ _ [CB _ ?j6] =>
          eapply MC with (lo := lo) (d := bv_unsigned sp + -56) (s := 0xa5cc0) (n := 24) (src := hooks_bytes) (junk := j6) end; clear MC; rewrite ?unsigned_lit by lia;
            first [ eapply (art_icpt_cells AI); exact HLs | exact HLs | exact F6 | reflexivity
                  | exact (hooks_bytes_at _ (art_cjst AI _ _ _ _ _ _ _ _ _ HLs))
                  | left; unfold lowmem_range, KLOWSHADOW_BEG; (cut_to CEIL' LO'; lia)
                  | app_rng AI
                  | apply wr_range_ok_high; lia
                  | intros _; exact (proj1 (proj2 (art_global_shadow AI _ _ _ _ _ _ _ _ _ HLs)))
                  | intros _; eapply stack_shadow_ok; [exact SSZs| alia| lia| lia]
                  | unfold wz; f_equal; (cut_to CEIL; lia)
                  | assumption | alia | lia ]. }
        cbv beta. intros ms4 PO4.
        (nelim PO4 22%nat; intros v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m4 -> MU4 WM4 MI4 BLK4 _ ST4).
        rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
        replace (ret_pc (Z_to_bv 64 0x83ef4)) with (Z_to_bv 64 0x83ef4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (hooks_recast _ _ BLK4) as FH. clear BLK4.
        lazymatch goal with FA0c : rw_cells bsegs m3s PB _ |- _ =>
          eapply (rw_cells_transport bsegs) in FA0c; [| exact MU4| exact WM4| cbn; lia]; rename FA0c into FA4 end.
        eapply (rw_cells_transport bsegs) in FV; [| exact MU4| exact WM4| cbn; lia].
        eapply (rw_cells_transport bsegs) in ERR3; [| exact MU4| exact WM4| cbn; lia].
        assert (HL4 : ART AI sp0 SPB ((A, pre) :: LB) LF TRS3 (B0 - cost_malloc pre) m4 mo3 g3).
        { eapply (art_frame AI); [exact HLs| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]]; right; left; cbn; lia. }
        assert (PR4 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m4).
        { eapply cj_pres_trans; [exact PRs|]. eapply (cj_pres_munch_below AI); [exact HLs| intros b Hb; right; exact (INLR _ Hb)| exact MU4| exact WM4| | lia| lia].
          constructor; [cbn; lia| constructor; [cbn; lia| constructor]]. }
        assert (SSZ4 : sh_zero m4 alloc_ceiling (2^47)).
        { eapply sh_zero_stack_munch; [exact SSZs| exact MU4|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]]. }
        pose proof (cj_chain_frame _ _ m4 _ _ _ _ CHs MU4 WM4 ltac:(intros A' n' Hin; cbn; pose proof (BB A' n' (INB _ Hin)); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; try rewrite alloc_ceiling_eq in *; lia)) as CH4.
        assert (MA4 : magree (in_cblock ((A, pre) :: LB)) m3s m4).
        { eapply magree_of_munch; [exact MU4| exact WM4|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). cbn. pose proof (BBX A' n' Hin). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in *. lia. }
        assert (ARR4 : u8arr bsegs m4 A junkA).
        { pose proof (u8arr_of_rw_cells bsegs _ _ _ _ BLK) as [AB AW]. split.
          - eapply bytes_at_magree; [exact MA4| exact AB|]. intros a Ha. exists A, pre. split; [left; reflexivity| lia].
          - eapply wr_at_magree; [exact MA4| exact AW|]. intros a Ha. exists A, pre. split; [left; reflexivity| lia]. }
        (* [comment removed for export] *)
        assert (FS4 : pb_struct m4 PB A pre 0 0 fw).
        { unfold pb_struct, wz. apply (rw_cells_app_join m4 PB [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 pre); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 fw]); [exact FA4|].
          cbn [cells_size Cells.csize Nat.add]. replace (PB + Z.of_nat 40%nat) with (bv_unsigned sp + -56) by lia. exact FH. }
        clear MU4 WM4 MAs HLs PRs SSZs CHs BLK FA4 FH.
        (* [comment removed for export] *)
        apply evt_done. cbv beta.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. zstep.
        change (Z_to_bv 64 540488) with (wz PVALUE_ENTRY).
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { pose proof (PV n) as X. unfold print_value_at in X.
          eapply X with (lo := lo) (LR := B ++ LR) (B := B) (bs := junkA) (buf := A) (len := pre) (off := 0) (dep := 0) (CH := []) (PB := PB);
            clear X; rewrite ?E1; rewrite ?unsigned_lit by lia;
            first [ exact HL4 | exact FS4 | exact CH4 | exact PNZ | exact ST4 | exact ERR3 | exact MI4 | exact TP | exact FRM | exact SSZ4 | exact TV3 | exact LFR | exact SP0 | exact BOT
                  | apply perm_skip; exact HP
                  | split; [exact ARR4| rewrite LJ; lia]
                  | unfold pb_nums; (cut_to PRE SP0 SPS0 LO' SPAL TOP CEIL NPR NPA HB0 CF BUD; lia)
                  | intros b Hb; apply in_or_app; left; exact Hb
                  | unfold pb_place; (cut_to SPB1 SPB2; lia)
                  | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
                  | intros HH; exfalso; lia
                  | exact I
                  | unfold chain_link; rewrite ?unsigned_lit by lia; (cut_to CEIL' LO' PLO; lia)
                  | apply Forall_nil
                  | unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia
                  | unfold pb_allow in *; rewrite cost_free_eq in *; lia
                  | reflexivity | alia | lia ]. }
        cbv beta. intros ms5 mo5 g5 PO.
        (nelim PO 30%nat; intros w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 F5 fc5 m5 e5 -> MI5 FRM5 FA5 ST5 ERR5 PVA CH5 GM5 _ OUT)
.
        rewrite ?E1 in ST5, PVA. unfold AERRNO, ATP in ERR5.
        replace (ret_pc (Z_to_bv 64 0x83f00)) with (Z_to_bv 64 0x83f00) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply (pv_agree_rw_cells_stack _ _ _ _ _ _ _ _ _ PVA) in FV; [| lia| cbn; lia| cbn; lia].
        assert (PR5 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m5).
        { eapply cj_pres_trans; [exact PR4|]. eapply (cj_pres_of_pv_agree AI); [exact HL4| intros b Hb; right; exact (INLR _ Hb)| exact PVA| lia| lia| alia]. }
        assert (GM5' : gmono g g5) by (eapply gmono_trans; [exact GM3| exact GM5]).
        clear PVA PR4 ST4 MI4 ERR3 HL4 SSZ4 CH4 MA4 ARR4 FS4.
        destruct OUT as (LB5 & TRS5 & B5 & np5 & buf5 & len5 & off5 & HL5 & TV5 & [(-> & [dep5 PBS5] & HBUF & HB5 & HN5) | (-> & (bs5 & HP5 & PBS5 & PD5 & PN5 & NUL5) & LEN5 & HB5 & HN5)]).
        + (* [comment removed for export] *)
          unfold pb_struct, wz in PBS5. unfold wz.
          pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL5) as (HK5 & _). unfold AHOOKS in HK5.
          lazymatch type of HK5 with cells_at _ ?mx ?a ?cs => change (ro_cells bsegs mx a cs) in HK5 end.
          eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
          zstep. zstep. zstep.
          replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          destruct HBUF as [[-> HPX]|[BNZ HPX]].
          * (* [comment removed for export] *)
            eapply lscps_bind.
            { eapply (art_free_null AI) with (lo := lo) (tl := []); rewrite ?unsigned_lit by lia;
                first [ exact HL5 | exact ST5 | exact ERR5 | exact MI5 | exact TP | reflexivity
                      | split; [lia| unfold PC0_FREE; lia]
                      | apply uwt_hook_nonfp; lia
                      | alia | lia ]. }
            cbv beta. intros ms6 mo6 g6 PO.
            (nelim PO 23%nat; intros x0 x1' x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5' x6 m6 -> MI6 ST6 ERR6 PR6 GM6 HL6).
            rewrite ?E1 in ST6, PR6.
            replace (ret_pc (Z_to_bv 64 0x83f2c)) with (Z_to_bv 64 0x83f2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR6) in PBS5; [| left; cbn; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR6) in FV; [| left; cbn; lia].
            assert (PR7 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m6).
            { eapply cj_pres_trans; [exact PR5|]. eapply cj_pres_weaken; [exact PR6| lia| intros b Hb; eapply Permutation_in; [exact HPX| exact Hb]| intros f Hf; exact Hf]. }
            assert (CH6 : cj_chain CJ_PRINTABLE m6 n p B).
            { eapply cj_chain_pres; [exact CH5| exact PR6|]. intros b Hb. eapply Permutation_in; [exact HPX|]. apply in_or_app. left. exact Hb. }
            eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
            eapply (pbuf_epi 0x83f30 _ _ _ _ _ _ (Z.max np np5)); [right; reflexivity| exact PBS5| reflexivity| exact FV| exact ST6| exact MI6| exact ERR6| exact FRM5| exact FA5| exact PR7| exact CH6| exact HL6
                                | eapply (tinv_mono TI); [exact TV5| lia]| blia| eapply gmono_trans; [exact GM5'| exact GM6]| (cut_on [PNZ CEIL' LO' N1' BUD R1 CR1 HB5] blia)|].
            left. split; [reflexivity| exact HPX].
          * (* [comment removed for export] *)
            (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL5 (perm_in_head _ _ _ HPX)) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
            eapply lscps_bind.
            { eapply (art_free_ok AI) with (lo := lo) (A := buf5) (n := len5) (tl := []); rewrite ?unsigned_lit by (lia_on SP0 SPS0 CEIL' LO' R1 R3);
                first [ exact HL5 | eapply perm_in_head; exact HPX | exact ST5 | exact ERR5 | exact MI5 | exact TP | reflexivity
                      | unfold pb_allow in *; rewrite cost_free_eq in *; (cut_to SPB1 CEIL HB0 LO' BUD HB5 BOT TOP SPAL; lia)
                      | split; [lia| unfold PC0_FREE; lia]
                      | apply uwt_hook_nonfp; lia
                      | eapply (tinv_room TI); [exact TV5| exact st_free]
                      | alia | lia ]. }
            cbv beta. intros ms6 mo6 g6 PO.
            (nelim PO 25%nat; intros x0 x1' x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5' x6 m6 TRS6 -> MI6 ST6 ERR6 PR6 GM6 TP6 HL6).
            rewrite ?E1 in ST6, PR6.
            replace (ret_pc (Z_to_bv 64 0x83f2c)) with (Z_to_bv 64 0x83f2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            pose proof (perm_cb_remove _ _ _ _ HPX (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL5))) as HP6.
            apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR6) in PBS5; [| left; cbn; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR6) in FV; [| left; cbn; lia].
            assert (PR7 : cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m6).
            { eapply cj_pres_trans; [exact PR5|]. eapply cj_pres_weaken; [exact PR6| lia| intros b Hb; eapply Permutation_in; [exact HP6| exact Hb]| intros f Hf; exact Hf]. }
            assert (CH6 : cj_chain CJ_PRINTABLE m6 n p B).
            { eapply cj_chain_pres; [exact CH5| exact PR6|]. intros b Hb. eapply Permutation_in; [exact HP6|]. apply in_or_app. left. exact Hb. }
            eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
            eapply (pbuf_epi 0x83f30 _ _ _ _ _ _ (Z.max np np5)); [right; reflexivity| exact PBS5| reflexivity| exact FV| exact ST6| exact MI6| exact ERR6| exact FRM5| exact FA5| exact PR7| exact CH6| exact HL6
                                | eapply (tinv_mono TI); [eapply (tinv_put TI); [exact TV5| exact st_free| exact TP6]| lia]| blia| eapply gmono_trans; [exact GM5'| exact GM6]
                                | blia|].
            left. split; [reflexivity| exact HP6].
        + (* [comment removed for export] *)
          unfold pb_struct, wz in PBS5. unfold wz. (nelim PN5 3%nat; intros PN1 PN2 PN3).
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL5 (perm_in_head _ _ _ HP5)) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM.
          pose proof (pb_npot_mono len5 INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)) as NPM5. rewrite pb_npot_IM_val' in NPM5.
          pose proof (pb_pot_mono len5 INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)) as PM5.
          pose proof (pb_npot_mono 0 pre ltac:(lia) ltac:(rewrite INT_MAX_eq; lia)) as NP0. assert (NZ0 : pb_npot 0 = 0) by reflexivity.
          eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          zstep. apply evt_done. cbv beta.
          eapply (pbuf_epi 0x83f08 _ _ _ _ _ _ (Z.max np np5)); [left; reflexivity| exact PBS5| reflexivity| exact FV| exact ST5| exact MI5| exact ERR5| exact FRM5| exact FA5| exact PR5| exact CH5| exact HL5
                              | eapply (tinv_mono TI); [exact TV5| lia]| blia| exact GM5'| blia|].
          right. exists buf5, len5. split; [reflexivity|]. split; [lia| exact HP5].
    Qed.
  End Call.

  Theorem pbuffered_spec : pbuffered_stmt AI TI.
  Proof.
    unfold pbuffered_stmt, print_pre_stmt. intros until errv.
    intros HL HP CH PNZ NMAX SPB1 SPB2 SPAL SP0 TOP S0LE SPS0 RA1 RA2 ST CEIL BOT LO ERR MI TP FRM SSZ TV NPR SPRINT LFR HB0 A0 nelH_; (nelim nelH_ 3%nat; intros pre -> PRE).
    unfold wz, PBUFD_ENTRY in *. subst a0.
    eapply pbuf_main; eassumption.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APRINT_STACK, APV_STACK, AMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK in *; lia.
Ltac blia := unfold pb_allow in *; rewrite ?PRINT_NP_eq, ?PB_FAIL_eq, ?cost_free_eq in *; lia.
