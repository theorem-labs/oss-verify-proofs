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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_mem.
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

Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia.
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

(* [comment removed for export] *)
Lemma pb_head_CB : forall m PB b l cs,
  rw_cells bsegs m PB (C8 b :: C8 l :: cs) -> rw_cells bsegs m PB [CB 16 (le8 b ++ le8 l)] /\ rw_cells bsegs m (PB + 16) cs.
Proof.
  intros m PB b l cs H.
  destruct (rw_cells_app_split m PB [C8 b; C8 l] cs H) as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
  split; [| exact H2].
  pose proof (rw_cells_merge bsegs m PB [] [C8 b; C8 l] [] ltac:(rewrite app_nil_r; exact H1)) as M.
  cbn [app cells_size cells_bytes csize cbytes Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

Lemma le8_zero : le8 (wz 0) = repeat (Z_to_bv 8 (0 mod 256)) 8.
Proof. reflexivity. Qed.

Lemma pb_head_zero : forall m PB cs,
  rw_cells bsegs m PB [CB (Z.to_nat 16) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 16))] -> rw_cells bsegs m (PB + 16) cs ->
  rw_cells bsegs m PB (C8 (wz 0) :: C8 (wz 0) :: cs).
Proof.
  intros m PB cs H1 H2.
  assert (H1' : rw_cells bsegs m PB [C8 (wz 0); C8 (wz 0)]) by (eapply rw_cells_recast; [exact H1| cbn; repeat split; exact I| reflexivity]).
  exact (rw_cells_app_join m PB [C8 (wz 0); C8 (wz 0)] cs H1' H2).
Qed.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis MEMSET : asan_memset_spec.

  Section Call.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : word -> option byte) (g : lghost)
              (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
              (PB buf len off dep : Z) (fw : word) (bs : list byte) (needed lo : Z) (errv : word).
    Hypothesis HP : Permutation ((buf, len) :: LR) LB.
    Hypothesis PN : pb_nums len off dep.
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis PAL : PB mod 8 = 0.                      (* [comment removed for export] *)
    Hypothesis SP16 : bv_unsigned sp + 16 <= PB.
    Hypothesis P80 : PB + 80 <= 2^47.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 < ASTACK_TOP sp0.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - AENSURE_STACK.
    Hypothesis TP : tp = wz ATP.
    Hypothesis ND : 0 <= needed < 2^64.
    Hypothesis LEN : Z.of_nat (length bs) = len.
    Hypothesis NPR : np + 2 <= NPMAX TI.
    Hypothesis HB : pb_allow len <= B0.
    (* [comment removed for export] *)
    Hypothesis R : ablock_range buf len.

    Notation POST := (ensure_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B0 PB buf len off dep fw bs needed lo m g).
    Notation SP1 := (bv_unsigned sp + -80).
    Notation FRAME mm := (rw_cells bsegs mm (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells bsegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                              C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)]).
    Notation SHB := (Z_to_bv 64 0x7fff8000).
    Notation SHA a := (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)).
    (* [comment removed for export] *)
    Notation LST pc mm rav x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 SP1) gp tp x5 x6 x7 x8 (Z_to_bv 64 (PB + 8)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (SHA PB) SHB (SHA (PB + 8)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

    (* [comment removed for export] *)
    Definition einv (mm : word -> option byte) (mo : Model) (gg : lghost) (LBX : list cblock) (TRSX : list (list Z)) (BX npX : Z) : Prop :=
      ART AI sp0 SPB LBX LF TRSX BX mm mo gg /\ FRAME mm /\ stk bsegs mm lo SP1 /\ mem_inv bsegs mm
      /\ (exists e, rw_cells bsegs mm AERRNO [C4 e]) /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m mm
      /\ sh_zero mm alloc_ceiling (2^47) /\ pb_below mm PB /\ gmono g gg /\ TINV TI npX TRSX.

    Lemma SP1eq : bv_unsigned (Z_to_bv 64 SP1) = SP1.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma SPtop : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.

    Lemma PBS_fold : forall mm b l, PBS mm b l -> pb_struct mm PB b l off dep fw.
    Proof. intros mm b l H. exact H. Qed.

    (* [comment removed for export] *)
    Lemma epi : forall mm mo' g' LB' TRS' B' np' e' (rav x5 x6 x7 x8 x10 x11 x12 r x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
      ART AI sp0 SPB LB' LF TRS' B' mm mo' g' -> TINV TI np' TRS' -> gmono g g' ->
      FRAME mm -> stk bsegs mm lo SP1 -> mem_inv bsegs mm -> rw_cells bsegs mm AERRNO [C4 e'] ->
      pv_agree sp0 LR LF (bv_unsigned sp) PB m mm ->
      ( (r = Z_to_bv 64 0 /\ Permutation LR LB' /\ pb_struct mm PB 0 0 off dep fw /\ B0 - PB_FAIL <= B' /\ np' <= np + 2)
        \/ (r = Z_to_bv 64 0 /\ Permutation ((buf, len) :: LR) LB' /\ pb_struct mm PB buf len off dep fw /\ pb_data mm buf len bs
            /\ B' = B0 /\ np' = np)
        \/ (exists buf' len' bs', r = Z_to_bv 64 (buf' + off) /\ Permutation ((buf', len') :: LR) LB'
              /\ pb_struct mm PB buf' len' off dep fw /\ pb_data mm buf' len' bs'
              /\ needed + off + 1 <= len' /\ len' < 2^31 /\ len <= len'
              /\ B0 - (pb_pot len' - pb_pot len) <= B' /\ np' <= np + (pb_npot len' - pb_npot len)) ) ->
      LSCPS bsegs POST (LST 0x866b0 mm rav x5 x6 x7 x8 x10 x11 x12 r x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31) mo' g'.
    Proof.
      intros until x31. intros HL' TV' GM' FR ST' MI' ERR' PVA OUT.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      eapply lscps_step_evt. cbv beta delta [mkR].
      do 12 zstep.
      release_frame FR ST' (bv_unsigned sp).
      zstep.
      apply evt_done. apply lscps_done. unfold ensure_post.
      nexists 21%nat. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact PVA|]. split; [exact HL'|]. split; [exact TV'|]. split; [exact GM'|].
      unfold wz. exact OUT.
    Qed.
    (* [comment removed for export] *)
    Lemma grow : forall (m1 : word -> option byte) (mo1 : Model) (ns : Z) (rav x5 x6 x7 x11 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      einv m1 mo1 g LB TRS B0 np -> PBS m1 buf len -> u8arr bsegs m1 buf bs ->
      needed + off + 1 <= ns -> ns <= INT_MAX -> len < needed + off + 1 -> (2 * len + 2 <= ns \/ ns = INT_MAX) ->
      LSCPS bsegs POST (LST 0x86704 m1 rav x5 x6 x7 (Z_to_bv 64 (PB + 16)) (Z_to_bv 64 PB) x11 (Z_to_bv 64 buf) x13 x14 x15 x16 x17
                            (Z_to_bv 64 ns) (SHA (PB + 16)) x23 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros (HL & FR & ST1 & MI1 & [e ERR] & PVA & SSZ1 & PBW1 & GM1 & TV1) PBS1 ARR NS1 NS2 NR HG.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      pose proof SP1eq as E1. pose proof SPtop as SPT. rewrite INT_MAX_eq in NS2, HG.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      assert (HBB : cost_realloc ns + cost_free <= B0).
      { pose proof (cost_realloc_le ns ltac:(lia)). pose proof (pb_allow_ge_fail len ltac:(rewrite INT_MAX_eq; lia)). rewrite PB_FAIL_eq, KRE_eq in *. rewrite cost_free_eq in *. lia. }
      pose proof cost_free_eq as CF.
      (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 56) SSZ1 ltac:(alia)) as Z56. asan_chk Z56. clear Z56.
      zstep. zstep. zstep. if_cases Kd; zify_cond Kd; [exfalso; unfold AREALLOC in Kd; lia|]. clear Kd.
      zstep. zstep. zstep.
      replace (ret_pc (Z_to_bv 64 AREALLOC)) with (wz AREALLOC) by (unfold wz, AREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      (* [comment removed for export] *)
      destruct (pb_head_CB _ _ _ _ _ PBS1) as [HD16 _].
      destruct (uwt_hook_frame16 m1 SP1 (ASTACK_TOP sp0) PC0_REALLOC (PB + 16) (Z_to_bv 64 buf) (Z_to_bv 64 len)) as [tl UW].
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
      replace (ret_pc (Z_to_bv 64 0x86730)) with (Z_to_bv 64 0x86730) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
        { eapply (pb_below_pv_agree sp0 LB LF (bv_unsigned sp + -80)); [eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; exact Hb]| exact PBW1| lia| lia]. }
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
        destruct (uwt_hook_frame16 m2 SP1 (ASTACK_TOP sp0) PC0_FREE PB w1 w2 BY16 Hw1 ltac:(lia)) as [tl2 UW2].
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
        replace (ret_pc (Z_to_bv 64 0x86830)) with (Z_to_bv 64 0x86830) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL2))) as HPr.
        assert (TV3 : TINV TI (np + 1 + 1) TRS3) by (eapply (tinv_put_paid_or TI); [exact TV2| lia| left; exact TP3]).
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in FR; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in PBS1; [| left; cbn; lia].
        assert (PVA3 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m3).
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_of_cj_pres; [exact PR3| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]]. }
        assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR3| exact SSZ2]).
        assert (PBW3 : pb_below m3 PB).
        { eapply (pb_below_pv_agree sp0 (cb_remove buf LB) LF (bv_unsigned sp + -80)); [eapply pv_agree_of_cj_pres; [exact PR3| lia| intros b Hb; exact Hb]| exists w1, w2; split; [exact BY16| exact Hw1]| lia| lia]. }
        clear PVA2 MI2 ST2 ERR2 HL2 SSZ2 BY16 UW2.
        (* [comment removed for export] *)
        destruct (pb_head_CB _ _ _ _ _ PBS1) as [HD TL].
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
          eapply MSX with (lo := lo) (d := PB) (c := 0) (n := 16); clear MSX; rewrite ?unsigned_lit by lia;
            first [ eapply (art_icpt_cells AI); exact HL3 | exact MI3 | exact ST3 | exact HD | reflexivity
                  | app_rng AI
                  | apply wr_range_ok_high; lia
                  | intros _; eapply sh_zero_shadow_ok; [exact SSZ3| alia| lia| lia]
                  | alia | lia ]. }
        cbv beta. intros ms4 PO4.
        (nelim PO4 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m4 -> MU4 WM4 MI4 ZB ST4).
        rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
        replace (ret_pc (Z_to_bv 64 0x86840)) with (Z_to_bv 64 0x86840) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply (rw_cells_transport bsegs) in FR; [| exact MU4| exact WM4| cbn; lia].
        eapply (rw_cells_transport bsegs) in ERR3; [| exact MU4| exact WM4| cbn; lia].
        eapply (rw_cells_transport bsegs) in TL; [| exact MU4| exact WM4| cbn; lia].
        pose proof (pb_head_zero _ _ _ ZB TL) as PBS4.
        assert (HL4 : ART AI sp0 SPB (cb_remove buf LB) LF TRS3 (B0 - cost_realloc ns - cost_free) m4 mo3 g3).
        { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]]; right; left; cbn; lia. }
        assert (PVA4 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m4).
        { eapply pv_agree_trans; [exact PVA3|]. eapply (pv_agree_of_munch2 AI); [exact HL3| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]| exact MU4| exact WM4| right; left; lia| right; right; try rewrite alloc_ceiling_eq; lia| lia| lia]. }
        clear MU4 WM4.
        zstep. zstep. apply evt_done. cbv beta.
        eapply epi; [exact HL4| exact TV3| eapply gmono_trans; [exact GM2'| exact GM3]| exact FR| exact ST4| exact MI4| exact ERR3| exact PVA4|].
        left. split; [reflexivity|]. split; [exact HPr|]. split; [exact (PBS_fold _ _ _ PBS4)|]. split; [| lia].
        rewrite PB_FAIL_eq, cost_free_eq. pose proof (cost_realloc_le ns ltac:(lia)). rewrite KRE_eq in *. lia.
      - (* [comment removed for export] *)
        rewrite ?E1 in PR2. unfold wz.
        (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
        pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PBS1; [| left; cbn; lia].
        assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]]. }
        assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR2| exact SSZ1]).
        assert (PBW2 : pb_below m2 PB).
        { eapply (pb_below_pv_agree sp0 (cb_remove buf LB) LF (bv_unsigned sp + -80)); [eapply pv_agree_of_cj_pres; [exact PR2| lia| intros b Hb; exact Hb]| exact PBW1| lia| lia]. }
        clear PVA PR2 MI1 ST1 ERR HL ARR SSZ1 PBW1 HD16 UW.
        rewrite (Z.min_l len ns) in BLK by lia.
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        pose proof (stack_shb0 m2 (PB + 8) SSZ2 ltac:(alia)) as Z8. asan_chk Z8. clear Z8.
        zstep. zstep.
        pose proof (stack_shb0 m2 PB SSZ2 ltac:(alia)) as Z0. asan_chk Z0. clear Z0.
        zstep.
        pose proof (stack_shb0 m2 (PB + 16) SSZ2 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. rewrite (zb_lxor_ones Bn) by lia. ugd.
        zstep. zstep.
        apply evt_done. cbv beta.
        lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mc _) _ _ => rename mc into m3 end.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 L1 L2).
        eapply epi; [ | exact TV2 | exact GM2' | exact FR | exact ST2 | exact MI2 | exact ERR2 | | right; right].
        + eapply (art_frame_store AI); [exact HL2| exact MU| exact WM| alia| lia].
        + eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia].
        + exists Bn, ns, (firstn (Z.to_nat len) bs ++ junk). split; [reflexivity|]. split.
          { eapply Permutation_trans; [| apply Permutation_refl]. apply perm_skip. exact HPr. }
          split; [exact (PBS_fold _ _ _ PBS1)|]. split.
          { split; [exact ARR2| rewrite length_app, L1, L2; lia]. }
          split; [lia|]. split; [lia|]. split; [lia|]. split.
          { pose proof (pb_pot_grow len ns ltac:(lia) ltac:(rewrite INT_MAX_eq; lia) ltac:(rewrite INT_MAX_eq; exact HG)). lia. }
          pose proof (pb_npot_grow len ns ltac:(lia) ltac:(rewrite INT_MAX_eq; lia) ltac:(rewrite INT_MAX_eq; exact HG)). lia.
    Qed.
    (* [comment removed for export] *)
    Lemma ret0 : forall m1 mo1 rav y5 y6 y7 y8 y10 y11 y12 y14 y15 y16 y17 y18 y22 y23 y28 y29 y30 y31,
      einv m1 mo1 g LB TRS B0 np -> PBS m1 buf len -> u8arr bsegs m1 buf bs ->
      LSCPS bsegs POST (LST 0x866b0 m1 rav y5 y6 y7 y8 y10 y11 y12 (Z_to_bv 64 0) y14 y15 y16 y17 y18 y22 y23 y28 y29 y30 y31) mo1 g.
    Proof.
      intros until y31. intros (HL & FR & ST1 & MI1 & [e ERR] & PVA & SSZ1 & PBW1 & GM1 & TV1) PBS1 ARR.
      eapply epi; [exact HL| exact TV1| exact GM1| exact FR| exact ST1| exact MI1| exact ERR| exact PVA|].
      right; left. split; [reflexivity|]. split; [exact HP|]. split; [exact (PBS_fold _ _ _ PBS1)|]. split; [split; [exact ARR| exact LEN]|]. split; reflexivity.
    Qed.

    Lemma ret94 : forall m1 mo1 rav y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y28 y29 y30 y31,
      einv m1 mo1 g LB TRS B0 np -> PBS m1 buf len -> u8arr bsegs m1 buf bs ->
      LSCPS bsegs POST (LST 0x8669c m1 rav y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y28 y29 y30 y31) mo1 g.
    Proof.
      intros until y31. intros EI PBS1 ARR.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta. eapply ret0; [exact EI| exact PBS1| exact ARR].
    Qed.

    (* [comment removed for export] *)
    Lemma tail58 : forall (m1 : word -> option byte) (mo1 : Model) (rav x5 x6 x7 x13 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
      einv m1 mo1 g LB TRS B0 np -> PBS m1 buf len -> u8arr bsegs m1 buf bs ->
      needed < 2^31 -> (len = 0 \/ off < len) ->
      LSCPS bsegs POST (LST 0x86660 m1 rav x5 x6 x7 (Z_to_bv 64 (PB + 16)) (Z_to_bv 64 PB) (Z_to_bv 64 needed) (Z_to_bv 64 buf) x13 (Z_to_bv 64 len) x15 x16 x17
                            x18 x22 x23 x28 x29 x30 x31) mo1 g.
    Proof.
      intros until x31. intros EI PBS1 ARR N31 OFL. (nelimp EI 10%nat; intros HL FR ST1 MI1 [e ERR] PVA SSZ1 PBW1 GM1 TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      pose proof SP1eq as E1. pose proof SPtop as SPT. pose proof INT_MAX_eq as IM.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 16) SSZ1 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep. zstep. zstep. if_cases Kroom; zify_cond Kroom.
      - (* [comment removed for export] *)
        zstep. rewrite (zb_lxor_ones buf) by lia. ugd.
        zstep. apply evt_done. cbv beta.
        eapply epi; [exact HL| exact TV1| exact GM1| exact FR| exact ST1| exact MI1| exact ERR| exact PVA|].
        right; right. exists buf, len, bs. split; [reflexivity|]. split; [exact HP|]. split; [exact (PBS_fold _ _ _ PBS1)|].
        split; [split; [exact ARR| exact LEN]|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [lia|]. lia.
      - (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (stack_shchk m1 (PB + 32) 4 SSZ1 ltac:(alia)) as CK32. asan_chk CK32.
        zstep. zstep. if_cases Kna; zify_cond Kna; [| exfalso; apply Kna; reflexivity]. clear Kna.
        zstep. zstep. if_cases K30; zify_cond K30.
        + (* [comment removed for export] *)
          zstep. apply evt_done. cbv beta.
          rewrite Z.shiftr_div_pow2 in K30 by lia.
          eapply grow; [exact EI| exact PBS1| exact ARR| rewrite Z.shiftl_mul_pow2 by lia; lia| rewrite Z.shiftl_mul_pow2 by lia; lia| lia| left; rewrite Z.shiftl_mul_pow2 by lia; lia].
        + zstep. zstep. if_cases K31; zify_cond K31.
          * (* [comment removed for export] *)
            apply evt_done. cbv beta. eapply ret94; [exact EI| exact PBS1| exact ARR].
          * zstep. zstep. zstep. apply evt_done. cbv beta.
            rewrite Z.shiftr_div_pow2 in K30, K31 by lia.
            eapply grow; [exact EI| exact PBS1| exact ARR| lia| lia| lia| right; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma body : forall (m1 : word -> option byte) (mo1 : Model) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      einv m1 mo1 g LB TRS B0 np -> PBS m1 buf len -> u8arr bsegs m1 buf bs ->
      LSCPS bsegs POST
        (MS (mkR ra (Z_to_bv 64 SP1) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PB) (Z_to_bv 64 needed) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x865f0) fc None m1 (seg_rom bsegs)) mo1 g.
    Proof.
      intros until x31. intros EI PBS1 ARR. (nelimp EI 10%nat; intros HL FR ST1 MI1 [e ERR] PVA SSZ1 PBW1 GM1 TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      pose proof SP1eq as E1. pose proof SPtop as SPT.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. shbase_split SB.
      eapply lscps_step_evt. cbv beta delta [mkR].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. zstep.
      pose proof (stack_shb0 m1 PB SSZ1 ltac:(alia)) as Z0. asan_chk Z0. clear Z0.
      zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (stack_shb0 m1 (PB + 8) SSZ1 ltac:(alia)) as Z8. asan_chk Z8. clear Z8.
      zstep. zstep. zstep. if_cases Klen; zify_cond Klen.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases Kn; zify_cond Kn.
        + (* [comment removed for export] *) apply evt_done. cbv beta. eapply ret94; [exact EI| exact PBS1| exact ARR].
        + apply evt_done. cbv beta. rewrite Z.shiftr_div_pow2 in Kn by lia.
          eapply tail58; [exact EI| exact PBS1| exact ARR| lia| left; exact Klen].
      - (* [comment removed for export] *)
        zstep. zstep.
        pose proof (stack_shb0 m1 (PB + 16) SSZ1 ltac:(alia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. if_cases Kn; zify_cond Kn.
        + apply evt_done. cbv beta. eapply ret0; [exact EI| exact PBS1| exact ARR].
        + zstep. zstep. if_cases Koff; zify_cond Koff.
          * apply evt_done. cbv beta. rewrite Z.shiftr_div_pow2 in Kn by lia.
            eapply tail58; [exact EI| exact PBS1| exact ARR| lia| right; exact Koff].
          * zstep. apply evt_done. cbv beta. eapply ret0; [exact EI| exact PBS1| exact ARR].
    Qed.

    (* [comment removed for export] *)
    Lemma entry : forall (mo : Model) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g -> TINV TI np TRS ->
      PBS m buf len -> u8arr bsegs m buf bs -> pb_below m PB -> sh_zero m alloc_ceiling (2^47) ->
      stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m AERRNO [C4 errv] -> mem_inv bsegs m ->
      LSCPS bsegs POST
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PB) (Z_to_bv 64 needed) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x865bc) fc None m (seg_rom bsegs)) mo g.
    Proof.
      intros until x31. intros HL TV PBS0 ARR PBW SSZ ST ERR MI.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AENSURE_STACK, AMALLOC_STACK in LO'.
      pose proof SP1eq as E1. pose proof SPtop as SPT.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). unfold AERRNO, ATP in ERR.
      pose proof (conj ERR I) as ERRbox. clear ERR. pose proof (conj PBS0 I) as PBSbox. clear PBS0.
      destruct ARR as [ABY AWR]. (nelim PBW 4%nat; intros w1 w2 BY16 Hw1).
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 80%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 11 zstep.
      (* [comment removed for export] *)
      zstep. replace (Z.land PB 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia). ugd.
      apply evt_done. cbv beta.
      lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mc _) _ _ => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB LF TRS B0 m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]).
      eapply body.
      - split; [exact HL1|]. split; [exact FR|]. split; [exact ST|]. split; [assumption|]. split.
        { exists errv. eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
        split. { eapply (pv_agree_stack AI); [exact HL| intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]| exact MU| exact WM| alia| lia| lia| lia]. }
        split. { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [cbn; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
        split. { exists w1, w2. split; [| exact Hw1]. first [exact BY16 | eapply (bytes_at_transport bsegs); [exact BY16| exact MU| rewrite length_app, !length_le8; cbn; lia]]. }
        split; [apply gmono_refl| exact TV].
      - eapply (rw_cells_transport bsegs); [exact (proj1 PBSbox)| exact MU| exact WM| cbn; lia].
      - split; [| first [exact AWR | eapply wr_at_transport; [exact AWR| exact WM]]]. first [exact ABY | eapply (bytes_at_transport bsegs); [exact ABY| exact MU| cbn; lia]].
    Qed.
  End Call.

  Theorem ensure_spec : ensure_stmt AI TI.
  Proof.
    unfold ensure_stmt. intros until errv.
    intros HL HP PS PD PN PL PAL PBW SP16 P80 SP0 TOP BOT SPAL ST CEIL LO ERR MI TP SSZ TV NPR HB A0 A1 ND.
    unfold AENSURE_ENTRY, wz in A0, A1. subst a0 a1. unfold wz, AENSURE_ENTRY.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as R.
    destruct PD as [ARR LEN].
    eapply entry; try eassumption.
  Qed.
End S.

(* [comment removed for export] *)
Theorem ensure_ok : forall AI TI, ensure_stmt AI TI.
Proof. intros AI TI. exact (ensure_spec AI TI ICPT_mem.asan_memset_ok). Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia.
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
