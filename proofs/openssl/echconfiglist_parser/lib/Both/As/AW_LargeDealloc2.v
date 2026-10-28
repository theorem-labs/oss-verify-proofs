(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_LargeAlloc1 AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition fl_pb (a : Z) : Z := sh a + 4095 - (sh a + 4095) mod 2 ^ 12.
Definition fl_pe (a msz : Z) : Z := sh (a + msz) - sh (a + msz) mod 2 ^ 12.

Lemma fl_pbe : forall a msz, 0 <= a -> a mod 4096 = 0 -> 0x10000 <= msz ->
  sh a <= fl_pb a < sh a + 4096 /\ sh a + msz / 8 - 4096 < fl_pe a msz <= sh a + msz / 8 /\ fl_pb a + 4096 <= fl_pe a msz
  /\ fl_pb a mod 4096 = 0 /\ fl_pe a msz mod 4096 = 0.
Proof.
  intros a msz A0 AL MS. unfold fl_pb, fl_pe, sh, ASHADOW_BASE. change (2 ^ 12) with 4096.
  assert (E : (a + msz) / 8 = a / 8 + msz / 8) by (Z.div_mod_to_equations; lia). rewrite E.
  Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition dealloc2a_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo a msz : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x1998e0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a)
                  (wz (fl_pb a)) (wz (fl_pe a msz - fl_pb a)) (wz 4) (wz 4) a4 a5 a6 (wz 233)
                  (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1948) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -32).

(* [comment removed for export] *)
Definition dealloc2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo a msz TH : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (j16 : list byte) m',
    ms' = MS (mkR (wz 0x1d3194) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz msz) (wz 0) (wz a) (wz msz) a2 a3 a4 a5 a6 (wz 215)
                  (wz a) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1910) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (TH + 2888, TH + 2904)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW.

Section Dealloc2.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (lo a msz TSD CTX TH : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -32).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 80 <= bv_unsigned sp.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ 0x10000 <= msz.   (* [comment removed for export] *)
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).

  (* [comment removed for export] *)
  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Ltac dealloc2_finish :=
    (* [comment removed for export] *)
    step; callN getcurthreadstats_spec; rewrite ?unsigned_lit by lia; try eassumption; try lia;
    try (unfold ATSDINIT; eassumption); try (acb; lia); try (unfold AIMG_TOP; lia);
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      let TS1 := fresh "TS1" in let TS2 := fresh "TS2" in let TS3 := fresh "TS3" in let TS4 := fresh "TS4" in let sj := fresh "sj" in let SJ := fresh "SJ" in
      destruct (stk_split asegs _ (TH + 2800) (TH + 2888) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H;
      destruct (stk_split asegs _ (TH + 2888) (TH + 2904) (TH + 3168) TS2 ltac:(hci; lia)) as [TS3 TS4]; clear TS2;
      destruct (stk_cells _ _ _ TS3 ltac:(hci; lia)) as [sj SJ]; replace (TH + 2904 - (TH + 2888)) with 16 in SJ by lia; change (Z.to_nat 16) with 16%nat in SJ;
      apply (rw_cells_split_CB asegs _ _ [] 16 sj [] [8;8]%nat) in SJ; [| reflexivity]; cbn [mk_CB_cells app] in SJ;
      repeat match type of SJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in SJ end;
      repeat match type of SJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in SJ end;
      repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end
    end;
    unfold wz;
    step; step; step; step; step; step; st1; st1;
    (* [comment removed for export] *)
    step; step; step; step; step; step; step;
    lazymatch goal with H : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FR H (bv_unsigned sp) end;
    step;
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ lo (bv_unsigned sp) |- _ =>
      step; carve_frame 48%nat H;
      lazymatch goal with FRu : rw_cells _ _ (bv_unsigned sp + -48) [CB 48 _] |- _ =>
        let J := fresh "J" in
        lazymatch type of FRu with rw_cells _ _ _ [CB 48 ?j] => remember j as J in FRu end;
        apply (rw_cells_split_CB asegs _ _ [] 48 J [] [16;8;8;8;8]%nat) in FRu; [| reflexivity]; cbn [mk_CB_cells app] in FRu;
        repeat match type of FRu with context [CB ?k (take ?i ?l)] => let X := fresh "jk" in remember (take i l) as X in FRu end;
        repeat match type of FRu with context [CB ?k (drop ?i ?l)] => let X := fresh "jk" in remember (drop i l) as X in FRu end;
        repeat match goal with H' : _ = take _ _ |- _ => clear H' | H' : _ = drop _ _ |- _ => clear H' | H' : _ = J |- _ => clear H' end
      end
    end;
    st1; st1; st1; st1;
    (let K := fresh "K" in step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K);
    step;
    (let K := fresh "K" in step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K);
    step; step; step; step; step;
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TST' : stk asegs mm (TH + 2800) (TH + 3168))
        by (apply (stk_merge asegs _ _ (TH + 2888)); [assumption| |lia]; apply (stk_merge asegs _ _ (TH + 2904)); [assumption|assumption|lia])
    end;
    apply evt_done; unfold dealloc2_post; do 12 eexists; eexists; eexists; split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.

  (* [comment removed for export] *)
  Theorem dealloc2b :
    evt asegs (dealloc2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz TH)
      (MS (mkR (wz 0x1998e0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a) a0 a1 a2 a3 a4 a5 a6 a7 (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d194c) fc None m (seg_rom asegs)).
  Proof.
    pose proof ENV as ENV0. pose proof ENV as ENV1. open_senv ENV1. clear Ecan Ethresh Emlim Edpm Erms Ename Eshb Ehme.   (* [comment removed for export] *)
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof AR as R; destruct R as (AHI & CE & AL & MSZ).
    unfold AHI_LO, AIMG_TOP in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (TH + 2888, TH + 2904)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. step.
    dealloc2_finish.
  Qed.

  (* [comment removed for export] *)
  Lemma dealloc2a_k : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 : word) (m1 : mem),
    SENV tp TSD CTX TH m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64) [C8 (wz msz); C8 (wz a); C8 (wz a); C8 (wz 0x1998e0)] ->
    evt asegs (dealloc2a_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo a msz)
      (MS (mkR (wz 0x1beea8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz msz) (wz a) (wz (sh (a + msz))) x11 x12 x13 x14 x15 x16 x17
               (wz (sh a)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x27 x28 x29 x30)
          F (Z_to_bv 64 0x1beea8) fc None m1 (seg_rom asegs)).
  Proof.
    intros until m1. clear MI ST FR HDR TST ENV. intros ENV1 MI ST FR0.
    pose proof ENV1 as ENV0. open_senv ENV1. clear Ecan Ethresh Emlim Edpm Erms Ename.   (* [comment removed for export] *)
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof AR as R; destruct R as (AHI & CE & AL & MSZ).
    unfold AHI_LO, AIMG_TOP in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (SHR : 2148314624 <= sh a /\ sh (a + msz) <= 17594333495296 /\ sh a + 8192 <= sh (a + msz)) by (clear - AHI CE AL MSZ; try acb; aunf; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 32)]%Z m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    release_frame FR0 ST (bv_unsigned sp + -32).
    step.
    (* [comment removed for export] *)
    step. carve_frame 32%nat ST. spill_frame ltac:(do 4 st1). step. step. step. step. step.
    step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step.
    rewrite (unsigned_lit (sh a + 4095)), (unsigned_lit (sh (a + msz))) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite !StrFun.land_align_down by lia.
    fold (fl_pb a). fold (fl_pe a msz).
    assert (RBE : sh a <= fl_pb a <= sh a + 4095 /\ sh (a + msz) - 4095 <= fl_pe a msz <= sh (a + msz) /\ fl_pb a + 4096 <= fl_pe a msz)
      by (unfold fl_pb, fl_pe; clear - SHR; try acb; Z.div_mod_to_equations; lia).
    remember (fl_pb a) as rb eqn:ERB. remember (fl_pe a msz) as re eqn:ERE.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    { exfalso. clear - K RBE. lia. }
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame H ST (bv_unsigned sp + -32) end. step.
    (* [comment removed for export] *)
    step. step. step. if_cases K2. { exfalso. revert K2. vm_compute. discriminate. } clear K2 K.
    step.
    step. if_cases K3. 2:{ exfalso. revert K3. vm_compute. discriminate. } clear K3.
    step.
    rewrite (unsigned_lit re), (unsigned_lit rb) by (clear - RBE SHR; lia).
    apply evt_done. unfold dealloc2a_post, wz. rewrite <- ERB, <- ERE. do 10 eexists; eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
  Qed.

  Lemma dealloc2a_post_at : forall m1, munch [(bv_unsigned sp - 64, bv_unsigned sp - 32)]%Z m m1 -> wmono asegs m m1 ->
    forall ms, dealloc2a_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo a msz ms ->
    dealloc2a_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz ms.
  Proof.
    clear. intros m1 MU WM ms P. unfold dealloc2a_post in P |- *.
    destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & m' & E' & MU' & WM' & REST).
    exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, m'. split; [exact E'|].
    split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans _ _ _ _ WM WM')|]. exact REST.
  Qed.

  (* [comment removed for export] *)
  Theorem dealloc2a :
    evt asegs (dealloc2a_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz)
      (MS (mkR (wz 0x1998d4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a) a0 a1 a2 a3 a4 a5 a6 a7 (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1998d4) fc None m (seg_rom asegs)).
  Proof.
    pose proof ENV as ENV0. open_senv ENV. clear Ecan Ethresh Emlim Edpm Erms Ename.   (* [comment removed for export] *)
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof AR as R; destruct R as (AHI & CE & AL & MSZ).
    unfold AHI_LO, AIMG_TOP in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (SHR : 2148314624 <= sh a /\ sh (a + msz) <= 17594333495296 /\ sh a + 8192 <= sh (a + msz)) by (clear - AHI CE AL MSZ; try acb; aunf; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 32%nat ST. spill_frame ltac:(do 4 st1). step. step. step.
    (* [comment removed for export] *)
    Ltac mem_to_shadow_hi :=
      step; step; step; step; step;
      replace (v_sltu (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
      step; step;
      let K := fresh "K" in
      step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K;
      (* [comment removed for export] *)
      step; step; step; step; step; step; step;
      step; if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615; intros K; lia]; clear K;
      (* [comment removed for export] *)
      step; step; step; step; step;
      step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K;
      step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K;
      (* [comment removed for export] *)
      step; step; step.
    Ltac mem_to_shadow_lo :=
      step; step; step; step; step;
      replace (v_sltu (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
      step; step;
      let K := fresh "K" in
      step; if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]; clear K;
      (* [comment removed for export] *)
      step; step; step.
    senv_img_at ENV0 MU WM ENV1.
    destruct AHI as [ALO|AHI'].
    - (* [comment removed for export] *)
      pose proof ALO as ALO2. unfold aapp_lo, AIMG_TOP, ALOWSH_LO in ALO2.
      mem_to_shadow_lo.
      rewrite (unsigned_lit a), Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (2147450880 + a / 8) with (sh a) by reflexivity.
      (* [comment removed for export] *)
      step. step. replace (msz + a) with (a + msz) by lia. step.
      mem_to_shadow_lo.
      rewrite (unsigned_lit (a + msz)), Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (2147450880 + (a + msz) / 8) with (sh (a + msz)) by reflexivity.
      eapply evt_mono; [eapply dealloc2a_k; eassumption| exact (dealloc2a_post_at _ MU WM)].
    - (* [comment removed for export] *)
      pose proof AHI' as AHI2. unfold aapp_hi, AHI_LO in AHI2.
      mem_to_shadow_hi.
      rewrite (unsigned_lit a), Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (2147450880 + a / 8) with (sh a) by reflexivity.
      (* [comment removed for export] *)
      step. step. replace (msz + a) with (a + msz) by lia. step.
      mem_to_shadow_hi.
      rewrite (unsigned_lit (a + msz)), Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (2147450880 + (a + msz) / 8) with (sh (a + msz)) by reflexivity.
      eapply evt_mono; [eapply dealloc2a_k; eassumption| exact (dealloc2a_post_at _ MU WM)].
  Qed.


End Dealloc2.

