(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_artF RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_spz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_sec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gbb_step (p acc h : Z) : Z := if (h <=? p) && (p - h <? p - acc) then h else acc.
Fixpoint gbb_scan (l : list (Z * Z)) (p acc : Z) : Z :=
  match l with [] => acc | e :: l' => gbb_scan l' p (gbb_step p acc (fst e)) end.

Section ScanValue.
  Variable l0 : list (Z * Z).          (* [comment removed for export] *)
  Variables mb n p : Z.
  Hypothesis HIN : In (mb, n) l0.
  Hypothesis ND : List.NoDup (map fst l0).
  Hypothesis HP : mb <= p < mb + smapsize n.
  Hypothesis DISJ : forall h nh, In (h, nh) l0 -> h = mb \/ h + smapsize nh <= mb \/ mb + smapsize n <= h.
  Hypothesis POS : forall h nh, In (h, nh) l0 -> 0 <= h /\ 0 < smapsize nh.

  Lemma other_below : forall h nh, In (h, nh) l0 -> h <> mb -> h <= p -> h < mb.
  Proof. intros h nh Hi Hne Hle. destruct (DISJ h nh Hi) as [E|[D|D]]; [congruence| | lia]. pose proof (POS h nh Hi). lia. Qed.

  Lemma scan_after : forall l acc, incl l l0 -> ~ In mb (map fst l) -> acc = mb -> gbb_scan l p acc = mb.
  Proof.
    induction l as [|[h nh] l IH]; intros acc Hincl Hni ->; [reflexivity|]. cbn.
    apply IH; [intros e He; apply Hincl; right; exact He| intros Hc; apply Hni; right; exact Hc|].
    unfold gbb_step. cbn [fst]. destruct (Z.leb_spec h p); [| reflexivity]. cbn [andb].
    assert (h <> mb) by (intros ->; apply Hni; left; reflexivity).
    pose proof (other_below h nh (Hincl _ ltac:(left; reflexivity)) ltac:(assumption) ltac:(assumption)).
    destruct (Z.ltb_spec (p - h) (p - mb)); [lia| reflexivity].
  Qed.

  Lemma scan_before : forall l acc, incl l l0 -> List.NoDup (map fst l) -> In (mb, n) l ->
    (acc = 0 \/ acc < mb) -> 0 <= acc -> gbb_scan l p acc = mb.
  Proof.
    induction l as [|[h nh] l IH]; intros acc Hincl Hnd Hin Hacc Hacc0; [destruct Hin|]. cbn.
    cbn in Hnd. inversion Hnd as [|x l' Hni Hnd']; subst.
    destruct Hin as [E|Hin].
    - injection E as -> ->. apply scan_after; [intros e He; apply Hincl; right; exact He| exact Hni|].
      unfold gbb_step. cbn [fst]. pose proof (POS mb n HIN).
      destruct (Z.leb_spec mb p); [| lia]. cbn [andb]. destruct (Z.ltb_spec (p - mb) (p - acc)); [reflexivity| destruct Hacc; lia].
    - assert (h <> mb) by (intros ->; apply Hni; apply in_map_iff; exists (mb, n); split; [reflexivity| exact Hin]).
      apply IH; [intros e He; apply Hincl; right; exact He| exact Hnd'| exact Hin| |];
      unfold gbb_step; cbn [fst]; pose proof (POS h nh (Hincl _ ltac:(left; reflexivity)));
      destruct (Z.leb_spec h p); cbn [andb]; try lia;
      destruct (Z.ltb_spec (p - h) (p - acc)); try lia.
      right. apply (other_below h nh); [apply Hincl; left; reflexivity| assumption| assumption].
  Qed.

  Lemma scan_value : gbb_scan l0 p 0 = mb.
  Proof. apply scan_before; [intros e He; exact He| exact ND| exact HIN| left; reflexivity| lia]. Qed.
End ScanValue.

Lemma skipn_nthz : forall {A} (l : list A) i d, 0 <= i < zlen l ->
  skipn (Z.to_nat i) l = nthz l i d :: skipn (Z.to_nat (i + 1)) l.
Proof.
  intros A l i d Hi. unfold nthz, zlen in *. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (HL : (Z.to_nat i < length l)%nat) by lia. revert HL. generalize (Z.to_nat i) as k. clear Hi.
  induction l as [|x l IH]; intros k HL; cbn in HL; [lia|]. destruct k as [|k]; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0e s1 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (st : rtstate) (mb n p lo : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HIN : In (mb, n) (st_sec st).
  Hypothesis HP : sec_alloc_beg mb <= p < mb + smapsize n.
  Hypothesis CEIL0 : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AGBB_STACK.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (gbb_post ra sp gp tp s0e s1 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb lo m).


  (* [comment removed for export] *)
  Lemma gbb_loop : forall (POSTL : machine_state -> Prop) m1 (cnt : nat) i acc x5 x6 x7 x15 x16 x17 x28 x29 x30 x31,
    Z.of_nat cnt = nsec st - i -> 0 <= i < nsec st -> 0 <= acc <= p ->
    mem_inv bsegs m1 ->
    (forall j, 0 <= j < nsec st -> rw_cells bsegs m1 (st_pa st + 8 * j) [W8 (fst (nthz (st_sec st) j (0,0)))]) ->
    (forall acc' x5 x15 x16 x17, acc' = gbb_scan (skipn (Z.to_nat i) (st_sec st)) p acc ->
       evt bsegs POSTL (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz 0xa6600) s1 (wz 0xa6398) (wz p)
                             (wz (st_pa st + 8 * nsec st)) (wz acc') (wz (st_pa st + 8 * nsec st)) x15 x16 x17 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (wz 0x34494) fc None m1 (seg_rom bsegs))) ->
    evt bsegs POSTL (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz 0xa6600) s1 (wz 0xa6398) (wz p)
                          (wz (st_pa st + 8 * i)) (wz acc) (wz (st_pa st + 8 * nsec st)) x15 x16 x17 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (wz 0x34468) fc None m1 (seg_rom bsegs)).
  Proof.
    induction cnt as [|cnt IH]; intros i acc x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Hcnt Hi Hacc MI PTR K; [lia|].
    pose proof (pa_range st WF) as PR. pose proof (sec_entry_range st WF mb n HIN) as ER. olin PR. olin ER.
    cbv beta delta [wz] in *. leaf_prep.
    pose proof (PTR i ltac:(lia)) as CI.
    set (h := fst (nthz (st_sec st) i (0, 0))) in *.
    assert (HRG : AIMG_HI <= h /\ h < CEIL).   (* [comment removed for export] *)
    { pose proof (sec_entry_range st WF h (snd (nthz (st_sec st) i (0, 0)))) as R.
      assert (In (h, snd (nthz (st_sec st) i (0, 0))) (st_sec st)).
      { subst h. rewrite <- surjective_pairing. unfold nthz. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        apply nth_In. unfold nsec, zlen in Hi. lia. }
      specialize (R ltac:(assumption)). destruct R as (R1 & R2 & _ & R4 & _). pose proof (ablk_img _ _ R1). unfold CEIL in *. lia. }
    unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    (* [comment removed for export] *)
    assert (CONT : forall x5 x16 x17,
      evt bsegs POSTL (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 0xa6600) s1 (Z_to_bv 64 0xa6398) (Z_to_bv 64 p)
                            (Z_to_bv 64 (st_pa st + 8 * i)) (Z_to_bv 64 (gbb_step p acc h)) (Z_to_bv 64 (st_pa st + 8 * nsec st)) (Z_to_bv 64 h) x16 x17
                            s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x34460) fc None m1 (seg_rom bsegs))).
    { intros y5 y16 y17.
      assert (HS : 0 <= gbb_step p acc h <= p) by (unfold gbb_step; destruct (Z.leb_spec h p); destruct (Z.ltb_spec (p - h) (p - acc)); cbn; lia).
      lstep. (* [comment removed for export] *)
      lstep. if_cases KE; zify_cond KE.
      - (* [comment removed for export] *)
        replace (Z_to_bv 64 (st_pa st + 8 * i + 8)) with (Z_to_bv 64 (st_pa st + 8 * nsec st) : word) by (f_equal; lia).
        apply K. rewrite (skipn_nthz _ i (0,0)) by (unfold nsec in *; lia). cbn [gbb_scan].
        replace (Z.to_nat (i + 1)) with (length (st_sec st)) by (unfold nsec, zlen in *; lia). rewrite skipn_all. reflexivity.
      - replace (Z_to_bv 64 (st_pa st + 8 * i + 8)) with (Z_to_bv 64 (st_pa st + 8 * (i + 1)) : word) by (f_equal; lia).
        apply (IH (i + 1) (gbb_step p acc h)); [lia| lia| exact HS| exact MI| exact PTR|].
        intros acc' z5 z15 z16 z17 ->. apply K.
        rewrite (skipn_nthz _ i (0,0)) by (unfold nsec in *; lia). reflexivity. }
    assert (WRAP : p < h -> (p - h) mod 18446744073709551616 = p - h + 18446744073709551616) by (intros; Z.div_mod_to_equations; lia).
    assert (NOWRAP : h <= p -> (p - h) mod 18446744073709551616 = p - h) by (intros; apply Z.mod_small; lia).
    set (q := st_pa st + 8 * i) in *.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      lstep. if_cases K2; zify_cond K2.
      + exfalso. rewrite WRAP in K1 by lia. lia.
      + rewrite NOWRAP in K1 by lia. lstep. lstep. (* [comment removed for export] *)
        replace (gbb_step p acc h) with h in CONT.
        2:{ unfold gbb_step. destruct (Z.leb_spec h p); [| lia]. destruct (Z.ltb_spec (p - h) (p - acc)); [reflexivity| lia]. }
        apply CONT.
    - lstep. lstep. if_cases K2; zify_cond K2.
      + replace (gbb_step p acc h) with acc in CONT.
        2:{ unfold gbb_step. destruct (Z.leb_spec h p); [lia| reflexivity]. }
        apply CONT.
      + rewrite NOWRAP in K1 by lia. lstep. lstep. lstep.
        replace (gbb_step p acc h) with acc in CONT.
        2:{ unfold gbb_step. destruct (Z.leb_spec h p); [| lia]. destruct (Z.ltb_spec (p - h) (p - acc)); [lia| reflexivity]. }
        apply CONT.
  Qed.

  Lemma gbb_walk : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1 (wz A_SECONDARY) (wz p) a2 a3 a4 a5 a6 a7 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AGET_BLOCK_BEGIN) fc None m (seg_rom bsegs)).
  Proof.
    intros until t6. intros ST MI.
    pose proof (sec_obj_cells st m HR) as (j1 & j2 & j3 & SECC & MUT).
    pose proof (mutex_cells_of m _ _ MUT) as (k & j4 & b1 & b2 & b3 & HK & E0 & E1 & MW & MJ). clear MUT.
    pose proof (pa_range st WF) as PR. pose proof (sec_entry_range st WF mb n HIN) as ER. olin PR. olin ER.
    unfold PTRARR_RES_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in PR, ER.
    unfold AGBB_STACK in LO. rewrite A_SECONDARY_val in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (0xa6398 + 616, 0xa6398 + 620)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold AGET_BLOCK_BEGIN. cbv beta delta [wz] in *. leaf_prep.
    replace (0xa6398 + 616) with 0xa6600 in * by reflexivity. replace (0xa6398 + 4) with 0xa639c in MJ by reflexivity.
    carve_frame 32%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    pose proof (sx32_256k_facts k HK) as VF. cbv zeta in VF.
    remember (sx32 (Z_to_bv 64 (256 * k))) as a5v eqn:Ea5. destruct VF as (VR & VM & V32 & _).
    pose proof (lock_word_val (bv_unsigned a5v) ltac:(lia) VM) as [LW1 LW2].
    lstep. lstep. lstep. lstep. rewrite LW1. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. rewrite LW2. lstep; try if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (NPOS : 1 <= nsec st).
    { unfold nsec, zlen. destruct (st_sec st) as [|e l] eqn:E; [destruct HIN| cbn; lia]. }
    lstep. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (PTR1 : forall j, 0 <= j < nsec st -> rw_cells bsegs m1 (st_pa st + 8 * j) [W8 (fst (nthz (st_sec st) j (0,0)))]).
    { intros j Hj. eapply (rw_cells_transport bsegs _ m m1); [exact (ptr_cells st m HR j Hj)| exact MU| exact WM| cbn; lia]. }
    cbv beta delta [wz] in PTR1.
    replace (Z_to_bv 64 (st_pa st + Z.shiftl (nsec st) 3)) with (Z_to_bv 64 (st_pa st + 8 * nsec st) : word)
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 (st_pa st)) with (Z_to_bv 64 (st_pa st + 8 * 0) : word) by (f_equal; lia).
    eapply (gbb_loop _ m1 (Z.to_nat (nsec st)) 0 0); [lia| lia| unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *; lia| exact MI| exact PTR1|].
    cbv beta delta [wz]. intros acc' y5 y15 y16 y17 ->. change (skipn (Z.to_nat 0) (st_sec st)) with (st_sec st).
    pose proof (ws_nodup st (wf_sec_ok st WF)) as ND.
    rewrite (scan_value (st_sec st) mb n p HIN ND); [| unfold sec_alloc_beg, SEC_HDR in HP; lia| intros h nh Hh; exact (sec_disj st WF mb n h nh HIN Hh)
      | intros h nh Hh; pose proof (sec_entry_range st WF h nh Hh) as (Q1 & _ & _ & Q4 & _); pose proof (ablk_img _ _ Q1); unfold AIMG_HI in *; split; lia].
    (* [comment removed for export] *)
    pose proof (secmap_cells st m HR WF mb n HIN) as (_ & _ & HDR).
    eapply (rw_cells_transport bsegs _ m m1) in HDR; [| exact MU| exact WM| cbn; pose proof (smapsize_pos n ltac:(lia)); unfold CEIL in *; lia]. cbv beta delta [wz] in HDR.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep; try if_lia. (* [comment removed for export] *)
    unfold sec_alloc_beg, SEC_HDR in HP.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    change 4095 with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (mb mod 4096) with 0 by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (E1' : le4 (Z_to_bv 64 (bv_unsigned a5v + 1)) = [zb 1; b1; b2; b3]).
    { rewrite <- E1. apply le4_mod32; [lia| lia|]. rewrite <- V32. Z.div_mod_to_equations. lia. }
    pose proof (mutex_cells_to m1 _ _ _ _ _ _ _ E1' MW MJ) as MX. clear MW MJ.
    lstep. (* [comment removed for export] *)
    do 4 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (4096 + mb)) with (wz (sec_alloc_beg mb)) by (unfold wz, sec_alloc_beg, SEC_HDR; f_equal; lia).
    apply evt_done. unfold gbb_post. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn. rewrite A_SECONDARY_val. intros; lia. }
    split; [exact WM|]. split; [assumption|]. split; [| exact ST].
    exists [b1; b2; b3]. rewrite A_SECONDARY_val. cbv beta delta [zb].
    lazymatch goal with |- rw_cells _ ?mm _ _ =>
      exact (proj1 (proj1 (rw_cells_app bsegs mm 681472 [C1 (Z_to_bv 8 0); CB 3 [b1; b2; b3]] [CB 4 j4]) MX)) end.
  Qed.
End Walk.

Theorem get_block_begin_proof : get_block_begin_spec.
Proof.
  unfold get_block_begin_spec. intros until lo. intros (HR & WF & HM & HG & HFR & HSW) HIN HP -> -> ST CEIL LO MI.
  eapply gbb_walk; eassumption.
Qed.


End CeilWrap.
