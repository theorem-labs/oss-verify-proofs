(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF RT_img.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_leaves_zone RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem set_oom_proof : set_oom_spec.
Proof.
  unfold set_oom_spec. intros until lo. intros HR WF MI ST HCEIL LO.
  pose proof (munch_refl [(A_ALLOC_OOM, A_ALLOC_OOM + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rr_consts st m HR) as HC.
  (nelim HC 16%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ [oom OOM] _).
  unfold A_SET_OOM_FN. unfold A_ALLOC_OOM in *. leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold leaf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  (* [comment removed for export] *)
  assert (HWok : Forall iaz_ok [(1230048, 1230048 + 1)]) by (constructor; [left; cbn; unfold IAZ_LO, IAZ_HI; lia| constructor]).
  eapply (iaz_transport st WF _ HWok m _ MU WM HR).
  - eapply (R_consts_iaz st st _ m _ MU WM); [| exact WF| reflexivity| exact (rr_consts st m HR)| eexists; exact OOM| ].
    + intros a sz Hz. cbn. unfold IAZ_LO, RT_artF.CEIL in Hz. split; [lia| exact I].
    + pose proof (rr_consts st m HR) as HC.
      (nelim HC 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H20 _).
      eapply (rwT _ m _ MU WM _ _ H20). unfold A_IA_INITED. cbn. lia.
  - eapply (T_ia _ m _ MU WM (rr_ia st m HR)). intros i Hi. unfold A_IA_MAP1. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma ia_chunk : forall m lo n, A_IA_INSTANCE <= lo -> lo + n <= A_IA_INSTANCE + A_IA_SIZE -> 0 <= n ->
  exists j, rw_cells asegs m lo [CB (Z.to_nat n) j].
Proof.
  intros m lo n H1 H2 Hn. unfold A_IA_INSTANCE, A_IA_SIZE in *.
  pose proof (img_rw_stk m lo (lo + n) ltac:(unfold ASEG2_LO; lia) ltac:(unfold AIMG_HI; lia) ltac:(lia)) as ST.
  (nelim (stk_carve asegs m lo (lo + n) (Z.to_nat n) ST ltac:(lia)) 3%nat; intros _ j FR).
  exists j. replace (lo + n - Z.of_nat (Z.to_nat n)) with lo in FR by lia. exact FR.
Qed.

(* [comment removed for export] *)
Lemma flw_to_C4 : forall m f, 0 <= f < 256 ->
  rw_cells asegs m 0x139d08 [C1 (Z_to_bv 8 f); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x139d08 [C4 (Z_to_bv 64 f)].
Proof.
  intros m f Hf H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. rewrite (Z.div_small f) by lia. reflexivity.
Qed.
Lemma flw_of_C4_256 : forall m,
  rw_cells asegs m 0x139d08 [C4 (Z_to_bv 64 256)] ->
  rw_cells asegs m 0x139d08 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  change (Z.shiftr 256 8) with 1. change (Z.shiftr 1 8) with 0. change (Z.shiftr 0 8) with 0.
  rewrite app_nil_r. f_equal. apply bv_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma R_ia_of_chunk : forall m N, Z.of_nat N = 262144 ->
  rw_cells asegs m 701576 [CB N (repeat (zb 0) N)] -> R_ia m.
Proof.
  intros m N HN [[_ HB] HW] i Hi. unfold A_IA_MAP1. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size Cells.csize] in HW. rewrite Nat.add_0_r in HW.
  (nelim HB 3%nat; intros B0 B1 HB). (nelim HW 3%nat; intros W0 W1 HW). rewrite repeat_length in B1, HB.
  split; [split; [cbn; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. change (le8 (wz 0)) with (repeat (zb 0) 8).
    split; [lia|]. split; [cbn [length repeat]; lia|].
    intros k Hk. change (length (repeat (zb 0) 8)) with 8%nat in Hk.
    replace (701576 + 8 * i + Z.of_nat k) with (701576 + Z.of_nat (Z.to_nat (8 * i) + k)) by lia.
    rewrite HB by lia. rewrite !nth_error_repeat by lia. reflexivity.
  - cbn [cells_size Cells.csize]. split; [lia|]. split; [lia|]. intros k Hk.
    replace (701576 + 8 * i + k) with (701576 + (8 * i + k)) by lia. apply HW. lia.
Qed.

Section IA.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 48 <= bv_unsigned sp.

  #[warnings="-notation-for-abbreviation"] Notation W := [(bv_unsigned sp - 48, bv_unsigned sp); (701568, 1230000); (1285384, 1285388)].
  #[warnings="-notation-for-abbreviation"] Notation POST := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W lo m
               (fun a0' _ m' => a0' = wz A_IA_INSTANCE /\ RTREP (set_ia_inited st) m')).

  Ltac ia_carve lo n CH := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let j := fresh "j" in
    destruct (ia_chunk mm lo n ltac:(unfold A_IA_INSTANCE; lia) ltac:(unfold A_IA_INSTANCE, A_IA_SIZE; lia) ltac:(lia)) as [j CH] end.
  (* [comment removed for export] *)
  Ltac ia_carve_lit lo n CH := ia_carve lo n CH; let k := eval vm_compute in (Z.to_nat n) in change (Z.to_nat n) with k in CH.
  Ltac restk :=
    repeat match goal with H : stk _ ?mm ?lo ?x, H' : stk _ ?mm' ?lo ?x' |- _ => constr_eq mm mm'; clear H' end;
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  (* [comment removed for export] *)
  Ltac ia_memset CH :=
    lstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MIh : mem_inv _ mm |- _ =>
      lazymatch goal with STh : stk _ mm _ _ |- _ =>
        call internal_memset_Z; [exact MIh | lia | lia | lia | exact CH | rewrite unsigned_lit by lia; exact STh | idtac; lia | ]
      end end end;
    try clear CH; restk;
    match goal with H : rw_cells _ _ _ [CB _ (repeat _ _)] |- _ => rename H into MSP end.
  Ltac cur_MI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIh : mem_inv _ mm |- _ => MIh end end.

  Lemma ia_not_inited :
    st_ia_inited st = false ->
    rw_cells asegs m 0x139d08 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5fd14) fc None m (seg_rom asegs)).
  Proof.
    intros NI FL. pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof HCEIL as CEIL'.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    leaf_prep.
    assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    carve_frame 48%nat ST.
    do 6 lstep. (* [comment removed for export] *)
    lstep. lstep. fl. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia.
    (* [comment removed for export] *)
    apply flw_to_C4 in FL; [|lia].
    do 8 (lstep; fl).
    amo_step. fl.
    lstep. lstep. lstep. lstep. fl.
    amo_step. fix_lit_store. fl.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    apply flw_of_C4_256 in FL.
    lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    do 7 (lstep; fl).
    (* [comment removed for export] *)
    ia_carve 1229960 40 CH1. ia_memset CH1. try rewrite E48 in *. clear MSP.
    (* [comment removed for export] *)
    ia_carve_lit 701568 8 CH0. lstep. clear CH0.
    do 4 (lstep; fl).
    (* [comment removed for export] *)
    ia_carve 701576 262144 CH2. ia_memset CH2. try rewrite E48 in *.
    pose proof (R_ia_of_chunk _ _ ltac:(apply Z2Nat.id; lia) MSP) as IA2. clear MSP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (963776, 1230000); (1285384, 1285388)] mm) as MU2;
      pose proof (wmono_refl asegs mm) as WM2 end.
    do 5 (lstep; fl).
    (* [comment removed for export] *)
    ia_carve 963776 3456 CH3. ia_memset CH3. try rewrite E48 in *. clear MSP.
    do 5 (lstep; fl).
    (* [comment removed for export] *)
    ia_carve 967232 262728 CH4. ia_memset CH4. try rewrite E48 in *. clear MSP.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (roT _ m mm MU 0xa1f60 [C8 (wz 0x139d20)] (R_link_at m 0xa1f60 0x139d20 (rr_link st m HR) ltac:(vm_compute; reflexivity))
                    ltac:(cbn; lia)) as GOTC;
      pose proof (rr_consts st m HR) as HC;
      (nelim HC 6%nat; intros _ _ _ _ K5 _);
      pose proof (roT _ m mm MU _ _ K5 ltac:(unfold A_PAGESIZE_CACHED; cbn; lia)) as PSC; clear K5;
      unfold A_PAGESIZE_CACHED in PSC;
      change (cells_at asegs mm 0xa1f60 [C8 (wz 0x139d20)]) with (ro_cells asegs mm 0xa1f60 [C8 (wz 0x139d20)]) in GOTC;
      change (cells_at asegs mm 1285408 [W8 4096]) with (ro_cells asegs mm 1285408 [W8 4096]) in PSC
    end.
    cbv beta delta [wz] in GOTC, PSC.
    lstep. lstep. fl. clear GOTC. (* [comment removed for export] *)
    lstep. fl. clear PSC. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    do 4 (lstep; fl).
    ia_carve_lit 967232 16 CH5.
    lstep. lstep. (* [comment removed for export] *) clear CH5.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. fl. (* [comment removed for export] *)
    do 7 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. { unfold A_IA_INSTANCE. reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with |- RTREP _ ?mm =>
      assert (HWok : Forall iaz_ok W)
        by (repeat (constructor; [unfold iaz_ok; cbn [fst snd]; unfold IAZ_LO, IAZ_HI, RT_artF.CEIL; lia|]); constructor);
      (nelim (iaz_others st WF _ HWok m mm MU WM HR) 14%nat; intros X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X16);
      apply RTREP_set_ia; try assumption
    end.
    - (* [comment removed for export] *)
      lazymatch goal with |- R_consts _ ?mm =>
        eapply (R_consts_iaz st (set_ia_inited st) _ m mm MU WM); [| exact WF| apply st_tls_set_ia| exact (rr_consts st m HR)| |] end.
      + intros a sz Hz. cbn. unfold IAZ_LO, RT_artF.CEIL in Hz. split; [lia|]. split; [lia|]. split; [lia| exact I].
      + pose proof (rr_consts st m HR) as HC.
        (nelim HC 16%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ [oom OOM] _).
        exists oom. lazymatch goal with |- rw_cells _ ?mm _ _ => eapply (rwT _ m mm MU WM _ _ OOM) end. unfold A_ALLOC_OOM. cbn. lia.
      + rewrite st_ia_inited_set. unfold A_IA_INITED. cbv beta delta [zb].
        exact FL.
    - (* [comment removed for export] *)
      lazymatch goal with |- R_ia ?mm => eapply (T_ia _ _ mm MU2 WM2 IA2) end.
      intros i Hi. unfold A_IA_MAP1. cbn. lia.
  Qed.

  Lemma ia_inited : forall f : Z, 1 <= f < 128 ->
    st_ia_inited st = true ->
    rw_cells asegs m 0x139d08 [C1 (Z_to_bv 8 f)] ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5fd14) fc None m (seg_rom asegs)).
  Proof.
    intros f Hf INI FL. pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof HCEIL as CEIL'.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU1.
    leaf_prep.
    carve_frame 48%nat ST.
    do 6 lstep. (* [comment removed for export] *)
    lstep. lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sxb (Z_to_bv 8 f)) with (Z_to_bv 64 f : word)
      by (unfold sxb; f_equal; rewrite Z_to_bv_signed; symmetry; apply bv_swrap_small; unfold bv_half_modulus, bv_modulus; cbn; lia).
    lstep. (* [comment removed for export] *)
    lstep. if_lia.
    lstep. lstep. fl. (* [comment removed for export] *)
    do 7 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    finish. { unfold A_IA_INSTANCE. reflexivity. }
    rewrite (set_ia_inited_true st INI).
    lazymatch goal with |- RTREP _ ?mm => eapply (RTREP_high st _ m mm WF); [| exact MU1| exact WM| exact HR] end.
    constructor; [cbn; lia| constructor].
  Qed.
End IA.


Theorem internal_allocator_proof : internal_allocator_spec.
Proof.
  unfold internal_allocator_spec. intros until lo. intros HR WF MI ST HCEIL LO.
  unfold A_INTERNAL_ALLOCATOR. cbv beta delta [wz].
  pose proof (rr_consts st m HR) as HC.
  (nelim HC 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H20 _).
  unfold A_IA_INITED in H20. cbv beta delta [zb] in H20.
  lazymatch goal with |- evt _ (leaf_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?W _ _ _) _ =>
    change W with [(bv_unsigned sp - 48, bv_unsigned sp); (701568, 1230000); (1285384, 1285388)] end.
  destruct (st_ia_inited st) eqn:E.
  - pose proof (rw_cells_take _ _ [C1 (Z_to_bv 8 1)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] H20) as FL1.
    eapply (ia_inited _ sp); [exact HR| exact WF| exact MI| exact ST| exact HCEIL| exact LO| | exact E| exact FL1]. lia.
  - eapply (ia_not_inited _ sp); [exact HR| exact WF| exact MI| exact ST| exact HCEIL| exact LO| exact E| exact H20].
Qed.


End CeilWrap.
