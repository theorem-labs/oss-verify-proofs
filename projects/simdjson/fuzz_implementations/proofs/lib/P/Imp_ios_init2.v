(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_loc_get0 Pj_os_kit Exit Imp_ios_defs Imp_ios_iface
  Imp_iosbase F_uselocale F_cxa_guard F_cxa_atexit Imp_ios_sb Imp_ios_imbue Imp_ios_init.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac retpc_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.

Ltac norm_addr H := lazymatch type of H with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in H end.
Ltac locx_now X1 X2 X3 X4 X5 X6 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (LX : locx mm) by (exact (conj (conj X1 (conj X2 X3)) (conj X4 (conj X5 X6)))) end.

Definition cxa0_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (1088992 + 8, 1088992 + 24); (1088992 + 32 + 8 * 0, 1088992 + 40 + 8 * 0); (1088992 + 288 + 8 * 0, 1088992 + 296 + 8 * 0)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (1088992 + 4) [C4 z64; C4 (Z_to_bv 64 (0 + 1))]
    /\ rw_cells psegs m' (1088992 + 16) [C8 (Z_to_bv 64 (1088992 + 24))]
    /\ rw_cells psegs m' (1088992 + 32 + 8 * 0) [C8 (Z_to_bv 64 X_IOSDTOR)]
    /\ rw_cells psegs m' (1088992 + 288 + 8 * 0) [C8 (Z_to_bv 64 949816)].
Lemma cxa0_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (f0 a0v : word) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] -> cxa_pre m 0 f0 a0v -> mem_inv psegs m ->
  a0 = Z_to_bv 64 X_IOSDTOR -> a1 = Z_to_bv 64 949816 -> (lo <= bv_unsigned sp - 48)%Z -> (GLOBALS_TOP <= lo)%Z ->
  evt psegs (cxa0_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RCXA_ATEXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST LCH PRE MI -> -> LO GLO.
  eapply evt_mono.
  { eapply (cxa_atexit_spec0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo X_IOSDTOR 949816 f0 a0v cdt thr sec tm1);
      [exact ST| exact LCH| exact PRE| exact MI| reflexivity| reflexivity| unfold X_IOSDTOR; lia| lia| exact LO| exact GLO]. }
  intros ms' P. unfold cxa_atexit_post, cxa0_postZ, AEX in *. exact P.
Qed.

Theorem ios_init_proof : ios_init_stmt.
Proof.
  unfold ios_init_stmt. intros until tm1. intros ST LO GLO SPHI IOSZ L0 AEXZ IMG LCH LK TPL SSP TPE MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_IOS_INIT, IOS, AEX, IOS_RLIBC, IOS_LOCLOCK, IOS_TPLOC, IOS_GLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 736, bv_unsigned sp); (0xe7e70, 0xe9488); (0xe9d68, 0xe9d70); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold LOC0, loc0_cells in L0. destruct SSP as [SG SC]. unfold got_ssp, ssp_guard in SG, SC.
  destruct IMG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).

  retype IOSZ [CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6); CB 1888 (repeat (Z_to_bv 8 0) 1888)].
  takeZ IOSZ 1%nat 949872%Z Z56. takeZ IOSZ 2%nat 949874%Z GRD. takeZ IOSZ 1%nat 949880%Z P6. rename IOSZ into IOSB.

  retype AEXZ [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
               CB 232 (repeat (Z_to_bv 8 0) 232); C8 z64; C8 z64; C8 z64].
  takeZ AEXZ 1%nat 1088993%Z FIN. takeZ AEXZ 1%nat 1088996%Z AP3. takeZ AEXZ 2%nat 1089004%Z LS. takeZ AEXZ 1%nat 1089008%Z AP4.
  takeZ AEXZ 1%nat 1089016%Z HD. takeZ AEXZ 1%nat 1089024%Z NX. takeZ AEXZ 1%nat 1089032%Z F0. takeZ AEXZ 2%nat 1089048%Z F12. takeZ AEXZ 1%nat 1089280%Z F3.
  takeZ AEXZ 1%nat 1089288%Z A0. rename AEXZ into A12.
  carve_frame 32%nat ST.
  lstep. lstep. lstep. lstep.
  lstep. lstep.
  lstep.
  change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  lstep.
  lstep. if_lit.
  lstep. lstep.
  lstep.
  call (guard_acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 949872%Z); [exact GRD | reflexivity | lia | lia | assumption |].
  try clear GRD. match goal with H : rw_cells psegs _ 949872 [C1 _; C1 _] |- _ => rename H into GRD end.
  lstep.
  try (replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity)).
  lstep. try if_lit.
  lstep.
  call_sp (doiosinit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo canary cdt thr sec tm1);
    [exact ST | unfold DOIOS_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | exact IOSB | exact L0 | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj G11 (conj G12 G13)))))))))))) | exact LCH | exact LK | exact TPL | exact (conj SG SC) | exact TPE | assumption |].
  try clear IOSB; try clear L0; try clear TPL.
  match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ _ ios_cells64 |- _ => rename H into IOS64; norm_addr IOS64; unfold ios_cells64, ios_cells in IOS64; cbv [skipn] in IOS64 end.
  match goal with H : rw_cells psegs _ 0xe9d68 _ |- _ => rename H into TPL end.
  match goal with H : LOCB _ |- _ => rename H into LB end.
  match goal with H : locx _ |- _ => destruct H as ((LX1 & LX2 & LX3) & LX4 & LX5 & LX6) end.
  unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4, VT_CVC, VT_CVW, CLOC in LX1, LX2, LX3, LX4, LX5, LX6. change (952960 + 16)%Z with 952976%Z in LX3.
  match goal with H : ssp_cells _ canary |- _ => destruct H as [SG2 SC2]; unfold got_ssp, ssp_guard in SG2, SC2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp - 736, bv_unsigned sp); (0xe7e70, 0xe7e72); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z mm) as MU3;
    pose proof (wmono_refl psegs mm) as WM3 end.
  lstep. lstep. lstep. lstep.
  lstep.
  lstep.
  call_sp (cxa0_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo _ _ cdt thr sec tm1);
    [exact ST | exact LCH | exact (conj FIN (conj LS (conj HD (conj F0 A0)))) | assumption | unfold X_IOSDTOR; reflexivity | reflexivity | lia | unfold GLOBALS_TOP; lia |].
  try clear LS; try clear HD; try clear F0; try clear A0.
  match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  lstep.
  lstep. lstep. lstep. lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  call (guard_release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 949872%Z _ _); [exact GRD | reflexivity | lia | lia | assumption |].
  try clear GRD. match goal with H : rw_cells psegs _ 949872 [C1 _; C1 _] |- _ => rename H into GRD end.

  lazymatch type of MU3 with munch ?W ?ma ?mb =>
    assert (LB3 : LOCB mb) by (apply (LOCB_transport W ma mb LB MU3 WM3); cbv [disjoint_from fst snd]; repeat split; lia) end.
  locx_now LX1 LX2 LX3 LX4 LX5 LX6.

  glueZ Z56 GRD. glueZ Z56 P6. glueZ Z56 IOS64.
  let csa := eval cbv in ios_cells in
  lazymatch type of Z56 with rw_cells _ _ _ ?cs => let n := eval vm_compute in (length cs) in retype_at Z56 0%nat n csa end;
  change csa with ios_cells in Z56.

  match goal with H : rw_cells psegs _ (1088992 + 4) _ |- _ => rename H into LS1; norm_addr LS1; change (0 + 1)%Z with 1%Z in LS1 end.
  match goal with H : rw_cells psegs _ (1088992 + 16) _ |- _ => rename H into HD1; norm_addr HD1 end.
  match goal with H : rw_cells psegs _ (1088992 + 32 + 8 * 0) _ |- _ => rename H into F01; norm_addr F01 end.
  match goal with H : rw_cells psegs _ (1088992 + 288 + 8 * 0) _ |- _ => rename H into A01; norm_addr A01 end.
  glueZ HD1 NX. glueZ HD1 F01. glueZ HD1 F12. glueZ A01 A12.
  apply evt_done. unfold ios_init_post. sys_finish.
  all: first [exact Z56 | exact (conj SG2 SC2) | idtac].
  unfold aex_tbl, AEX, AEX_IOS. change (1 <=? 1)%Z with true. change (1 <=? 2)%Z with true. cbv iota.
  split; [exact FIN|]. split; [exact LS1|]. split; [exact HD1| exact A01].
Qed.
