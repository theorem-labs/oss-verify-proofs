(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Imp_ios_defs Imp_iosbase F_uselocale Imp_ios_sb.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac retpc_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.

Definition F_IMBUE_C : Z := 0x86fe4.
Definition F_IMBUE_W : Z := 0x87750.
Definition F_WENCODING : Z := 0xaf634.
Definition VTS_CVC_ENC : Z := 0xdfc80.
Definition VTS_CVW_ENC : Z := 0xdf9d0.
Notation TPLOC := 0xf5518%Z (only parsing).
Notation GLOC := 0x115810%Z (only parsing).
Notation RTP_ := 0xf5548%Z (only parsing).

Definition wencoding_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (TPLOC, TPLOC + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' TPLOC [C8 (Z_to_bv 64 GLOC)].

Lemma wencoding_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  a0 = Z_to_bv 64 LOC_CVW -> rw_cells usegs m (LOC_CVW + 16) [C8 (Z_to_bv 64 CLOC)] ->
  tp = Z_to_bv 64 RTP_ -> rw_cells usegs m TPLOC [C8 (Z_to_bv 64 GLOC)] ->
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48) -> (GLOBALS_TOP <= lo) ->
  mem_inv usegs m ->
  evt usegs (wencoding_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_WENCODING) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros -> CVL -> TPL ST LO GLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_WENCODING, GLOBALS_TOP, CLOC, LOC_CVW in *. change (999984 + 16)%Z with 1000000%Z in CVL.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (0xf5518, 0xf5518 + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  Ltac eval_post H := cbn [usel_ret usel_new] in H;
    match type of H with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] => let v' := eval vm_compute in v in replace v with v' in H by (vm_compute; reflexivity) end.
  carve_frame 48%nat ST.
  do 5 lstep.
  lstep. lstep.
  lstep.
  name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST, FR by lia.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1136656 149832); [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. rename POST into TPL1.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. if_lit.
  lstep. lstep. try retpc_lit.
  lstep.
  lstep. if_lit.
  lstep. lstep.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 149832 18446744073709551615); [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. rename POST into TPL2.
  lstep. if_lit.
  lstep.
  lstep. if_lit.
  lstep.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1136656 149832); [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. rename POST into TPL3.
  lstep. lstep.
  lstep.
  lstep. lstep.
  lstep.
  lstep. if_lit.
  lstep. lstep. try retpc_lit.
  lstep.
  lstep. if_lit.
  lstep. lstep.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 149832 18446744073709551615); [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. rename POST into TPL4.
  lstep. lstep.
  do 4 lstep.
  unname_sp.
  lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold wencoding_post. sys_finish.
Qed.

Section Imbue.
  Variables (ENTRY GOTID ID FAC VTS FENC FNOC NOCONV : Z).

  Definition imbue_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo SB : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (SB + 72, SB + 80); (SB + 88, SB + 92); (SB + 97, SB + 98); (TPLOC, TPLOC + 8)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ LOCB m'
      /\ rw_cells usegs m' (SB + 72) [C8 (Z_to_bv 64 FAC)] /\ rw_cells usegs m' (SB + 88) [C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' (SB + 97) [C1 (Z_to_bv 8 NOCONV)]
      /\ rw_cells usegs m' TPLOC [C8 (Z_to_bv 64 GLOC)].

  Definition imbue_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo SB P : Z) (j72 j88 j97 : list byte),
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^62) ->
    LOCB m -> locx m ->
    rw_cells usegs m P [C8 (Z_to_bv 64 LOC_IMP)] -> (bv_unsigned sp <= P) -> (P + 8 <= 2^62) ->
    rw_cells usegs m (SB + 72) [CB 8 j72] -> rw_cells usegs m (SB + 88) [CB 4 j88] -> rw_cells usegs m (SB + 97) [CB 1 j97] -> (0 <= SB) -> (SB + 98 <= 0xf3d88) ->
    rw_cells usegs m GOTID [C8 (Z_to_bv 64 ID)] -> (0 <= GOTID /\ GOTID + 8 <= SB) ->
    rw_cells usegs m VTS [C8 (Z_to_bv 64 FENC); C8 (Z_to_bv 64 FNOC)] -> (0 <= VTS /\ VTS + 16 <= SB) ->
    tp = Z_to_bv 64 RTP_ -> rw_cells usegs m TPLOC [C8 (Z_to_bv 64 GLOC)] ->
    mem_inv usegs m ->
    evt usegs (imbue_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo SB m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 P) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
End Imbue.

Ltac imbue_prologue :=
  intros until j97; intros ST LO LOLO SPHI LB LX PL PLO PHI C72 C88 C97 SB0 SBH GID GIDB VSL VSLB TPE TPL MI;
  destruct LX as ((LX1 & LX2 & LX3) & LX4 & LX5 & LX6); unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4, VT_CVC, VT_CVW, CLOC in LX1, LX2, LX3, LX4, LX5, LX6;
  rename LB into LBm.

Lemma imbue_c_spec : imbue_stmt F_IMBUE_C 0xe1b18 LOC_IDC LOC_CVC VTS_CVC_ENC 0xaed94 0xaed9c 1.
Proof.
  unfold imbue_stmt. imbue_prologue.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_IMBUE_C, LOC_IDC, LOC_CVC, VTS_CVC_ENC, GLOBALS_TOP, LOC_IMP in *.
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (SB + 72, SB + 80); (SB + 88, SB + 92); (SB + 97, SB + 98); (0xf5518, 0xf5518 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 16%nat ST.
  lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep.
  lstep.
  lstep.
  locb_now LBm MU WM.
  pose proof (proj1 (proj1 (rw_cells_app usegs _ _ [C8 (Z_to_bv 64 999584)] [C8 (Z_to_bv 64 999984)]) LX6)) as FAC4.
  call_sp (use_facet_id_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo P 0xf3ed0 5 0xf40a0);
    [exact ST | lia | unfold GLOBALS_TOP; lia | exact LB | exact PL | lia | exact LX4 | lia | unfold GLOBALS_TOP; lia | lia | exact FAC4 | lia | assumption |].
  clear LB. clear POST. rename PC into ST.
  lstep.
  lstep.
  lstep.
  lstep.
  lstep. lstep. try retpc_lit.
  lstep. lstep.
  lstep.
  lstep.
  lstep. lstep.
  lstep. lstep. try retpc_lit.
  lstep.
  lstep.
  lstep.
  lstep. try if_lit.
  lstep. lstep.
  lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  locb_now LBm MU WM.
  apply evt_done. unfold imbue_post. sys_finish.
Qed.

Lemma imbue_w_spec : imbue_stmt F_IMBUE_W 0xe1b28 LOC_IDW LOC_CVW VTS_CVW_ENC 0xaf634 0xaf734 0.
Proof.
  unfold imbue_stmt. imbue_prologue.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_IMBUE_W, LOC_IDW, LOC_CVW, VTS_CVW_ENC, GLOBALS_TOP, LOC_IMP in *.
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (SB + 72, SB + 80); (SB + 88, SB + 92); (SB + 97, SB + 98); (0xf5518, 0xf5518 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 16%nat ST.
  lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep.
  lstep.
  lstep.
  locb_now LBm MU WM.
  pose proof (proj2 (proj1 (rw_cells_app usegs _ _ [C8 (Z_to_bv 64 999584)] [C8 (Z_to_bv 64 999984)]) LX6)) as FAC4.
  lazymatch type of FAC4 with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in FAC4 end.
  call_sp (use_facet_id_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo P 0xf3ee0 6 0xf4230);
    [exact ST | lia | unfold GLOBALS_TOP; lia | exact LB | exact PL | lia | exact LX5 | lia | unfold GLOBALS_TOP; lia | lia | exact FAC4 | lia | assumption |].
  clear LB. clear POST. rename PC into ST.
  lstep.
  lstep.
  lstep.
  lstep.
  call_sp (wencoding_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo); [reflexivity | exact LX3 | exact TPE | exact TPL | exact ST | lia | unfold GLOBALS_TOP; lia | assumption |].
  try clear TPL. rename POST into TPL. rename PC into ST.
  lstep. lstep.
  lstep.
  lstep.
  lstep. lstep.
  lstep. lstep. try retpc_lit.
  lstep.
  lstep.
  lstep.
  lstep. try if_lit.
  lstep. lstep.
  lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  locb_now LBm MU WM.
  apply evt_done. unfold imbue_post. sys_finish.
Qed.
