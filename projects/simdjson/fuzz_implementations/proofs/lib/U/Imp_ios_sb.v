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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Imp_ios_defs Imp_iosbase.
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

Definition F_USE_FACET : Z := 0xac380.
Definition F_SBC_CTOR : Z := 0x86ce8.
Definition F_SBW_CTOR : Z := 0x86dd8.
Definition F_LOCALE_COPY : Z := 0xabaf4.
Definition F_LOCALE_DTOR : Z := 0xabb18.
Definition LOC_IMP : Z := 0xf4388.
Definition LOC_FACETS : Z := 0xf43b0.
Definition GOT_SBVT : Z := 0xe19e8.
Definition GOT_WSBVT : Z := 0xe1b00.
Definition SBVT : Z := 0xdf090.
Definition WSBVT : Z := 0xdf1b0.
Definition VT_SBC : Z := 0xdf5d8.
Definition VT_SBW : Z := 0xdf708.
Definition GOT_IDC : Z := 0xe1b18.
Definition GOT_IDW : Z := 0xe1b28.
Definition VTS_CVC_NOCONV : Z := 0xdfc88.
Definition VTS_CVW_NOCONV : Z := 0xdf9d8.
Definition F_CVC_NOCONV : Z := 0xaed9c.
Definition F_CVW_NOCONV : Z := 0xaf734.

Definition use_facet_id_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (FAC : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FAC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ LOCB m'.

Lemma use_facet_id_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo P ID i FAC : Z),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48) -> (GLOBALS_TOP <= lo) ->
  LOCB m -> rw_cells usegs m P [C8 (Z_to_bv 64 LOC_IMP)] -> (bv_unsigned sp <= P < 2^63) ->
  rw_cells usegs m ID [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 i)] -> (0 <= ID) -> (ID + 12 <= GLOBALS_TOP) ->
  (1 <= i <= 30) ->
  rw_cells usegs m (LOC_FACETS + 8 * (i - 1)) [C8 (Z_to_bv 64 FAC)] -> (0 < FAC < 2^64) ->
  mem_inv usegs m ->
  evt usegs (use_facet_id_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo FAC m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 ID) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_USE_FACET) fc None m (seg_rom usegs)).
Proof.
  intros until FAC. intros ST LO LOLO LB LOC RP IDC ID0 IDH HI SLOT FB MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_USE_FACET, LOC_IMP, LOC_FACETS, GLOBALS_TOP in *.
  match type of SLOT with rw_cells _ _ ?A _ => remember A as SA eqn:ESA end.
  assert (HSA : SA = 0xf43b0 + 8 * (i - 1)) by exact ESA. clear ESA.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct LB as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & LB). unfold locb_cells in LB.
  carve_frame 48%nat ST.
  do 11 lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 i)) with (Z_to_bv 64 i : word) by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  do 5 lstep.
  lstep. if_cases Ki; zify_cond Ki. 1:{ exfalso. clear - Ki HI. rewrite ?unsigned_lit in Ki by lia. cbn in Ki. lia. } clear Ki.
  lstep. lstep.

  lazymatch goal with |- context [Z.shiftl ?x 3] => rewrite (Z.shiftl_mul_pow2 x 3) by lia end || idtac.
  try (replace (0xf43b0 + (i - 1) * 2 ^ 3) with SA by lia).
  try (replace (0xf43b0 + (i + -1) * 2 ^ 3) with SA by lia).
  try (replace (0xf43b0 + Z.shiftl (i - 1) 3) with SA by (rewrite Z.shiftl_mul_pow2 by lia; lia)).
  lstep.
  lstep. if_cases Kf; [exfalso; unfold bv_eqb in Kf; rewrite !unsigned_lit in Kf by lia; apply Z.eqb_eq in Kf; lia|]. clear Kf.
  do 4 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  unfold use_facet_id_post. sys_finish.
  exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15. assumption.
Qed.

Section SbCtor.
  Variables (ENTRY GOTV SBV VT GOTID ID FAC VTSLOT FNOCONV NOCONV : Z).

  Definition sb_obj_cells (f st : Z) : list cell :=
    [C8 (Z_to_bv 64 VT); C8 (Z_to_bv 64 LOC_IMP); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
     C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 FAC); C8 (Z_to_bv 64 st); C1 (Z_to_bv 8 NOCONV)].

  Definition sb_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo D f st : Z) (jt : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (D, D + 89)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ LOCB m'
      /\ rw_cells usegs m' D (sb_obj_cells f st ++ [CB 7 jt]).

  Definition sb_ctor_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo D f st : Z) (junk jt : list byte),
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 112) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^62) ->
    LOCB m -> locx m ->
    rw_cells usegs m D [CB 89 junk] -> rw_cells usegs m (D + 89) [CB 7 jt] -> (0 <= D) -> (D + 96 <= 0xf3d88) ->
    rw_cells usegs m GOTV [C8 (Z_to_bv 64 SBV)] -> rw_cells usegs m GOTID [C8 (Z_to_bv 64 ID)] -> rw_cells usegs m VTSLOT [C8 (Z_to_bv 64 FNOCONV)] ->
    (0 <= GOTV /\ GOTV + 8 <= D) -> (0 <= GOTID /\ GOTID + 8 <= D) -> (0 <= VTSLOT /\ VTSLOT + 8 <= D) ->
    (0 <= f < 2^64) -> (0 <= st < 2^64) ->
    mem_inv usegs m ->
    evt usegs (sb_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D f st jt m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 f) (Z_to_bv 64 st) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
End SbCtor.

Ltac locb_now LBm MU WM := lazymatch type of MU with munch ?W ?ma ?mb =>
  assert (LB : LOCB mb) by (apply (LOCB_transport W ma mb LBm MU WM); cbv [disjoint_from fst snd]; repeat split; lia) end.

Lemma sbc_ctor_spec : sb_ctor_stmt F_SBC_CTOR GOT_SBVT SBVT VT_SBC GOT_IDC LOC_IDC LOC_CVC VTS_CVC_NOCONV F_CVC_NOCONV 1.
Proof.
  unfold sb_ctor_stmt. intros until jt; intros ST LO LOLO SPHI LB LX OBJ TAIL D0 DHI GV GID VSL GVB GIDB VSLB FB STB MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  unfold F_SBC_CTOR, GOT_SBVT, SBVT, VT_SBC, GOT_IDC, LOC_IDC, LOC_CVC, VTS_CVC_NOCONV, F_CVC_NOCONV, GLOBALS_TOP, LOC_IMP in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (D, D + 89)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

  destruct LX as ((LX1 & LX2 & LX3) & LX4 & LX5 & LX6). unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4, VT_CVC, VT_CVW, CLOC in LX1, LX2, LX3, LX4, LX5, LX6.

  apply (rw_cells_split_CB usegs _ _ [] 89 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 1]%nat) in OBJ; [|reflexivity].
  cbn [mk_CB_cells app] in OBJ. forget_junk OBJ.
  carve_frame 64%nat ST.
  do 10 lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep.
  lstep.
  takeZ OBJ 1%nat (D + 8)%Z VP0. takeZ OBJ 1%nat (D + 16)%Z LC0.

  rename LB into LBm.
  locb_now LBm MU WM.
  call_sp (locale_ctor_specS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (D + 8)%Z _);
    [exact ST | lia | lia | exact LB | exact LC0 | lia | lia | lia | assumption |].
  try clear LB; try clear LC0. clear POST. rename PC0 into LC0. rename PC into ST.
  do 2 lstep. lstep.
  do 6 lstep.
  lstep.
  lstep. lstep.
  lstep.

  lazymatch goal with FRx : rw_cells _ _ _ (CB 16 ?jj :: ?post) |- _ =>
    apply (rw_cells_split_CB usegs _ _ [] 16 jj post [8; 8]%nat) in FRx; [|reflexivity]; cbn [mk_CB_cells app] in FRx; forget_junk FRx;
    takeZ FRx 1%nat (bv_unsigned sp + -56)%Z J0; takeZ FRx 1%nat (bv_unsigned sp + -48)%Z SLT; rename FRx into FSV end.
  call_sp (locale_copy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -56)%Z (D + 8)%Z _);
    [exact LC0 | exact SLT | lia | lia | lia | assumption |].
  try clear SLT. rename POST into SLT.
  lstep. lstep. lstep.
  lstep.
  locb_now LBm MU WM.
  pose proof (proj1 (proj1 (rw_cells_app usegs _ _ [C8 (Z_to_bv 64 999584)] [C8 (Z_to_bv 64 999984)]) LX6)) as FAC4.
  call_sp (use_facet_id_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (bv_unsigned sp + -56)%Z 0xf3ed0 5 0xf40a0);
    [exact ST | lia | unfold GLOBALS_TOP; lia | exact LB | exact SLT | lia | exact LX4 | lia | unfold GLOBALS_TOP; lia | lia | exact FAC4 | lia | assumption |].
  clear LB. clear POST. rename PC into ST.
  lstep. lstep.
  lstep.
  name_sp sp (-64)%Z.
  eapply evt_cut; [eapply locale_dtor_spec; [exact SLT| lia| assumption]|]. intros ms' (u0 & u1 & ->).
  replace (ret_pc (Z_to_bv 64 0x86d7c)) with (Z_to_bv 64 0x86d7c : word) by (apply bv_eq; vm_compute; reflexivity).
  unname_sp.
  lstep.
  lstep. lstep.
  lstep.
  lstep. lstep.
  lstep. lstep.
  replace (ret_pc (Z_to_bv 64 0x86d94)) with (Z_to_bv 64 0x86d94 : word) by (apply bv_eq; vm_compute; reflexivity).
  lstep.
  do 6 lstep.
  lstep.
  glueZ SLT FSV. glueZ J0 SLT. release_frame J0 ST (bv_unsigned sp).
  lstep.
  locb_now LBm MU WM.
  glueZ LC0 OBJ. glueZ VP0 LC0. glueZ VP0 TAIL.
  apply evt_done. unfold sb_ctor_post, sb_obj_cells, LOC_IMP. sys_finish.
Qed.

Lemma sbw_ctor_spec : sb_ctor_stmt F_SBW_CTOR GOT_WSBVT WSBVT VT_SBW GOT_IDW LOC_IDW LOC_CVW VTS_CVW_NOCONV F_CVW_NOCONV 0.
Proof.
  unfold sb_ctor_stmt. intros until jt; intros ST LO LOLO SPHI LB LX OBJ TAIL D0 DHI GV GID VSL GVB GIDB VSLB FB STB MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  unfold F_SBW_CTOR, GOT_WSBVT, WSBVT, VT_SBW, GOT_IDW, LOC_IDW, LOC_CVW, VTS_CVW_NOCONV, F_CVW_NOCONV, GLOBALS_TOP, LOC_IMP in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (D, D + 89)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

  destruct LX as ((LX1 & LX2 & LX3) & LX4 & LX5 & LX6). unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4, VT_CVC, VT_CVW, CLOC in LX1, LX2, LX3, LX4, LX5, LX6.

  apply (rw_cells_split_CB usegs _ _ [] 89 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 1]%nat) in OBJ; [|reflexivity].
  cbn [mk_CB_cells app] in OBJ. forget_junk OBJ.
  carve_frame 64%nat ST.
  do 10 lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep.
  lstep.
  takeZ OBJ 1%nat (D + 8)%Z VP0. takeZ OBJ 1%nat (D + 16)%Z LC0.

  rename LB into LBm.
  locb_now LBm MU WM.
  call_sp (locale_ctor_specS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (D + 8)%Z _);
    [exact ST | lia | lia | exact LB | exact LC0 | lia | lia | lia | assumption |].
  try clear LB; try clear LC0. clear POST. rename PC0 into LC0. rename PC into ST.
  do 2 lstep. lstep.
  do 6 lstep.
  lstep.
  lstep. lstep.
  lstep.

  lazymatch goal with FRx : rw_cells _ _ _ (CB 16 ?jj :: ?post) |- _ =>
    apply (rw_cells_split_CB usegs _ _ [] 16 jj post [8; 8]%nat) in FRx; [|reflexivity]; cbn [mk_CB_cells app] in FRx; forget_junk FRx;
    takeZ FRx 1%nat (bv_unsigned sp + -56)%Z J0; takeZ FRx 1%nat (bv_unsigned sp + -48)%Z SLT; rename FRx into FSV end.
  call_sp (locale_copy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -56)%Z (D + 8)%Z _);
    [exact LC0 | exact SLT | lia | lia | lia | assumption |].
  try clear SLT. rename POST into SLT.
  lstep. lstep. lstep.
  lstep.
  locb_now LBm MU WM.
  pose proof (proj2 (proj1 (rw_cells_app usegs _ _ [C8 (Z_to_bv 64 999584)] [C8 (Z_to_bv 64 999984)]) LX6)) as FAC4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in FAC4.
  lazymatch type of FAC4 with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in FAC4 end.
  call_sp (use_facet_id_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (bv_unsigned sp + -56)%Z 0xf3ee0 6 0xf4230);
    [exact ST | lia | unfold GLOBALS_TOP; lia | exact LB | exact SLT | lia | exact LX5 | lia | unfold GLOBALS_TOP; lia | lia | exact FAC4 | lia | assumption |].
  clear LB. clear POST. rename PC into ST.
  lstep. lstep.
  lstep.
  name_sp sp (-64)%Z.
  eapply evt_cut; [eapply locale_dtor_spec; [exact SLT| lia| assumption]|]. intros ms' (u0 & u1 & ->).
  replace (ret_pc (Z_to_bv 64 0x86e6c)) with (Z_to_bv 64 0x86e6c : word) by (apply bv_eq; vm_compute; reflexivity).
  unname_sp.
  lstep.
  lstep. lstep.
  lstep.
  lstep. lstep.
  lstep. lstep.
  replace (ret_pc (Z_to_bv 64 0x86e84)) with (Z_to_bv 64 0x86e84 : word) by (apply bv_eq; vm_compute; reflexivity).
  lstep.
  do 6 lstep.
  lstep.
  glueZ SLT FSV. glueZ J0 SLT. release_frame J0 ST (bv_unsigned sp).
  lstep.
  locb_now LBm MU WM.
  glueZ LC0 OBJ. glueZ VP0 LC0. glueZ VP0 TAIL.
  apply evt_done. unfold sb_ctor_post, sb_obj_cells, LOC_IMP. sys_finish.
Qed.
