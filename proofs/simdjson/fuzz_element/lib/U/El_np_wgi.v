(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memcmp Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit El_os_defs El_os_xsputn El_os_pad.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.

Lemma rw_cells_C1_CB1 : forall m A (b : byte), rw_cells usegs m A [C1 b] -> rw_cells usegs m A [CB 1 [b]].
Proof.
  intros m A b H. apply (rw_cells_retype usegs m A [C1 b] [CB 1 [b]] H); [cbn; repeat split; reflexivity | reflexivity | reflexivity].
Qed.

Definition widen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S D n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S + n)) a1 (Z_to_bv 64 (S + n)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat n) junk'].

Section Widen.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (S D n : Z) (src : list byte) (m0 : word -> option byte).
Hypothesis RS : (0 <= S)%Z.
Hypothesis RS2 : (S + n < 2^62)%Z.
Hypothesis RD : (0 <= D)%Z.
Hypothesis RD2 : (D + n < 2^62)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Hypothesis LEN : length src = Z.to_nat n.

Lemma widen_loop : forall (k : nat) (i : Z) (junk : list byte) (m : word -> option byte) (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  (n - i <= Z.of_nat k)%Z -> (0 <= i < n)%Z ->
  munch [(D, D + n)]%Z m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  bytes_at usegs m S src ->
  rw_cells usegs m D [CB (Z.to_nat n) junk] ->
  evt usegs (widen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S D n m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S + i)) a1 (Z_to_bv 64 (S + n)) (Z_to_bv 64 (D + i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa9060) fc None m (seg_rom usegs)).
Proof using RS RS2 RD RD2 SEP LEN.
  induction k as [|k IH]; intros i junk m t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 HK HI MU WM MI SRC DST; [lia|].

  pose proof (ro_C1_of_bytes m (S + i) _ (bytes_at_nth m S src i SRC ltac:(rewrite LEN; lia))) as SB.
  set (cs := (S + i)%Z) in *.
  destruct (rw_cells_CB_cut3 m D (Z.to_nat n) junk i 1 ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST) as (d1 & d2 & d3 & D1 & D2 & D3).
  change (Z.to_nat 1) with 1%nat in D2. clear DST.
  set (cd := (D + i)%Z) in *.
  lstep.
  lstep.
  lstep.
  sbZ.
  lstep.
  subst cs cd. apply rw_cells_C1_CB1 in D2.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_join3 mm D (Z.to_nat i) 1 (Z.to_nat n - Z.to_nat i - 1) (Z.to_nat n) d1 _ d3 (D + i)%Z (D + i + 1)%Z D1 D2 D3
                ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
  clear D1 D2 D3 SB.
  lstep.
  replace (S + i + 1)%Z with (S + (i + 1))%Z by lia. replace (D + i + 1)%Z with (D + (i + 1))%Z by lia.
  destruct (Z_lt_dec (i + 1) n) as [MORE|LAST].
  - bru true.
    eapply (IH (i + 1)%Z); try eassumption; lia.
  - bru false.
    replace (i + 1)%Z with n by lia.
    lstep.
    unfold widen_post. sys_finish; eassumption.
Qed.

Lemma widen_spec : forall (junk : list byte) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  (0 <= n)%Z -> mem_inv usegs m0 -> bytes_at usegs m0 S src -> rw_cells usegs m0 D [CB (Z.to_nat n) junk] ->
  evt usegs (widen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S D n m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 (S + n)) (Z_to_bv 64 D) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EL_DO_WIDEN_R) fc None m0 (seg_rom usegs)).
Proof using RS RS2 RD RD2 SEP LEN.
  intros until t6. intros RN MI SRC DST.
  pose proof (munch_refl [(D, D + n)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
  lstep.
  lstep.
  destruct (Z.eq_dec n 0) as [N0|N1].
  - bru true. subst n.
    lstep.
    unfold widen_post. replace (S + 0)%Z with S by lia. sys_finish; eassumption.
  - bru false.
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
    eapply (widen_loop (Z.to_nat n) 0%Z); try eassumption; lia.
Qed.
End Widen.

Definition wgi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo NB NP NE OB CAP POP POE : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (OB, OB + CAP); (POP, POP + 8); (POE, POE + 8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' OB [CB (Z.to_nat CAP) junk']
    /\ rw_cells usegs m' POP [C8 (Z_to_bv 64 (OB + (NP - NB)))]
    /\ rw_cells usegs m' POE [C8 (Z_to_bv 64 (OB + (NE - NB)))]
    /\ LOCB m'.

Definition wgi_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo NB NP NE OB CAP POP POE PLOC : Z) (src junk jp je : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x111000 <= lo)%Z ->
  rw_cells usegs m NB [CB (Z.to_nat (NE - NB)) src] -> (NB <= NP <= NE)%Z -> (NE - NB <= CAP)%Z ->
  rw_cells usegs m OB [CB (Z.to_nat CAP) junk] ->
  rw_cells usegs m POP [CB 8 jp] -> rw_cells usegs m POE [CB 8 je] -> rw_cells usegs m PLOC [C8 (Z_to_bv 64 EL_IMP)] ->
  (bv_unsigned sp <= NB)%Z -> (NE < 2^62)%Z -> (bv_unsigned sp <= OB)%Z -> (OB + CAP < 2^62)%Z ->
  (bv_unsigned sp <= POP)%Z -> (POP + 8 < 2^62)%Z -> (bv_unsigned sp <= POE)%Z -> (POE + 8 < 2^62)%Z -> (bv_unsigned sp <= PLOC)%Z -> (PLOC + 8 < 2^62)%Z ->
  (NE <= OB \/ OB + CAP <= NB)%Z -> (POP + 8 <= OB \/ OB + CAP <= POP)%Z -> (POE + 8 <= OB \/ OB + CAP <= POE)%Z -> (POE + 8 <= POP \/ POP + 8 <= POE)%Z ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (wgi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB NP NE OB CAP POP POE m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NB) (Z_to_bv 64 NP) (Z_to_bv 64 NE) (Z_to_bv 64 OB) (Z_to_bv 64 POP) (Z_to_bv 64 POE) (Z_to_bv 64 PLOC) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_WGI) fc None m (seg_rom usegs)).

Theorem wgi_proof : wgi_stmt.
Proof.
  unfold wgi_stmt. intros until je. intros ST LO LOLO SRC RNP RCAP DST HOP HOE HLOC R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 D1 D2 D3 D4 LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (OB, OB + CAP); (POP, POP + 8); (POE, POE + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct DCC as (_ & WS & _ & NPV & _ & _).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  carve_frame 160%nat ST.
  do 22 lstep.
  do 7 lstep.
  lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (vm_compute; reflexivity).
  do 6 lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_false.
  do 7 lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 11)) with (Z_to_bv 64 11) by (vm_compute; reflexivity).
  do 6 lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_false.
  do 4 lstep.
  lstep.

  retype_at LBC 25%nat 1%nat [CB 8 (repeat (Z_to_bv 8 0) 8)].
  do 2 lstep.
  lstep.
  if_false.
  retype_at LBC 25%nat 1%nat [C8 (Z_to_bv 64 0)].
  do 7 lstep.

  retype_at FR 1%nat 1%nat [CB 8 (repeat (Z_to_bv 8 0) 8)].
  do 2 lstep.
  lstep.
  if_true.
  lstep.
  lstep.
  if_false.
  do 6 lstep.
  lstep.
  assert (LEN : length src = Z.to_nat (NE - NB)) by (destruct SRC as [[[L _] _] _]; exact L).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SRB : bytes_at usegs mm NB src) by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B) end.
  replace (Z_to_bv 64 NE) with (Z_to_bv 64 (NB + (NE - NB))) by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_cut3 mm OB (Z.to_nat CAP) junk 0 (NE - NB) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) DST)
      as (e1 & e2 & e3 & DP1 & DP2 & DP3) end.
  replace (OB + 0)%Z with OB in DP2 by lia. replace (OB + 0)%Z with OB in DP3 by lia. clear DST.
  call_sp (widen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc NB OB (NE - NB)%Z src _);
    [lia | lia | lia | lia | lia | exact LEN | lia | assumption | exact SRB | exact DP2 |].
  rename POST into DP2. clear SRB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_join3 mm OB (Z.to_nat 0) (Z.to_nat (NE - NB)) (Z.to_nat CAP - Z.to_nat 0 - Z.to_nat (NE - NB)) (Z.to_nat CAP)
                e1 _ e3 OB (OB + (NE - NB))%Z DP1 DP2 DP3
                ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 DST] end.
  clear DP1 DP2 DP3.
  replace (NB + (NE - NB))%Z with NE by lia.
  do 2 lstep.
  lstep.
  lstep.
  destruct (Z.eq_dec NP NE) as [PE|PNE].
  - subst NP. bru false.
    lstep.
    do 2 lstep.
    lstep.
    lstep.
    if_true.
    do 15 lstep.
    release_frame FR ST (bv_unsigned sp).
    unfold wgi_post. sys_finish; [eassumption .. | do 15 eexists; exact LBC].
  - bru true.
    do 2 lstep.
    do 2 lstep.
    lstep.
    lstep.
    if_true.
    do 15 lstep.
    release_frame FR ST (bv_unsigned sp).
    unfold wgi_post. sys_finish; [eassumption .. | do 15 eexists; exact LBC].
Qed.
