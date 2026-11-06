(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_gates F_rip I_strtolfix M_sspdefs M_strtol.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition strtolq_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (E : Z) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (k : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 528, q); (E, E + 8); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ rw_cells asegs m' (bv_unsigned tp - 164) [C4 errv']
    /\ 0 <= k <= Z.of_nat (length str)
    /\ rw_cells asegs m' E [C8 (wz (S + k))].

Lemma strtox_callq : forall entry, strtox_stmt entry ->
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (E base : Z) (ejunk : list byte) (errv canary : word) (lo : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> rw_cells asegs m E [CB 8 ejunk] -> q <= E -> E + 8 < 2^63 ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  stk asegs m lo q -> mem_inv asegs m -> (base = 10 \/ base = 16) ->
  lo <= q - 528 -> 0x10007fff8000 <= lo -> q < 2^63 ->
  4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 160 <= 0x609000 ->
  (bv_unsigned tp - 160 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164) ->
  (bv_unsigned tp - 160 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164) ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo -> S + 2^41 <= 2^63 -> Z.of_nat (length str) + 1 <= 2^40 ->
  evt asegs (strtolq_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz E) (wz base) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom asegs)).
Proof.
  intros entry SP. intros until lo. intros STR EC QE E63 ERR GOT CAN ST MI HB LO KLO Q63 TP1 TP2 D1 D2 S1 S2 S3 LEN.
  assert (U : bv_unsigned (wz q) = q) by (apply unsigned_lit; destruct ST as (L0 & _); lia).
  unfold got_ssp, ssp_guard in *.
  eapply evt_mono.
  { eapply (SP ra (wz q) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S str E base ejunk errv canary lo);
      rewrite ?U; unfold STRTOL_DEPTH, got_ssp, ssp_guard; try eassumption; try lia.
    intros _. exact EC. }
  intros ms' P. unfold strtol_post, STRTOL_DEPTH in P. rewrite !U in P. unfold strtolq_post.
  destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & errv' & k & EQ & MU & WM & MI' & ST' & STR' & GOT' & CAN' & ERR' & HK & EC').
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m', errv', k.
  repeat (split; [assumption|]). apply EC'. destruct ST as (L0 & _). lia.
Qed.

Definition istrtol_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (E : Z) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (k : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (E, E + 8); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ rw_cells asegs m' (bv_unsigned tp - 164) [C4 errv']
    /\ 0 <= k <= Z.of_nat (length str)
    /\ rw_cells asegs m' E [C8 (wz (S + k))].

Lemma strtol_i_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (E base : Z) (ejunk : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m E [CB 8 ejunk] ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  icpt_env m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> cwin S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  accessible m E 8 -> sh_readable m E 8 -> cwin E 8 ->
  (base = 10 \/ base = 16) ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 48 - 2144 - 80 -> q < 2^63 ->
  bv_unsigned tp = 0x5e75b0 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo -> S + Z.of_nat (length str) + 1 < 2^47 ->
  0x609000 <= E -> E + 8 <= lo -> E + 8 < 2^47 -> E mod 8 = 0 ->
  (E + 8 <= S \/ S + Z.of_nat (length str) + 1 <= E) ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz E -> a2 = wz base ->
  evt asegs (istrtol_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strtol) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros STR EC ERR GOT CAN IE ACCS RDS WINS NSZ ACCE RDE WINE HB ST KLO LO Q63 TPV S1 S2 S3 E1 E2 E3 EAL SEPE MI -> -> ->.
  unfold A0_strtol. rewrite TPV in *. unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(lo, q); (E, E + 8); (6190348, 6190348 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 48) by lia.
  carve_frame 48%nat ST.
  zstep. do 9 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (SAFE : env_band_safe [(lo, q); (E, E + 8); (6190348, 6190348 + 4)]) by (repeat (constructor; [cbn; lia|]); constructor);
    pose proof (icpt_env_frame _ m m1 IE MU WM SAFE) as IE1 end.
  call ensure_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch _ m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_frame _ m m1 IE MU' WM' SAFE) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_aflags _ IE1) as AF1. pose proof (ie_real_lib _ IE1) as (_ & _ & _ & RL1).
  unfold env_cf in CF1. unfold env_aflags in AF1.
  do 5 zstep.
  zstep. lit_branch.
  do 3 zstep. fix_lit_store. do 4 zstep.
  apply (proj1 (rw_cells_app asegs _ (q + -48) [C8 (wz 12297829382473034410)] [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR. destruct FR as [FR0 FR].
  cbn [cells_size csize Nat.add Z.of_nat] in FR.
  destruct (rw_cells_C8_CB _ _ _ _ FR0) as [ej FRE]. clear FR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (strtox_callq strtol_entry strtol_proof) with (lo := lo) (S := S) (str := str) (E := q + -48) (base := base) (ejunk := ej) (canary := canary);
      rewrite ?TPV; unfold got_ssp, ssp_guard;
      first [ eassumption | lia | idtac ]
    | post_call asegs mm ] end.
  replace (q + -48 + Z.of_nat 8) with (q + -40) in FR by lia.
  match goal with H : 0 <= ?kk <= Z.of_nat (length str) |- _ => rename kk into k; rename H into HK end.
  do 8 zstep.
  clear IE1 CF1 AF1 RL1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch _ m mm, WM' : wmono asegs m mm |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q); (E, E + 8); (6190348, 6190348 + 4)] s)
      by (intros s Hs; destruct WINE as [_ WE]; cbn [outside]; lia);
    pose proof (icpt_env_frame _ m mm IE MU' WM' SAFE) as IE1;
    assert (ACS1 : accessible mm S (Z.of_nat (length str) + 1)) by (eapply accessible_munch; [exact ACCS| exact MU'| exact WINS| intros s Hs; apply HO; lia]);
    assert (RDS1 : sh_readable mm S (Z.of_nat (length str) + 1)) by (eapply sh_readable_munch; [exact RDS| exact MU'| exact WINS| exact HO]);
    assert (ACE1 : accessible mm E 8) by (eapply accessible_munch; [exact ACCE| exact MU'| exact WINE| intros s Hs; apply HO; lia]);
    assert (RDE1 : sh_readable mm E 8) by (eapply sh_readable_munch; [exact RDE| exact MU'| exact WINE| exact HO]);
    eapply evt_cut;
    [ eapply sfixE_spec with (lo := lo) (S := S) (str := str) (k := k) (base := base) (E := E) (ejunk := ejunk);
      first [ eassumption | reflexivity | lia | idtac ]
    | post_call asegs mm ] end end.
  do 8 zstep.
  match goal with H0 : rw_cells asegs ?mm (q + -48) [C8 ?v], H1 : rw_cells asegs ?mm (q + -40) ?cs |- _ =>
    assert (FRJ : rw_cells asegs mm (q + -48) ([C8 v] ++ cs))
      by (apply (proj2 (rw_cells_app asegs mm (q + -48) [C8 v] cs)); split; [exact H0|];
          replace (q + -48 + Z.of_nat (cells_size [C8 v])) with (q + -40) by (cbn; lia); exact H1);
    clear H0 H1 end.
  cbn [app] in FRJ.
  match goal with H : stk asegs _ lo (q + -48) |- _ => release_frame FRJ H q end.
  finish.
  - rewrite TPV. exact MU.
  - eassumption.
  - exact (proj1 HK).
  - exact (proj2 HK).
  - eassumption.
Qed.

Definition istrtol0_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ rw_cells asegs m' (bv_unsigned tp - 164) [C4 errv'].

Lemma strtol0_i_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (base : Z) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  icpt_env m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> cwin S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  (base = 10 \/ base = 16) ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 48 - 2144 - 80 -> q < 2^63 ->
  bv_unsigned tp = 0x5e75b0 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo -> S + Z.of_nat (length str) + 1 < 2^47 ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz 0 -> a2 = wz base ->
  evt asegs (istrtol0_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strtol) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros STR ERR GOT CAN IE ACCS RDS WINS NSZ HB ST KLO LO Q63 TPV S1 S2 S3 MI -> -> ->.
  unfold A0_strtol. rewrite TPV in *. unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(lo, q); (6190348, 6190348 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 48) by lia.
  carve_frame 48%nat ST.
  zstep. do 9 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (SAFE : env_band_safe [(lo, q); (6190348, 6190348 + 4)]) by (repeat (constructor; [cbn; lia|]); constructor);
    pose proof (icpt_env_frame _ m m1 IE MU WM SAFE) as IE1 end.
  call ensure_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch _ m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_frame _ m m1 IE MU' WM' SAFE) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_aflags _ IE1) as AF1. pose proof (ie_real_lib _ IE1) as (_ & _ & _ & RL1).
  unfold env_cf in CF1. unfold env_aflags in AF1.
  do 5 zstep.
  zstep. lit_branch.
  do 3 zstep. fix_lit_store. do 4 zstep.
  apply (proj1 (rw_cells_app asegs _ (q + -48) [C8 (wz 12297829382473034410)] [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR. destruct FR as [FR0 FR].
  cbn [cells_size csize Nat.add Z.of_nat] in FR.
  destruct (rw_cells_C8_CB _ _ _ _ FR0) as [ej FRE]. clear FR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (strtox_callq strtol_entry strtol_proof) with (lo := lo) (S := S) (str := str) (E := q + -48) (base := base) (ejunk := ej) (canary := canary);
      rewrite ?TPV; unfold got_ssp, ssp_guard;
      first [ eassumption | lia | idtac ]
    | post_call asegs mm ] end.
  replace (q + -48 + Z.of_nat 8) with (q + -40) in FR by lia.
  match goal with H : 0 <= ?kk <= Z.of_nat (length str) |- _ => rename kk into k; rename H into HK end.
  do 8 zstep.
  clear IE1 CF1 AF1 RL1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch _ m mm, WM' : wmono asegs m mm |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q); (6190348, 6190348 + 4)] s)
      by (intros s Hs; cbn [outside]; lia);
    pose proof (icpt_env_frame _ m mm IE MU' WM' SAFE) as IE1;
    assert (ACS1 : accessible mm S (Z.of_nat (length str) + 1)) by (eapply accessible_munch; [exact ACCS| exact MU'| exact WINS| intros s Hs; apply HO; lia]);
    assert (RDS1 : sh_readable mm S (Z.of_nat (length str) + 1)) by (eapply sh_readable_munch; [exact RDS| exact MU'| exact WINS| exact HO]);
    eapply evt_cut;
    [ eapply sfix0_spec with (lo := lo) (S := S) (str := str) (k := k) (base := base);
      first [ eassumption | reflexivity | lia | idtac ]
    | post_call asegs mm ] end end.
  do 8 zstep.
  match goal with H0 : rw_cells asegs ?mm (q + -48) [C8 ?v], H1 : rw_cells asegs ?mm (q + -40) ?cs |- _ =>
    assert (FRJ : rw_cells asegs mm (q + -48) ([C8 v] ++ cs))
      by (apply (proj2 (rw_cells_app asegs mm (q + -48) [C8 v] cs)); split; [exact H0|];
          replace (q + -48 + Z.of_nat (cells_size [C8 v])) with (q + -40) by (cbn; lia); exact H1);
    clear H0 H1 end.
  cbn [app] in FRJ.
  match goal with H : stk asegs _ lo (q + -48) |- _ => release_frame FRJ H q end.
  finish.
  - rewrite TPV. exact MU.
  - eassumption.
Qed.
