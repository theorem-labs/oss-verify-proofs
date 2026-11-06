(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_memset. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison_g.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 FsKit ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AHNR : Z := 0x65de8.

Lemma platform_unpoison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> ATOP <= lo ->
  rw_cells asegs m 0xd1558 [C8 (Z_to_bv 64 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x609f8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO CEIL SEAL RIMG RSTK.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 3 zstep.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [| exfalso; clear - K; lia].
  zstep.
  do 4 zstep.
  release_frame FR0 ST (bv_unsigned sp). finish.
Qed.

Lemma hnr_land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. reflexivity. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma hnr_round8 : forall s, 0 <= s <= 0x4000000 -> s mod 8 = 0 -> Z.land (s + 7) 268435448 = s.
Proof.
  intros s Hs M. replace 268435448 with (Z.ldiff (Z.ones 28) (Z.ones 3)) by reflexivity.
  assert (E : Z.land (s + 7) (Z.ldiff (Z.ones 28) (Z.ones 3)) = Z.ldiff (Z.land (s + 7) (Z.ones 28)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit (s + 7) i), (Z.testbit (Z.ones 28) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite E, Z.land_ones by lia. rewrite (Z.mod_small (s + 7)) by (change (2^28) with 268435456; lia).
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

Definition hnr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bottom size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp); (shad bottom, shad bottom + shlen size); (fs + 96, fs + 97)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad bottom) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen size)))]
    /\ rw_cells asegs m' (fs + 96) [C1 (Z_to_bv 8 1)].

Lemma handle_no_return_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs bottom size : Z) (g : byte) (junk : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m -> rw_cells asegs m 0xd1558 [C8 (Z_to_bv 64 1)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (t + 72) [C8 (Z_to_bv 64 fs)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  poison_cells m ->
  0 < ctx -> ctx + 4096 <= ATOP -> sclr ctx 4096 -> 0 < t -> t + 4096 <= ATOP -> sclr t 4096 ->
  0 <= bot -> bot < top -> top <= 2^47 -> top mod 8 = 0 ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> rw_cells asegs m (fs + 96) [C1 g] ->

  bottom = (bv_unsigned sp - 4160) / 4096 * 4096 -> size = top - bottom -> 0 < size <= 0x4000000 ->
  rw_cells asegs m (shad bottom) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG fs 11571200 ->
  rng RNG (shad bottom) (shlen size) ->
  evtF asegs RNG (hnr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs bottom size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AHNR) fc None m (seg_rom asegs)).
Proof.
  intros until junk.
  intros MI ST LO CEIL TP INI SEAL TI TK T88 TSD CT TB SW FSP GPG PGS PC CXa CXb CXs T0 T1 Ts B0 BT TT TAL
         FLO FHI NGC BOTTOM SIZE SZR DST RIMG RSTK RCTX RT RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (shad bottom, shad bottom + shlen size); (fs + 96, fs + 97)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold ATP, ATSDI, ATSDK, ATP88, ATSD, AHNR, GOT_PGSZ, APGSZ in *.
  word_range sp SPR. pose proof atop_range as ATR.
  assert (BAL : bottom mod 4096 = 0) by (rewrite BOTTOM; apply Z.mod_mul; lia).
  assert (BLO : bv_unsigned sp - 4160 - 4096 < bottom <= bv_unsigned sp - 4160) by (rewrite BOTTOM; clear - SPR LO CEIL LO0 ATR; Z.div_mod_to_equations; lia).
  assert (SM8 : size mod 8 = 0) by (rewrite SIZE; clear - TAL BAL; Z.div_mod_to_equations; lia).
  assert (SHR : 0x8fff7000 <= shad bottom /\ shad bottom + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - BLO SIZE SZR SM8 TT LO CEIL LO0 ATR SPR BAL. Z.div_mod_to_equations. lia. }
  carve_frame 80%nat ST.
  do 6 zstep.
  zstep. zstep.
  lstep. zstep. zstep.
  step. if_lit.
  zstep.
  call_sp platform_unpoison_spec; first [ exact MI | exact ST | exact SEAL | exact RIMG | lia | solve_rng | idtac ].
  rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka; lia|].
  zstep. zstep.
  zstep. zstep.
  zstep.
  box RCTX; box RT.
  call_sp get_current_thread_spec;
    first [ exact MI2 | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT.
  rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI3 end.
  zstep. if_cases Kb; zify_cond Kb; [exfalso; clear - Kb T0 T1; pose proof atop_range; lia|].
  zstep. zstep.
  zstep.
  zstep. if_cases Kc; zify_cond Kc; [| exfalso; clear - Kc; lia].
  zstep.
  callp stack_top_spec; [exact MI3 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. zstep.
  zstep. zstep. zstep. zstep.
  replace (Z.land (bv_unsigned sp + -64 - 4096) 18446744073709547520) with bottom
    by (rewrite hnr_land_align4096 by lia; rewrite BOTTOM; f_equal; f_equal; lia).
  zstep.
  zstep.
  zstep. zstep.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd SIZE SZR; rewrite ?Z.mod_small in Kd by lia; lia].
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  replace (Z.land (top - bottom + 7) 268435448) with size by (rewrite <- SIZE; symmetry; apply hnr_round8; [lia| exact SM8]).
  zstep.
  lazymatch goal with MUx : munch ?W m ?mm |- _ =>
    assert (PC1 : poison_cells mm)
      by (eapply poison_cells_frame; [exact PC| exact MUx| exact WM|];
          repeat (apply Forall_cons; [cbn; unfold AIMG_HI; lia|]); apply Forall_nil)
  end.
  pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof CXs as CXB. pose proof Ts as TsB. unfold sclr, KLS in CXB, TsB.
  box RCTX; box RT; box RFS.
  call_sp (poison_shadow_spec_g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc _ bottom size 0 lo junk);
    first [ exact MI3 | exact ST | exact PC1 | reflexivity | exact DST | exact RIMG | exact RSH
          | (right; split; lia) | (intros _; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia)
          | (clear - BAL; Z.div_mod_to_equations; lia) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RFS.
  rename PC0 into ST. rename POST into ZSH. rename MI into MI4.
  zstep.
  box RCTX; box RT; box RFS.
  call_sp get_current_thread_spec;
    first [ exact MI4 | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RFS.
  rename POST into ST.
  zstep. if_cases Ke; zify_cond Ke; [exfalso; clear - Ke T0 T1 ATR; lia|].
  lstep.
  step. if_lit.
  zstep.
  zstep. zstep. zstep.
  replace (fs <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change ((0 + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  zstep. if_cases Kf; zify_cond Kf; [exfalso; clear - Kf FLOL FB; lia|].
  zstep.
  zstep.
  zstep.
  zstep.
  do 5 zstep.
  zstep. zstep.
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -80) _ |- _ => rename H into FRx end.
  release_frame FRx ST (bv_unsigned sp).
  apply evtF_done. unfold hnr_post. do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact ZSH| exact NGC].
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import RtCells.TwinB AProto.TwinB ABase.TwinB F_tryinit.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind. Import F_memset.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison_g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB FsKit.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AHNR : Z := 0x66778.

Lemma platform_unpoison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> ATOP <= lo ->
  rw_cells bsegs m 0xd3670 [C8 (Z_to_bv 64 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x61388) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST LO CEIL SEAL RIMG RSTK.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 3 zstep.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [| exfalso; clear - K; lia].
  zstep.
  do 4 zstep.
  release_frame FR0 ST (bv_unsigned sp). finish.
Qed.

Lemma hnr_land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. reflexivity. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma hnr_round8 : forall s, 0 <= s <= 0x4000000 -> s mod 8 = 0 -> Z.land (s + 7) 268435448 = s.
Proof.
  intros s Hs M. replace 268435448 with (Z.ldiff (Z.ones 28) (Z.ones 3)) by reflexivity.
  assert (E : Z.land (s + 7) (Z.ldiff (Z.ones 28) (Z.ones 3)) = Z.ldiff (Z.land (s + 7) (Z.ones 28)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit (s + 7) i), (Z.testbit (Z.ones 28) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite E, Z.land_ones by lia. rewrite (Z.mod_small (s + 7)) by (change (2^28) with 268435456; lia).
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

Definition hnr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bottom size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp); (shad bottom, shad bottom + shlen size); (fs + 96, fs + 97)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad bottom) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen size)))]
    /\ rw_cells bsegs m' (fs + 96) [C1 (Z_to_bv 8 1)].

Lemma handle_no_return_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs bottom size : Z) (g : byte) (junk : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m -> rw_cells bsegs m 0xd3670 [C8 (Z_to_bv 64 1)] ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (t + 72) [C8 (Z_to_bv 64 fs)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  poison_cells m ->
  0 < ctx -> ctx + 4096 <= ATOP -> sclr ctx 4096 -> 0 < t -> t + 4096 <= ATOP -> sclr t 4096 ->
  0 <= bot -> bot < top -> top <= 2^47 -> top mod 8 = 0 ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> rw_cells bsegs m (fs + 96) [C1 g] ->

  bottom = (bv_unsigned sp - 4160) / 4096 * 4096 -> size = top - bottom -> 0 < size <= 0x4000000 ->
  rw_cells bsegs m (shad bottom) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG fs 11571200 ->
  rng RNG (shad bottom) (shlen size) ->
  evtF bsegs RNG (hnr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs bottom size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AHNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk.
  intros MI ST LO CEIL TP INI SEAL TI TK T88 TSD CT TB SW FSP GPG PGS PC CXa CXb CXs T0 T1 Ts B0 BT TT TAL
         FLO FHI NGC BOTTOM SIZE SZR DST RIMG RSTK RCTX RT RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (shad bottom, shad bottom + shlen size); (fs + 96, fs + 97)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold ATP, ATSDI, ATSDK, ATP88, ATSD, AHNR, GOT_PGSZ, APGSZ in *.
  word_range sp SPR. pose proof atop_range as ATR.
  assert (BAL : bottom mod 4096 = 0) by (rewrite BOTTOM; apply Z.mod_mul; lia).
  assert (BLO : bv_unsigned sp - 4160 - 4096 < bottom <= bv_unsigned sp - 4160) by (rewrite BOTTOM; clear - SPR LO CEIL LO0 ATR; Z.div_mod_to_equations; lia).
  assert (SM8 : size mod 8 = 0) by (rewrite SIZE; clear - TAL BAL; Z.div_mod_to_equations; lia).
  assert (SHR : 0x8fff7000 <= shad bottom /\ shad bottom + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - BLO SIZE SZR SM8 TT LO CEIL LO0 ATR SPR BAL. Z.div_mod_to_equations. lia. }
  carve_frame 80%nat ST.
  do 6 zstep.
  zstep. zstep.
  lstep. zstep. zstep.
  step. if_lit.
  zstep.
  call_sp platform_unpoison_spec; first [ exact MI | exact ST | exact SEAL | exact RIMG | lia | solve_rng | idtac ].
  rename POST into ST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka; lia|].
  zstep. zstep.
  zstep. zstep.
  zstep.
  box RCTX; box RT.
  call_sp get_current_thread_spec;
    first [ exact MI2 | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT.
  rename POST into ST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI3 end.
  zstep. if_cases Kb; zify_cond Kb; [exfalso; clear - Kb T0 T1; pose proof atop_range; lia|].
  zstep. zstep.
  zstep.
  zstep. if_cases Kc; zify_cond Kc; [| exfalso; clear - Kc; lia].
  zstep.
  callp stack_top_spec; [exact MI3 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. zstep.
  zstep. zstep. zstep. zstep.
  replace (Z.land (bv_unsigned sp + -64 - 4096) 18446744073709547520) with bottom
    by (rewrite hnr_land_align4096 by lia; rewrite BOTTOM; f_equal; f_equal; lia).
  zstep.
  zstep.
  zstep. zstep.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd SIZE SZR; rewrite ?Z.mod_small in Kd by lia; lia].
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  replace (Z.land (top - bottom + 7) 268435448) with size by (rewrite <- SIZE; symmetry; apply hnr_round8; [lia| exact SM8]).
  zstep.
  lazymatch goal with MUx : munch ?W m ?mm |- _ =>
    assert (PC1 : poison_cells mm)
      by (eapply poison_cells_frame; [exact PC| exact MUx| exact WM|];
          repeat (apply Forall_cons; [cbn; unfold AIMG_HI; lia|]); apply Forall_nil)
  end.
  pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof CXs as CXB. pose proof Ts as TsB. unfold sclr, KLS in CXB, TsB.
  box RCTX; box RT; box RFS.
  call_sp (poison_shadow_spec_g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc _ bottom size 0 lo junk);
    first [ exact MI3 | exact ST | exact PC1 | reflexivity | exact DST | exact RIMG | exact RSH
          | (right; split; lia) | (intros _; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia)
          | (clear - BAL; Z.div_mod_to_equations; lia) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RFS.
  rename PC0 into ST. rename POST into ZSH. rename MI into MI4.
  zstep.
  box RCTX; box RT; box RFS.
  call_sp get_current_thread_spec;
    first [ exact MI4 | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RFS.
  rename POST into ST.
  zstep. if_cases Ke; zify_cond Ke; [exfalso; clear - Ke T0 T1 ATR; lia|].
  lstep.
  step. if_lit.
  zstep.
  zstep. zstep. zstep.
  replace (fs <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change ((0 + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  zstep. if_cases Kf; zify_cond Kf; [exfalso; clear - Kf FLOL FB; lia|].
  zstep.
  zstep.
  zstep.
  zstep.
  do 5 zstep.
  zstep. zstep.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -80) _ |- _ => rename H into FRx end.
  release_frame FRx ST (bv_unsigned sp).
  apply evtF_done. unfold hnr_post. do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact ZSH| exact NGC].
Qed.
End CANSEC1.
End TwinB.
