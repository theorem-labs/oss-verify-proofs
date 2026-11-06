(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg RtCells AProto ABase F_tryinit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_m2s_b.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit FsKit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module AFake_sm0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC0 : Z := 0x48310.

Definition sm0_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (shad F, shad F + 8)].

Definition sm0_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h1 h2 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm0_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 (Z_to_bv 64 (h + 1)); C8 h1; C8 h2; CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)].

Lemma stack_malloc0_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 56) [C8 j56] ->
  rw_cells asegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. rewrite <- POS.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 4096 + pos)] => replace (fs + 4096 + pos) with flag by lia end.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm0.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit2.
Module AFake_sm1g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm1_flag (fs p : Z) : Z := fs + 20480 + Z.land p 8191.

Lemma sm1_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv asegs m ->
  0 <= i -> i + Z.of_nat j < 8192 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm1_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells asegs m (sm1_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (8192 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 (fs + 20480))
                    (Z_to_bv 64 8191) (Z_to_bv 64 (sm1_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (h + 8192)) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 8191))
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48590) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (8192 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 (fs + 20480))
             (Z_to_bv 64 8191) a5 (Z_to_bv 64 (h + 8192)) a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48518) fc None m (seg_rom asegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm1_flag in FREE |- *.
    remember (Z.land (h + i) 8191) as pos eqn:POS.
    assert (PB : 0 <= pos < 8192) by (subst pos; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 20480 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 8191 with (Z.ones 13) at 1. rewrite ?(land_wrap64 _ 13) by lia. change (Z.ones 13) with 8191. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm1_flag in CB.
    replace (8192 - i - Z.of_nat (S j)) with (8192 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 8191) as pos eqn:POS.
    assert (PB : 0 <= pos < 8192) by (subst pos; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 20480 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 8191 with (Z.ones 13) at 1. rewrite ?(land_wrap64 _ 13) by lia. change (Z.ones 13) with 8191. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (8192 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Definition ASTKMALLOC1 : Z := 0x48484.

Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1g_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 h0; C8 (Z_to_bv 64 hv); C8 h1; CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc1_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j248 sh0 sh1 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 8192 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm1_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 120) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm1g_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 8191 < 8192) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm1_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm1_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm1_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.

End CANSEC1.
End AFake_sm1g.

Module AFake_sm2.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC2 : Z := 0x48614.

Definition sm2_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (shad F, shad F + 32)].

Definition sm2_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm2_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 (h + 1)); CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc2_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 248) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm2_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm2_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.
  zstep. rewrite <- POS.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 28672 + pos)] => replace (fs + 28672 + pos) with flag by lia end.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm2.

Module AFake_sm0g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import AFake_sm0.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm0_flag (fs p : Z) : Z := fs + 4096 + Z.land p 16383.

Lemma sm0_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv asegs m ->
  0 <= i -> i + Z.of_nat j < 16384 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm0_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells asegs m (sm0_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (16384 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 16383)
                    a4 (Z_to_bv 64 (sm0_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 16383)) (Z_to_bv 64 0)
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x4840c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (16384 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 16383)
             a4 a5 a6 a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48394) fc None m (seg_rom asegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm0_flag in FREE |- *.
    remember (Z.land (h + i) 16383) as pos eqn:POS.
    assert (PB : 0 <= pos < 16384) by (subst pos; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 4096 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 16383 with (Z.ones 14) at 1. rewrite ?(land_wrap64 _ 14) by lia. change (Z.ones 14) with 16383. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm0_flag in CB.
    replace (16384 - i - Z.of_nat (S j)) with (16384 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 16383) as pos eqn:POS.
    assert (PB : 0 <= pos < 16384) by (subst pos; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 4096 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 16383 with (Z.ones 14) at 1. rewrite ?(land_wrap64 _ 14) by lia. change (Z.ones 14) with 16383. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (16384 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Lemma stack_malloc0_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 16384 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm0_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 56) [C8 j56] ->
  rw_cells asegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j) flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 16383 < 16384) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm0_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm0_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm0_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm0g.

Module AFake_sm2g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm2_flag (fs p : Z) : Z := fs + 28672 + Z.land p 4095.

Lemma sm2_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv asegs m ->
  0 <= i -> i + Z.of_nat j < 4096 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm2_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells asegs m (sm2_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (4096 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 (fs + 28672))
                    (Z_to_bv 64 4095) (Z_to_bv 64 (sm2_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (h + 4096)) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 4095))
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48720) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (4096 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 (fs + 28672))
             (Z_to_bv 64 4095) a5 (Z_to_bv 64 (h + 4096)) a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x486a8) fc None m (seg_rom asegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm2_flag in FREE |- *.
    remember (Z.land (h + i) 4095) as pos eqn:POS.
    assert (PB : 0 <= pos < 4096) by (subst pos; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 28672 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 4095 with (Z.ones 12) at 1. rewrite ?(land_wrap64 _ 12) by lia. change (Z.ones 12) with 4095. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm2_flag in CB.
    replace (4096 - i - Z.of_nat (S j)) with (4096 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 4095) as pos eqn:POS.
    assert (PB : 0 <= pos < 4096) by (subst pos; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 28672 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 4095 with (Z.ones 12) at 1. rewrite ?(land_wrap64 _ 12) by lia. change (Z.ones 12) with 4095. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (4096 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Definition sm2g_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm2_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 hv); CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc2_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 4096 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs m (sm2_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 248) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm2g_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm2_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 4095 < 4096) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm2_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm2_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm2_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm2g.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ABytes AFake_gc AFake_gcl AFake_gcf.
Module AFake_sm2gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import AFake_sm2. Import AFake_sm2g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition gfl' (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) (c p : Z) : byte :=
  if gfreed bot cur (fl c p) (rs c p) then Z_to_bv 8 0 else fl c p.

Lemma c8x4_of_dc : forall m A, dc_at m A 32 -> exists w0 w1 w2 w3 : word, rw_cells asegs m A [C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
  intros m A D. destruct (dc_split m A 16 16 D ltac:(lia) ltac:(lia)) as [D1 D2].
  destruct (c8c8_of_dc m A D1) as (w0 & w1 & H1). destruct (c8c8_of_dc m (A + 16) D2) as (w2 & w3 & H2).
  exists w0, w1, w2, w3. apply (proj2 (rw_cells_app asegs m A [C8 w0; C8 w1] [C8 w2; C8 w3])). split; [exact H1| exact H2].
Qed.

Definition sm2gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs + 16, fs + 24) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 248, F + 256)
  :: (shad F, shad F + 32) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm2gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm2gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 hv); CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (2, (flag - (fs + 28672))) ->
          rw_cells asegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc2_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells asegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells asegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 4096 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 2 (Z.land (h + t) 4095)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  gfl' fl rs bot (bv_unsigned sp) 2 pos = Z_to_bv 8 0 ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 248) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm2gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm2gc_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 4095 < 4096) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 296536)) with (Z_to_bv 64 296536) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x62f000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells asegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells asegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono asegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 2134016 <= F /\ F + 256 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 248) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8x4_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & q1 & q2 & q3 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs + 16, fs + 24) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 248, F + 256) :: (shad F, shad F + 32) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256);
                          (shad F, shad F + 32)]%Z mg) as MUq.
  pose proof (wmono_refl asegs mg) as WMq.
  assert (GF2 : forall p, gflag fs 2 p = fs + 28672 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 2)) with 8192; lia).
  assert (GN2 : gcN 2 = 4096) by reflexivity.
  assert (FL0g : rw_cells asegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 2 pos ltac:(lia) ltac:(rewrite GN2; lia)) as X. rewrite GF2 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm2_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 2 (Z.land (h + tq) 4095)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm2_flag.
    pose proof (FLSg 2 (Z.land (h + tq) 4095) ltac:(lia) ltac:(rewrite GN2; lia)) as X. rewrite GF2 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm2_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB ATR. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm2gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm2gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 2 pos c p ltac:(lia) ltac:(rewrite GN2; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF2 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm2gc.

Module AFake_sm1gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import AFake_sm1g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf. Import AFake_sm2gc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition sm1gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs + 8, fs + 16) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 120, F + 128)
  :: (shad F, shad F + 16) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm1gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm1gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' fs [C8 h0; C8 (Z_to_bv 64 hv); C8 h1; CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (1, (flag - (fs + 20480))) ->
          rw_cells asegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc1_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 sh1 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells asegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells asegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 8192 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 1 (Z.land (h + t) 8191)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  gfl' fl rs bot (bv_unsigned sp) 1 pos = Z_to_bv 8 0 ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 120) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm1gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm1gc_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 8191 < 8192) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 296136)) with (Z_to_bv 64 296136) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x62f000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells asegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells asegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono asegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 1085440 <= F /\ F + 128 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 120) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8c8_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & q1 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs + 8, fs + 16) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 120, F + 128) :: (shad F, shad F + 16) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128);
                          (shad F, shad F + 16)]%Z mg) as MUq.
  pose proof (wmono_refl asegs mg) as WMq.
  assert (GF1 : forall p, gflag fs 1 p = fs + 20480 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 1)) with 16384; lia).
  assert (GN1 : gcN 1 = 8192) by reflexivity.
  assert (FL0g : rw_cells asegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 1 pos ltac:(lia) ltac:(rewrite GN1; lia)) as X. rewrite GF1 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm1_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 1 (Z.land (h + tq) 8191)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm1_flag.
    pose proof (FLSg 1 (Z.land (h + tq) 8191) ltac:(lia) ltac:(rewrite GN1; lia)) as X. rewrite GF1 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm1_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm1gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm1gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 1 pos c p ltac:(lia) ltac:(rewrite GN1; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF1 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm1gc.

Module AFake_sm0gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import AFake_sm0. Import AFake_sm0g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf. Import AFake_sm2gc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition sm0gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs, fs + 8) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 56, F + 64)
  :: (shad F, shad F + 8) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm0gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm0gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' fs [C8 (Z_to_bv 64 hv); C8 h0; C8 h1; CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (0, (flag - (fs + 4096))) ->
          rw_cells asegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc0_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 h0 h1 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 (Z_to_bv 64 h); C8 h0; C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells asegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells asegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 16384 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 0 (Z.land (h + t) 16383)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  gfl' fl rs bot (bv_unsigned sp) 0 pos = Z_to_bv 8 0 ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 56) [C8 j248] ->
  rw_cells asegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm0gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm0gc_W in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 16383 < 16384) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 295764)) with (Z_to_bv 64 295764) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x62f000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells asegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells asegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono asegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 36864 <= F /\ F + 64 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 56) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs, fs + 8) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 56, F + 64) :: (shad F, shad F + 8) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64);
                          (shad F, shad F + 8)]%Z mg) as MUq.
  pose proof (wmono_refl asegs mg) as WMq.
  assert (GF0 : forall p, gflag fs 0 p = fs + 4096 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 0)) with 32768; lia).
  assert (GN0 : gcN 0 = 16384) by reflexivity.
  assert (FL0g : rw_cells asegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 0 pos ltac:(lia) ltac:(rewrite GN0; lia)) as X. rewrite GF0 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells asegs mm (sm0_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 0 (Z.land (h + tq) 16383)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm0_flag.
    pose proof (FLSg 0 (Z.land (h + tq) 16383) ltac:(lia) ltac:(rewrite GN0; lia)) as X. rewrite GF0 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm0_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm0gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm0gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 0 pos c p ltac:(lia) ltac:(rewrite GN0; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF0 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm0gc.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module AFake_sm0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC0 : Z := 0x48ca0.

Definition sm0_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (shad F, shad F + 8)].

Definition sm0_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h1 h2 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm0_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 (Z_to_bv 64 (h + 1)); C8 h1; C8 h2; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)].

Lemma stack_malloc0_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 56) [C8 j56] ->
  rw_cells bsegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. rewrite <- POS.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 4096 + pos)] => replace (fs + 4096 + pos) with flag by lia end.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm0.

Module AFake_sm1g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm1_flag (fs p : Z) : Z := fs + 20480 + Z.land p 8191.

Lemma sm1_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv bsegs m ->
  0 <= i -> i + Z.of_nat j < 8192 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm1_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells bsegs m (sm1_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (8192 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 (fs + 20480))
                    (Z_to_bv 64 8191) (Z_to_bv 64 (sm1_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (h + 8192)) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 8191))
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48f20) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (8192 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 (fs + 20480))
             (Z_to_bv 64 8191) a5 (Z_to_bv 64 (h + 8192)) a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48ea8) fc None m (seg_rom bsegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm1_flag in FREE |- *.
    remember (Z.land (h + i) 8191) as pos eqn:POS.
    assert (PB : 0 <= pos < 8192) by (subst pos; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 20480 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 8191 with (Z.ones 13) at 1. rewrite ?(land_wrap64 _ 13) by lia. change (Z.ones 13) with 8191. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm1_flag in CB.
    replace (8192 - i - Z.of_nat (S j)) with (8192 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 8191) as pos eqn:POS.
    assert (PB : 0 <= pos < 8192) by (subst pos; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 20480 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 8191 with (Z.ones 13) at 1. rewrite ?(land_wrap64 _ 13) by lia. change (Z.ones 13) with 8191. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (8192 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Definition ASTKMALLOC1 : Z := 0x48e14.

Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1g_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 h0; C8 (Z_to_bv 64 hv); C8 h1; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc1_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j248 sh0 sh1 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 8192 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm1_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 120) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm1g_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 8191 < 8192) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm1_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm1_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm1_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.

End CANSEC1.
End AFake_sm1g.

Module AFake_sm2.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC2 : Z := 0x48fa4.

Definition sm2_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (shad F, shad F + 32)].

Definition sm2_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm2_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 (h + 1)); CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc2_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 248) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm2_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm2_W in MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.
  zstep. rewrite <- POS.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 28672 + pos)] => replace (fs + 28672 + pos) with flag by lia end.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm2.

Module AFake_sm0g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import AFake_sm0.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm0_flag (fs p : Z) : Z := fs + 4096 + Z.land p 16383.

Lemma sm0_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv bsegs m ->
  0 <= i -> i + Z.of_nat j < 16384 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm0_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells bsegs m (sm0_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (16384 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 16383)
                    a4 (Z_to_bv 64 (sm0_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 16383)) (Z_to_bv 64 0)
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48d9c) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (16384 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 16383)
             a4 a5 a6 a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x48d24) fc None m (seg_rom bsegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm0_flag in FREE |- *.
    remember (Z.land (h + i) 16383) as pos eqn:POS.
    assert (PB : 0 <= pos < 16384) by (subst pos; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 4096 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 16383 with (Z.ones 14) at 1. rewrite ?(land_wrap64 _ 14) by lia. change (Z.ones 14) with 16383. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm0_flag in CB.
    replace (16384 - i - Z.of_nat (S j)) with (16384 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 16383) as pos eqn:POS.
    assert (PB : 0 <= pos < 16384) by (subst pos; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 4096 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 16383 with (Z.ones 14) at 1. rewrite ?(land_wrap64 _ 14) by lia. change (Z.ones 14) with 16383. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (16384 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Lemma stack_malloc0_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 16384 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm0_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 56) [C8 j56] ->
  rw_cells bsegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j) flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 16383 < 16384) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm0_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm0_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm0_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm0g.

Module AFake_sm2g.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Lemma land_wrap64 : forall x k, 0 <= k <= 64 -> Z.land (x mod 18446744073709551616) (Z.ones k) = Z.land x (Z.ones k).
Proof.
  intros x k Hk. rewrite !Z.land_ones by lia. change 18446744073709551616 with (2^64).
  symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ztobv_wrap_add : forall x d, Z_to_bv 64 (x mod 18446744073709551616 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Definition sm2_flag (fs p : Z) : Z := fs + 28672 + Z.land p 4095.

Lemma sm2_probe_loop : forall RNG (j : nat) (i : Z)
    ra sp gp tp t0 t1 t2 s0 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (fs h : Z),
  mem_inv bsegs m ->
  0 <= i -> i + Z.of_nat j < 4096 -> 0 <= h -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm2_flag fs (h + i + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  rw_cells bsegs m (sm2_flag fs (h + i + Z.of_nat j)) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 (Z_to_bv 64 fs)
                    (Z_to_bv 64 (4096 - i - Z.of_nat j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i + Z.of_nat j)) (Z_to_bv 64 (fs + 28672))
                    (Z_to_bv 64 4095) (Z_to_bv 64 (sm2_flag fs (h + i + Z.of_nat j))) (Z_to_bv 64 (h + 4096)) (Z_to_bv 64 (Z.land (h + i + Z.of_nat j) 4095))
                    (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x490b0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 fs)
             (Z_to_bv 64 (4096 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 (fs + 28672))
             (Z_to_bv 64 4095) a5 (Z_to_bv 64 (h + 4096)) a7
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 0x49038) fc None m (seg_rom bsegs)).
Proof.
  intros RNG j. induction j as [|j IH]; intros until h; intros MI I0 IJ H0 F0 FB BUSY FREE RFS.
  -
    cbn [Z.of_nat] in FREE |- *. rewrite Z.add_0_r in FREE |- *. rewrite Z.sub_0_r. unfold sm2_flag in FREE |- *.
    remember (Z.land (h + i) 4095) as pos eqn:POS.
    assert (PB : 0 <= pos < 4096) by (subst pos; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 28672 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 4095 with (Z.ones 12) at 1. rewrite ?(land_wrap64 _ 12) by lia. change (Z.ones 12) with 4095. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep; rewrite zxb_lit by lia.
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
    apply evtF_done. reflexivity.
  -
    destruct (BUSY 0 ltac:(lia)) as (b & CB & NZ). rewrite Z.add_0_r in CB. unfold sm2_flag in CB.
    replace (4096 - i - Z.of_nat (S j)) with (4096 - (i + 1) - Z.of_nat j) by lia.
    replace (h + i + Z.of_nat (S j)) with (h + (i + 1) + Z.of_nat j) by lia.
    remember (Z.land (h + i) 4095) as pos eqn:POS.
    assert (PB : 0 <= pos < 4096) by (subst pos; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    remember (fs + 28672 + pos) as flag eqn:FLAG.
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG PB; lia).
    zstep. change 4095 with (Z.ones 12) at 1. rewrite ?(land_wrap64 _ 12) by lia. change (Z.ones 12) with 4095. rewrite <- POS.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep.
    setreg 10 (Z_to_bv 64 (4096 - (i + 1))) ltac:(f_equal; rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); lia).
    setreg 12 (Z_to_bv 64 (h + (i + 1))) ltac:(first [f_equal; lia | rewrite <- (ztobv_wrap_add (h + i) 1); f_equal; lia | rewrite ztobv_wrap_add; f_equal; lia]).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by lia; lia].
    eapply IH; try eassumption; try lia.
    all: lazymatch goal with
         | |- forall t, _ => intros t Ht; destruct (BUSY (t + 1) ltac:(lia)) as (b' & CB' & NZ'); exists b'; split; [|exact NZ'];
                             replace (h + (i + 1) + t) with (h + i + (t + 1)) by lia; exact CB'
         | |- rw_cells _ _ _ _ => replace (h + (i + 1) + Z.of_nat j) with (h + i + Z.of_nat (S j)) by lia; exact FREE
         | |- ?G => idtac "REMAINING" G
         end.
Qed.

Definition sm2g_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm2_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 hv); CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc2_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j : nat) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->

  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->

  Z.of_nat j < 4096 ->
  (forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs m (sm2_flag fs (h + t)) [C1 b] /\ bv_unsigned b <> 0) ->
  pos = Z.land (h + Z.of_nat j) 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 248) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm2g_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm2_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 4095 < 4096) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep; rewrite zxb_lit by lia.
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm2_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. destruct (BUSY tq Ht) as (bq & CB & NZ). exists bq. split; [|exact NZ]. replace (h + 0 + tq) with (h + tq) by lia.
    pose proof (LB (h + tq)) as LBt. unfold sm2_flag in CB |- *.
    xport CB MUs WM ltac:(clear - LBt FHI CEIL LO LO0; lia). exact CB. }
  eapply evtF_cut.
  { eapply (sm2_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG. exact FL0. }
  cbv beta. intros ms' ->. clear MUs BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End AFake_sm2g.

Module AFake_sm2gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import AFake_sm2. Import AFake_sm2g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition gfl' (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) (c p : Z) : byte :=
  if gfreed bot cur (fl c p) (rs c p) then Z_to_bv 8 0 else fl c p.

Lemma c8x4_of_dc : forall m A, dc_at m A 32 -> exists w0 w1 w2 w3 : word, rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
  intros m A D. destruct (dc_split m A 16 16 D ltac:(lia) ltac:(lia)) as [D1 D2].
  destruct (c8c8_of_dc m A D1) as (w0 & w1 & H1). destruct (c8c8_of_dc m (A + 16) D2) as (w2 & w3 & H2).
  exists w0, w1, w2, w3. apply (proj2 (rw_cells_app bsegs m A [C8 w0; C8 w1] [C8 w2; C8 w3])). split; [exact H1| exact H2].
Qed.

Definition sm2gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs + 16, fs + 24) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 248, F + 256)
  :: (shad F, shad F + 32) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm2gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm2gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 hv); CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (2, (flag - (fs + 28672))) ->
          rw_cells bsegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc2_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells bsegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells bsegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 4096 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 2 (Z.land (h + t) 4095)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  gfl' fl rs bot (bv_unsigned sp) 2 pos = Z_to_bv 8 0 ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 248) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm2gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm2gc_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 4095 < 4096) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 298984)) with (Z_to_bv 64 298984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x631000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells bsegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells bsegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono bsegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 2134016 <= F /\ F + 256 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 248) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8x4_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & q1 & q2 & q3 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs + 16, fs + 24) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 248, F + 256) :: (shad F, shad F + 32) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256);
                          (shad F, shad F + 32)]%Z mg) as MUq.
  pose proof (wmono_refl bsegs mg) as WMq.
  assert (GF2 : forall p, gflag fs 2 p = fs + 28672 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 2)) with 8192; lia).
  assert (GN2 : gcN 2 = 4096) by reflexivity.
  assert (FL0g : rw_cells bsegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 2 pos ltac:(lia) ltac:(rewrite GN2; lia)) as X. rewrite GF2 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm2_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 2 (Z.land (h + tq) 4095)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm2_flag.
    pose proof (FLSg 2 (Z.land (h + tq) 4095) ltac:(lia) ltac:(rewrite GN2; lia)) as X. rewrite GF2 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm2_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm2_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB ATR. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm2gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm2gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 2 pos c p ltac:(lia) ltac:(rewrite GN2; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF2 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm2gc.

Module AFake_sm1gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import AFake_sm1g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB. Import AFake_sm2gc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition sm1gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs + 8, fs + 16) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 120, F + 128)
  :: (shad F, shad F + 16) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm1gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm1gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' fs [C8 h0; C8 (Z_to_bv 64 hv); C8 h1; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (1, (flag - (fs + 20480))) ->
          rw_cells bsegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc1_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 sh1 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells bsegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells bsegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 8192 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 1 (Z.land (h + t) 8191)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  gfl' fl rs bot (bv_unsigned sp) 1 pos = Z_to_bv 8 0 ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 120) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm1gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm1gc_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 8191 < 8192) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 298584)) with (Z_to_bv 64 298584) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x631000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells bsegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells bsegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono bsegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 1085440 <= F /\ F + 128 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 120) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8c8_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & q1 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs + 8, fs + 16) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 120, F + 128) :: (shad F, shad F + 16) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128);
                          (shad F, shad F + 16)]%Z mg) as MUq.
  pose proof (wmono_refl bsegs mg) as WMq.
  assert (GF1 : forall p, gflag fs 1 p = fs + 20480 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 1)) with 16384; lia).
  assert (GN1 : gcN 1 = 8192) by reflexivity.
  assert (FL0g : rw_cells bsegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 1 pos ltac:(lia) ltac:(rewrite GN1; lia)) as X. rewrite GF1 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep. zstep. zstep. zstep.
  zstep.
  do 9 zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm1_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 1 (Z.land (h + tq) 8191)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm1_flag.
    pose proof (FLSg 1 (Z.land (h + tq) 8191) ltac:(lia) ltac:(rewrite GN1; lia)) as X. rewrite GF1 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm1_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm1_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm1gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm1gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 1 pos c p ltac:(lia) ltac:(rewrite GN1; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF1 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm1gc.

Module AFake_sm0gc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import AFake_sm0. Import AFake_sm0g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB. Import AFake_sm2gc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition sm0gc_W (sp fs flag F : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot : Z) : list (Z * Z) :=
  (sp - 240, sp) :: (fs + 96, fs + 97) :: (fs, fs + 8) :: (flag, flag + 1) :: (F + 24, F + 32) :: (F + 56, F + 64)
  :: (shad F, shad F + 8) :: gcWall fs fl rs bot sp 0 GC_NCLS.

Definition sm0gc_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs hv flag F bot : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm0gc_W (bv_unsigned sp) fs flag F fl rs bot) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' fs [C8 (Z_to_bv 64 hv); C8 h0; C8 h1; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (0, (flag - (fs + 4096))) ->
          rw_cells bsegs m' (gflag fs c p) [C1 (gfl' fl rs bot (bv_unsigned sp) c p)]).

Lemma stack_malloc0_gcspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F top bot : Z) (j : nat) (g : byte)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (j24 j248 sh0 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->

  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> bot <= bv_unsigned sp <= top ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 (Z_to_bv 64 h); C8 h0; C8 h1; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 g] -> bv_unsigned g <> 0 ->

  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells bsegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells bsegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot (bv_unsigned sp) (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe fs c p)) (map C8 ws)) ->

  Z.of_nat j < 16384 ->
  (forall t, 0 <= t < Z.of_nat j -> bv_unsigned (gfl' fl rs bot (bv_unsigned sp) 0 (Z.land (h + t) 16383)) <> 0) ->
  pos = Z.land (h + Z.of_nat j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  gfl' fl rs bot (bv_unsigned sp) 0 pos = Z_to_bv 8 0 ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 56) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0] ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm0gc_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat j + 1) flag F bot fl rs h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CXa CXb T0 T1 BLO BHI V TB SW B0 BT TT CURR
         FLO FHI FAL HNT HB LOG NGC GNZ FL RS SH JB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FBD). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0gc_W (bv_unsigned sp) fs flag F fl rs bot) m) as MU. unfold sm0gc_W in MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MUs.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (LB : forall x, 0 <= Z.land x 16383 < 16384) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
  zstep.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  { exfalso. pose proof (bv_unsigned_in_range 8 g) as RG8. change (bv_modulus 8) with 256 in RG8. rewrite ?Z.mod_small in Kb by lia. lia. }
  zstep. zstep.
  zstep.
  pose proof atop_range as ATR.
  word_range sp SPR.

  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRs : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.
  eapply evtF_cut.
  { eapply gc_spec with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := bv_unsigned sp) (fl := fl) (rs := rs);
      try eassumption; try reflexivity; try lia.
    all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    - exact ST.
    - lia.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TRs; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TRs; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TRs; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. unfold gc_post.
  intros ms' (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mg & -> & MUg & WMg & MIg & STg & NGC0 & FLSg).
  rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
  replace (ret_pc (Z_to_bv 64 298212)) with (Z_to_bv 64 298212) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof GC_NCLS_eq as NCE.

  assert (DGs : forall A n, ATOP <= A -> bv_unsigned sp + -32 <= A -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (DGi : forall A n, 0 <= n -> A + n <= 0x631000 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_img; try assumption; lia. }
  assert (DGf : forall A n, 0 <= n -> fs <= A -> A + n <= fs + 96 -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A n).
  { intros A n HN HA HA2. unfold gc_W. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _).
    apply gcW1_disj_in_fs; try assumption; lia. }
  lazymatch goal with MUx : munch [(bv_unsigned sp - 240, bv_unsigned sp)] m ?mm |- _ =>
    assert (TRg : forall A cs, rw_cells bsegs mm A cs -> disjoint_from (gc_W (bv_unsigned sp + -32) fs fl rs bot (bv_unsigned sp)) A (Z.of_nat (cells_size cs)) ->
                    rw_cells bsegs mg A cs)
      by (intros A cs H HD; eapply rw_cells_transport; [exact H| exact MUg| exact WMg| exact HD])
  end.
  apply TRg in HNT; [| apply DGf; cbn; lia].
  apply TRg in SHB; [| apply DGi; cbn; lia]. apply TRg in LAY; [| apply DGi; cbn; lia]. apply TRg in G50; [| apply DGi; cbn; lia].
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => apply TRg in FRx; [| apply DGs; cbn; lia]; rename FRx into FRg end.

  assert (WMt : wmono bsegs m mg) by (eapply wmono_trans; [exact WM| exact WMg]).
  assert (FRNG : fs + 36864 <= F /\ F + 64 <= fs + 11571200) by (clear - FF PB; lia).
  lazymatch type of F24 with rw_cells _ ?mm _ _ =>
    destruct (c8_of_dc mg (F + 24) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F24) WMg ltac:(lia))) as (k24 & F24g);
    destruct (c8_of_dc mg (F + 56) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ F56) WMg ltac:(lia))) as (k248 & F56g);
    destruct (c8_of_dc mg (shad F) (dc_at_any mm mg _ _ (dc_of_cells mm _ _ SH0) WMg ltac:(rewrite SHF; clear - FRNG FLOL; Z.div_mod_to_equations; lia)))
      as (q0 & SH0g)
  end.
  clear F24 F56 SH0.

  assert (MUt : munch ((bv_unsigned sp - 240, bv_unsigned sp) :: (fs + 96, fs + 97) :: (fs, fs + 8) :: (flag, flag + 1) :: (F + 24, F + 32)
                        :: (F + 56, F + 64) :: (shad F, shad F + 8) :: gcWall fs fl rs bot (bv_unsigned sp) 0 GC_NCLS) m mg).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUg]. unfold gc_W. intros xx Hxx. cbn [outside] in Hxx |- *.
    destruct Hxx as (X1 & X2 & _ & _ & _ & _ & _ & X8). split; [lia|]. split; [exact X2| exact X8]. }
  clear MU MUs WM TRs TRg MUg WMg DGs DGi DGf. rename MUt into MU. rename WMt into WM. rename STg into STq. clear ST. rename STq into ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64);
                          (shad F, shad F + 8)]%Z mg) as MUq.
  pose proof (wmono_refl bsegs mg) as WMq.
  assert (GF0 : forall p, gflag fs 0 p = fs + 4096 + p) by (intros p; unfold gflag, gflags; change (2 ^ (15 - 0)) with 32768; lia).
  assert (GN0 : gcN 0 = 16384) by reflexivity.
  assert (FL0g : rw_cells bsegs mg flag [C1 (Z_to_bv 8 0)]).
  { pose proof (FLSg 0 pos ltac:(lia) ltac:(rewrite GN0; lia)) as X. rewrite GF0 in X. unfold gfl' in FL0. rewrite FL0 in X. rewrite FLAG. exact X. }
  zstep. zstep. zstep.
  zstep; lits.
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
  zstep. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep.

  setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUSYk : forall t, 0 <= t < Z.of_nat j -> exists b : byte, rw_cells bsegs mm (sm0_flag fs (h + 0 + t)) [C1 b] /\ bv_unsigned b <> 0) end.
  { intros tq Ht. exists (gfl' fl rs bot (bv_unsigned sp) 0 (Z.land (h + tq) 16383)). split; [| apply BUSY; exact Ht].
    replace (h + 0 + tq) with (h + tq) by lia. pose proof (LB (h + tq)) as LBt. unfold sm0_flag.
    pose proof (FLSg 0 (Z.land (h + tq) 16383) ltac:(lia) ltac:(rewrite GN0; lia)) as X. rewrite GF0 in X.
    exact X. }
  eapply evtF_cut.
  { eapply (sm0_probe_loop RNG j 0); try eassumption; try lia.
    replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG. exact FL0g. }
  cbv beta. intros ms2 ->. clear BUSYk.
  replace (h + 0 + Z.of_nat j) with (h + Z.of_nat j) by lia. unfold sm0_flag. rewrite <- POS, <- FLAG.
  rename F24g into F24. rename F56g into F56. rename SH0g into SH0.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep.
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.
  zstep.
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.
  do 6 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  lazymatch goal with FRx : rw_cells bsegs _ (bv_unsigned sp + -32) _ |- _ => rename FRx into FR9 end.
  release_frame FR9 ST9 (bv_unsigned sp).
  apply evtF_done. unfold sm0gc_cpost. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold sm0gc_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST9|].
  split; [exact NGC0|]. split; [exact HNT|]. split; [exact FL0g|]. split; [exact F24|]. split; [exact F56|]. split; [exact SH0|].
  intros c p Hc Hp NE. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSg; assumption| exact MUq| exact WMq|].
  cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
  assert (NF : gflag fs c p + 1 <= flag \/ flag + 1 <= gflag fs c p).
  { destruct (gflag_sep fs 0 pos c p ltac:(lia) ltac:(rewrite GN0; lia) Hc Hp
               ltac:(intros E; injection E as E1 E2; subst c p; apply NE; f_equal; rewrite FLAG; lia)) as [X|X];
      rewrite GF0 in X; rewrite FLAG; [left|right]; lia. }
  repeat split; try lia.
Qed.
End CANSEC1.
End AFake_sm0gc.
End TwinB.
