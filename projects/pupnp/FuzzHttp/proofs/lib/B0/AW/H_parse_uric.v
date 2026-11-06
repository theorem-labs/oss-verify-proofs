(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_parse_uric.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto F_ctypeA AWRng AWUb.
Import ListNotations.
Open Scope Z_scope.

Definition parse_uric_entryA : Z := 0x8e19c.
Notation MARKTAB_A := 0x21c20%Z.
Notation RESVTAB_A := 0x21c60%Z.
Notation mark10 := P0.H_parse_uric.mark10.
Notation resv13 := P0.H_parse_uric.resv13.

Lemma mark_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m MARKTAB_A mark10.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m MARKTAB_A mark10 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma resv_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m RESVTAB_A resv13.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m RESVTAB_A resv13 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma memchr_chk_le : forall A c n buf, 0 < A -> 0 <= n ->
  0 <= (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) <= n.
Proof.
  intros A c n buf HA Hn. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; cbv zeta.
  - destruct (find_byte_Some _ _ _ E) as (L & _ & _). rewrite length_firstn in L.
    destruct (Z.eqb_spec (A + Z.of_nat i) 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma dia1 : forall (IN i : Z) x1 xsp gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x25 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  acc m (IN + i) -> 0 <= IN + i < 2^63 ->
  evt asegs (fun ms' => exists a0' a1',
      ms' = MS (mkR x1 xsp gp tp t0 t1 t2 x8 (wz IN) a0' a1' a2 a3 a4 a5 a6 a7 (wz i) x19 x20 x21 (wz (IN + i)) x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
               F (wz 0x8e238) fc None m (seg_rom asegs))
    (MS (mkR x1 xsp gp tp t0 t1 t2 x8 (wz IN) a0 a1 a2 a3 a4 a5 a6 a7 (wz i) x19 x20 x21 x22 x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
        F (wz 0x8e224) fc None m (seg_rom asegs)).
Proof.
  intros IN i x1 xsp gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x25 s10 s11 t3 t4 t5 t6 F fc m HACC RNG.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  acc_chk 10 (IN + i) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; step; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: apply evt_done; do 2 eexists; reflexivity.
Qed.

#[using="Type"] Lemma dia2 : forall (V : Z) x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x25 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  acc m (V + 1) -> 0 <= V -> V + 1 < 2^63 ->
  evt asegs (fun ms' => exists a1' a2',
      ms' = MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 (wz (V + 1)) a1' a2' a3 a4 a5 a6 a7 x18 x19 x20 x21 (wz V) x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
               F (wz 0x8e298) fc None m (seg_rom asegs))
    (MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (wz V) x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
        F (wz 0x8e284) fc None m (seg_rom asegs)).
Proof.
  intros V x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x25 s10 s11 t3 t4 t5 t6 F fc m HACC V0 RNG.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  acc_chk 11 (V + 1) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; step; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: apply evt_done; do 2 eexists; reflexivity.
Qed.

#[using="Type"] Lemma dia3 : forall (V : Z) x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x25 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  acc m (V + 2) -> 0 <= V -> V + 2 < 2^63 ->
  evt asegs (fun ms' => exists a1' a2',
      ms' = MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 (wz (V + 2)) a1' a2' a3 a4 a5 a6 a7 x18 x19 x20 x21 (wz V) x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
               F (wz 0x8e2bc) fc None m (seg_rom asegs))
    (MS (mkR x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (wz V) x23 (wz 0x7fff8000) x25 s10 s11 t3 t4 t5 t6)
        F (wz 0x8e2a8) fc None m (seg_rom asegs)).
Proof.
  intros V x1 xsp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x25 s10 s11 t3 t4 t5 t6 F fc m HACC V0 RNG.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  acc_chk 11 (V + 2) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; step; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: apply evt_done; do 2 eexists; reflexivity.
Qed.

Definition parse_uric_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (IN O max lo : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (i : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (O, O + 16)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' O [C8 (wz IN); C8 (wz i)]
    /\ bytes_at asegs m' IN bs
    /\ 0 <= i <= max.

Definition parse_uric_stmt_A : Prop :=
  forall (IN O max lo : Z) (bs : list byte) (ow1 ow2 : word)
         (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at asegs m IN bs -> Z.of_nat (length bs) >= max -> 0 <= max ->
  rw_cells asegs m O [C8 ow1; C8 ow2] ->

  0x609000 <= IN -> IN + Z.of_nat (length bs) <= alloc_ceiling -> shw m IN max ->

  0x609000 <= O -> O + 16 <= alloc_ceiling -> O mod 8 = 0 -> shw m O 16 ->
  (IN + Z.of_nat (length bs) <= O \/ O + 16 <= IN) ->

  shw m MARKTAB_A 10 -> shw m RESVTAB_A 13 ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz IN -> a1 = wz max -> a2 = wz O ->
  evt asegs (parse_uric_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IN O max lo bs m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_uric_entryA) fc None m (seg_rom asegs)).

Section WALK.
  Variables (IN O max lo : Z) (bs : list byte) (ow1 ow2 : word).
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis LBS : Z.of_nat (length bs) >= max.
  Hypothesis MAX : 0 <= max.
  Hypothesis INLO : 0x609000 <= IN.
  Hypothesis INHI : IN + Z.of_nat (length bs) <= alloc_ceiling.
  Hypothesis SHWIN : shw m0 IN max.
  Hypothesis OLO : 0x609000 <= O.
  Hypothesis OHI : O + 16 <= alloc_ceiling.
  Hypothesis OAL : O mod 8 = 0.
  Hypothesis SHWO : shw m0 O 16.
  Hypothesis SEP : IN + Z.of_nat (length bs) <= O \/ O + 16 <= IN.
  Hypothesis SHWMK : shw m0 MARKTAB_A 10.
  Hypothesis SHWRV : shw m0 RESVTAB_A 13.
  Hypothesis AE0 : asan_env asegs m0.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LO : lo <= q - 112 - 4096.
  Hypothesis QHI : q < 2^64.

  Notation POST := (parse_uric_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IN O max lo bs m0).

  Definition minvA (m : mem) : Prop :=
    (exists j8, rw_cells asegs m (q + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs m lo (q + -112)
    /\ rw_cells asegs m O [C8 ow1; C8 ow2]
    /\ bytes_at asegs m IN bs
    /\ mem_inv asegs m
    /\ munch [(lo, q); (O, O + 16)] m0 m
    /\ wmono asegs m0 m.

  Notation LSTU pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 mm :=
    (MS (mkR x1 (wz (q + -112)) gp tp x5 x6 x7 (wz O) (wz IN) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (wz max) (wz MARKTAB_A) (wz RESVTAB_A) x22 x23 (wz 0x7fff8000) (wz (Z.lxor IN 18446744073709551615)) (wz 37) (wz (-3)) x28 x29 x30 x31)
        F (wz pc) fc None mm (seg_rom asegs)).

  #[using="HC OLO OHI OAL SHWO SEP AE0 CLO LO"] Lemma tailA0 : forall (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 m,
    minvA m -> 0 <= i <= max ->
    evt asegs POST (MS (mkR x1 (wz (q + -112)) gp tp x5 x6 x7 (wz O) (wz IN) x10 x11 x12 x13 x14 x15 x16 x17
                            (wz i) x19 x20 x21 x22 x23 (wz 0x7fff8000) x25 x26 x27 x28 x29 x30 x31)
                        F (wz 0x8e2fc) fc None m (seg_rom asegs)).
  Proof.
    intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 m.
    intros ([j8 FR] & ST & OC & BUF & MI & MU & WM) HI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    walk_lia_to 0x8e360%Z. release_to q. step. step.
    env_now AE0 MU WM.
    unfold parse_uric_post_A. finish. all: first [exact OC | exact BUF | lia].
  Qed.

  #[using="HC OLO OHI OAL SHWO SEP AE0 CLO LO QHI"] Lemma tailA : forall (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 m,
    minvA m -> 0 <= i <= max ->
    evt asegs POST (MS (mkR x1 (wz (q + -112)) gp tp x5 x6 x7 (wz O) (wz IN) x10 x11 x12 x13 x14 x15 x16 x17
                            (wz i) x19 x20 x21 x22 x23 (wz 0x7fff8000) x25 x26 x27 x28 x29 x30 x31)
                        F (wz 0x8e2f4) fc None m (seg_rom asegs)).
  Proof.
    intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 m MV HI.
    pose proof (munch_refl [] m) as MUx.
    ub_align.
    apply (tailA0 i); assumption.
  Qed.

  #[using="O bs"] Lemma byte_rangeA : forall b : byte, 0 <= bv_unsigned b < 256.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
  #[using="O LBS OLO"] Lemma nth_bsA : forall i, 0 <= i < max -> exists b, nth_error bs (Z.to_nat i) = Some b.
  Proof.
    intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  Ltac mv_tac FR := split; [eexists; exact FR|]; repeat (split; [assumption|]); assumption.
  Ltac get_mv FR := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MV := fresh "MV" in assert (MV : minvA mm) by mv_tac FR end.

  #[using="HC IC LBS MAX INLO INHI SHWIN OLO OHI OAL SHWO SEP SHWMK SHWRV AE0 CLO LO QHI"] Lemma loopU : forall (k : nat) (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 m,
    max - i < Z.of_nat k -> 0 <= i < max -> minvA m ->
    evt asegs POST (LSTU 0x8e220 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz i) x22 x23 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 m; intros HK HI MV; [lia|].
    pose proof MV as ([j8 FR] & ST & OC & BUF & MI & MU & WM).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bsA i ltac:(lia)) as [b Hb]. pose proof (byte_rangeA b) as BR.
    pose proof (u8ro_read asegs m IN bs i b (Z_to_bv 64 (IN + i)) BUF Hb ltac:(lia) eq_refl) as RD.
    pose proof (shw_frame _ m0 m IN max SHWIN MU ltac:(app_ivs_tac)) as SHWINm.

    assert (CONT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 m',
      minvA m' ->
      evt asegs POST (LSTU 0x8e218 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz i) y22 y23 y28 y29 y30 y31 m')).
    { intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 m' MV'.
      pose proof (munch_refl [] m') as MUx. zstep. step. if_cases KC; zify_cond KC.
      -   zstep. apply (tailA max); [exact MV'| lia].
      - apply (IH (i + 1)); [lia| lia| exact MV']. }
    step. ubr.
    eapply evt_cut. { eapply (dia1 IN i); [exact (proj1 SHWINm (IN + i) ltac:(lia))| lia]. }
    intros ms' (a0' & a1' & ->).
    zstep. zstep.
    step.
    call isalnum_spec_A. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K1; zify_cond K1.
    {   apply CONT. exact MV. }
    zstep. zstep. zstep. step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_frame _ m0 mm MARKTAB_A 10 SHWMK MU ltac:(app_ivs_tac)) as SHWTm;
      pose proof (asan_env_frame asegs m0 mm _ AE0 MU WM ltac:(env_safe_tac)) as AEn end.
    pose proof (memchr_chk_le MARKTAB_A (bv_unsigned b) 10 mark10 ltac:(lia) ltac:(lia)) as CK.
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_memchr IC) with (A := MARKTAB_A) (c := bv_unsigned b) (n := 10) (buf := mark10) (lo := lo);
        first [ rng_tac | exact (mark_bytes_A mm MIx) | apply P0.H_parse_uric.memchr_ok_mark | exact AEn | exact MIx | reflexivity
              | (eapply accessible_sub; [exact (proj1 SHWTm)| lia| lia])
              | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWTm))| lia| lia| lia])
              | (unfold A0_RT_STACK; lia) | (left; cbn; lia) | lia | eassumption ]
      | post_call asegs mm ] end.
    clear MV SHWTm AEn CK SHWINm. get_mv FR.
    pose proof (P0.H_parse_uric.memchr_res_small' MARKTAB_A (bv_unsigned b) 10 mark10 ltac:(lia)) as MR.
    cbn [length P0.H_parse_uric.mark10 map Z.of_nat Pos.of_succ_nat Pos.succ] in MR.
    zstep. if_cases K2; zify_cond K2.
    {   apply CONT. exact MV. }
    clear MR. zstep. zstep. zstep. step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_frame _ m0 mm RESVTAB_A 13 SHWRV MU ltac:(app_ivs_tac)) as SHWTm;
      pose proof (asan_env_frame asegs m0 mm _ AE0 MU WM ltac:(env_safe_tac)) as AEn end.
    pose proof (memchr_chk_le RESVTAB_A (bv_unsigned b) 13 resv13 ltac:(lia) ltac:(lia)) as CK.
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_memchr IC) with (A := RESVTAB_A) (c := bv_unsigned b) (n := 13) (buf := resv13) (lo := lo);
        first [ rng_tac | exact (resv_bytes_A mm MIx) | apply P0.H_parse_uric.memchr_ok_resv | exact AEn | exact MIx | reflexivity
              | (eapply accessible_sub; [exact (proj1 SHWTm)| lia| lia])
              | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWTm))| lia| lia| lia])
              | (unfold A0_RT_STACK; lia) | (left; cbn; lia) | lia | eassumption ]
      | post_call asegs mm ] end.
    clear MV SHWTm AEn CK. get_mv FR.
    pose proof (P0.H_parse_uric.memchr_res_small' RESVTAB_A (bv_unsigned b) 13 resv13 ltac:(lia)) as MR.
    cbn [length P0.H_parse_uric.resv13 map Z.of_nat Pos.of_succ_nat Pos.succ] in MR.
    zstep. if_cases K3; zify_cond K3.
    {   apply CONT. exact MV. }
    clear MR. zstep. step. if_cases K4; zify_cond K4.
    {   apply (tailA i); [exact MV| lia]. }
    step. if_cases K5; zify_cond K5.
    {   apply (tailA i); [exact MV| lia]. }
    zstep. step. ubr.
    destruct (nth_bsA (i + 1) ltac:(lia)) as [b1 Hb1]. pose proof (byte_rangeA b1) as BR1.
    destruct (nth_bsA (i + 2) ltac:(lia)) as [b2 Hb2]. pose proof (byte_rangeA b2) as BR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_frame _ m0 mm IN max SHWIN MU ltac:(app_ivs_tac)) as SHWINx;
      destruct MV as (_ & _ & _ & BUFx & _);
      pose proof (u8ro_read asegs mm IN bs (i + 1) b1 (Z_to_bv 64 (IN + i + 1)) BUFx Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1;
      pose proof (u8ro_read asegs mm IN bs (i + 2) b2 (Z_to_bv 64 (IN + i + 2)) BUFx Hb2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2 end.
    get_mv FR.
    eapply evt_cut. { eapply (dia2 (IN + i)); [exact (proj1 SHWINx (IN + i + 1) ltac:(lia))| lia| lia]. }
    intros ms' (a1x & a2x & ->).
    zstep. step.
    call isxdigit_spec_A. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ eassumption. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K6; zify_cond K6.
    {   apply (tailA i); [exact MV| lia]. }
    step.
    ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-3) mod 18446744073709551616) with 18446744073709551613 in KU; lia).
    eapply evt_cut. { eapply (dia3 (IN + i)); [exact (proj1 SHWINx (IN + i + 2) ltac:(lia))| lia| lia]. }
    intros ms' (a1y & a2y & ->).
    zstep. step.
    call isxdigit_spec_A. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ eassumption. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K7; zify_cond K7.
    { apply CONT. exact MV. }
    zstep. apply (tailA i); [exact MV| lia].
  Qed.
  #[using="HC IC LBS MAX INLO INHI SHWIN OLO OHI OAL SHWO SEP SHWMK SHWRV AE0 CLO LO QHI"] Lemma bodyU : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    bytes_at asegs m0 IN bs -> rw_cells asegs m0 O [C8 ow1; C8 ow2] ->
    stk asegs m0 lo q -> mem_inv asegs m0 ->
    evt asegs POST
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz IN) (wz max) (wz O) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz parse_uric_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. intros BUF OC ST MI. unfold parse_uric_entryA.
    a0_prologue AE0 [(lo, q); (O, O + 16)]%Z m0.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    carve_frame 112%nat ST.
    walk_lia_to 0x8e1ec%Z. step. if_cases K0; zify_cond K0.
    {
      zstep. zstep. step.
      ubr3.
      apply (tailA0 0); [mv_tac FR| lia]. }
    walk_lia_to 0x8e220%Z.
    apply (loopU (Datatypes.S (Z.to_nat max)) 0); [lia| lia| mv_tac FR].
  Qed.
End WALK.

#[using="IC"] Lemma parse_uric_spec_A : parse_uric_stmt_A.
Proof.
  unfold parse_uric_stmt_A. intros IN O max lo bs ow1 ow2 ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros BUF LBS MAX OC INLO INHI SHWIN OLO OHI OAL SHWO SEP SHWMK SHWRV AE ST CLO LO QHI MI -> -> ->.
  unfold A0_RT_STACK in LO.
  eapply (bodyU IN O max lo bs ow1 ow2); eauto.
Qed.

End W.
