(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Notation IFRA m q j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
  (rw_cells asegs m q [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition isegA_post (lo MB SRC n A len cap : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (x1 a0' a1' a4' a5' x18 x24 x25 x26 x27 : word) (c0 : cell) (pc nsz : Z),
    ms' = MS (mkR x1 (wz (q + -112)) gp tp t0 t1 t2 (wz (MB + 8)) (wz (MB + 16)) a0' a1' (wz n) (wz len) a4' a5' a6 a7
                  x18 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) (wz (Z.shiftr MB 3))
                  (wz (len + n)) x24 x25 x26 x27 t3 t4 t5 t6)
             F (wz pc) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -112)
    /\ rw_cells asegs m' (q + -112) [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' MB (mbuf_cells A len cap)
    /\ ( (pc = 0x8c544 /\ nsz = cap /\ a0' = wz MB /\ a1' = wz SRC /\ x24 = wz cap /\ (exists j, c0 = CB 8 j) /\ len + n <= cap)
       \/ (pc = A0_realloc /\ x1 = wz 0x8c514 /\ a0' = wz A /\ a1' = wz (nsz + 1) /\ x18 = wz MB /\ x24 = wz nsz /\ x25 = wz SRC /\ x26 = wz n
           /\ x27 = wz (Z.shiftr MB 3 + 2147450880) /\ c0 = C8 (wz len) /\ len + n <= nsz /\ cap + 5 <= nsz <= cap + Z.max 5 n /\ cap < len + n    ) ).

Ltac isegA_leaf :=
  apply evt_done; unfold isegA_post, A0_realloc, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 14 eexists; split; [reflexivity|];
  repeat (split; [eassumption|]).

#[using="Type"] Lemma isegA : forall (lo MB SRC n A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < SRC < 2^64 -> 0 <= len <= cap -> 1 <= n -> cap + n + 8 <= 2^28 -> 0 <= A < 2^64 ->
  evt asegs (isegA_post lo MB SRC n A len cap ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) (wz len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c404) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A len cap ra q gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL ACC WK HS HLC HN HNC HA. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 112%nat ST.
  do 14 (step; fix_lit_store).
  step. step. step.
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC1.
  zstep. zstep. zstep. acc_chk0 20 (MB + 8) ACC1. step. step. lit_branch.
  step. zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. zstep. zstep. acc_chk0 21 (MB + 16) ACC1. step. step. lit_branch.
  step. zstep. zstep.
  zstep. if_cases K3; zify_cond K3.
  2: { exfalso. lia. }
  zstep. if_cases K4; zify_cond K4.
  -
    isegA_leaf. left. repeat split; try reflexivity; try lia. eexists; reflexivity.
  -
    zstep. zstep. zstep. acc_chk0 15 (MB + 24) ACC1. step. step. lit_branch.
    step. zstep. if_cases K5; zify_cond K5.
    + zstep. zstep. step. fix_lit_store. zstep.
      pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC2.
      acc_chk0 27 MB ACC2. step. step. lit_branch.
      zstep. zstep. step. zstep. step.
      isegA_leaf. right. repeat split; try reflexivity; lia.
    + zstep. zstep. zstep. step. fix_lit_store. zstep.
      pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC2.
      acc_chk0 27 MB ACC2. step. step. lit_branch.
      zstep. zstep. step. zstep. step.
      isegA_leaf. right. repeat split; try reflexivity; lia.
Qed.

Definition isegS_post (lo MB SRC n B len nsz : Z) (q : Z) (gp tp : word) (x18 x22 x23 x24 x25 x26 x27 : word)
    (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (fr : list cell)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (a4' a5' : word),
    ms' = MS (mkR (wz 0x8c514) (wz (q + -112)) gp tp t0 t1 t2 (wz (MB + 8)) (wz (MB + 16)) (wz MB) (wz SRC) (wz n) (wz len) a4' a5' a6 a7
                  x18 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F (wz 0x8c544) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -112) /\ rw_cells asegs m' (q + -112) (C8 (wz len) :: fr)
    /\ rw_cells asegs m' MB (mbuf_cells B len nsz).

#[using="Type"] Lemma isegS : forall (lo MB SRC n A B len cap nsz : Z) (q : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 x23 t3 t4 t5 t6
    (F : bvmap 5 word) fc (fr : list cell) m,
  stk asegs m lo (q + -112) -> alloc_ceiling <= lo -> lo <= q - 112 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -112) (C8 (wz len) :: fr) -> cells_size fr = 104%nat ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < B < 2^64 -> 0 <= len < 2^64 ->
  evt asegs (isegS_post lo MB SRC n B len nsz q gp tp (wz MB) x22 x23 (wz nsz) (wz SRC) (wz n) (wz (Z.shiftr MB 3 + 2147450880))
               t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc fr m)
    (MS (mkR (wz 0x8c514) (wz (q + -112)) gp tp t0 t1 t2 (wz (MB + 8)) (wz (MB + 16)) (wz B) a1 a2 a3 a4 a5 a6 a7
             (wz MB) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) x22 x23
             (wz nsz) (wz SRC) (wz n) (wz (Z.shiftr MB 3 + 2147450880)) t3 t4 t5 t6)
        F (wz 0x8c514) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A B len cap nsz q gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 x23 t3 t4 t5 t6 F fc fr m.
  intros ST CLO LO QHI MI FR FRS MBC MBLO MBHI AL ACC WK HB HL. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. acc_chk0 27 MB ACC. step. zstep. step. step. lit_branch.
  step. fix_lit_store.
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(unfold win_ok in WK; app_ivs_tac)) as ACC1.
  acc_chk0 21 (MB + 16) ACC1. step. step. lit_branch.
  zstep. zstep. step. fix_lit_store.
  apply evt_done. unfold isegS_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). exact MBC.
Qed.

Definition isegM_post (lo MB n A' len cap' : Z) (bsF : list byte) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' MB (mbuf_cells A' (len + n) cap')
    /\ rw_cells asegs m' A' [CB (Z.to_nat (cap' + 1)) bsF].

#[using="IC"] Lemma isegM : forall (lo MB SRC n A' len cap' : Z) (src bs j : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 x1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x18 x23 x24 x25 x26 x27 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -112) -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q + -112) [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m MB (mbuf_cells A' len cap') -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  shw m MB 32 ->
  1 <= n -> 0 <= len -> len + n <= cap' -> cap' + 1 < 2^32 ->
  rw_cells asegs m A' [CB (Z.to_nat (cap' + 1)) bs] -> shw m A' (cap' + 1) ->
  0x609000 <= A' -> A' + (cap' + 1) <= alloc_ceiling -> A' mod 8 = 0 ->
  (MB + 32 <= A' \/ A' + (cap' + 1) <= MB) ->
  bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> shw m SRC n ->
  (SRC + n <= alloc_ceiling \/ (q <= SRC /\ SRC + n < 2^47)) -> (SRC + n <= MB \/ MB + 32 <= SRC) -> (SRC + n <= A' \/ A' + (cap' + 1) <= SRC) ->
  evt asegs (isegM_post lo MB n A' len cap' (firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs)
               ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (q + -112)) gp tp t0 t1 t2 (wz (MB + 8)) (wz (MB + 16)) (wz MB) (wz SRC) (wz n) (wz len) a4 a5 a6 a7
             x18 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) (wz (Z.shiftr MB 3))
             x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (wz 0x8c544) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A' len cap' src bs j ra q gp tp t0 t1 t2 s0 s1 x1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x18 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR MBC MBLO MBHI AL SHWM HN HL0 HLN HC32 BLK SHWA AHI ACE AAL DJM SRCB LEN SHWS SLO DJS DJA.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *. unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BB.
  assert (LBS : length bs = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; tauto).
  zstep. acc_chk0 22 MB (proj1 SHWM). step. step. lit_branch.
  zstep. acc_chk0 20 (MB + 8) (proj1 SHWM). step. step. lit_branch.
  step. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. step.
  replace (len - len)%Z with 0%Z by lia.
  pose proof (shw_win_ok _ _ _ SHWM) as WKM. unfold win_ok in WKM.
  env_now AE0 MU WM.
  pose proof (u8arr_of_rw_cells asegs _ _ _ _ BLK) as ARR. clear BLK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memmove IC) with (D := A' + len + n) (S := A' + len) (n := 0) (U := A') (us := bs) (lo := lo);
      first [ rng_tac | exact ARR | exact MI | exact AE | exact ST | reflexivity
            | (intros a Ha; exfalso; lia) | (intros Hn; exfalso; lia)
            | (rewrite ?LBS; lia) | (unfold A0_RT_STACK; lia) ]
    | post_call asegs mm ] end.
  change (Z.to_nat 0) with 0%nat in POST. unfold upd_bytes in POST. cbn [firstn length app] in POST. rewrite Nat.add_0_r, firstn_skipn in POST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (rw_cells_of_u8arr asegs _ _ _ POST) as BLK1. rewrite LBS in BLK1. clear POST SHR SHR0.

  apply (rw_cells_split_CB asegs m1 A' [] (Z.to_nat (cap' + 1)) bs [] [Z.to_nat len; Z.to_nat n; 1%nat; Z.to_nat (cap' - len - n)]) in BLK1; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK1.
  lazymatch type of BLK1 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4] =>
    destruct (proj1 (rw_cells_app asegs m1 A' [c1] [c2; c3; c4]) BLK1) as [BLKa BLKb];
    cbn [cells_size csize] in BLKb; rewrite Nat.add_0_r, Z2Nat.id in BLKb by lia;
    destruct (proj1 (rw_cells_app asegs m1 (A' + len) [c2] [c3; c4]) BLKb) as [BLKn BLKc];
    cbn [cells_size csize] in BLKc; rewrite Nat.add_0_r, Z2Nat.id in BLKc by lia end.
  clear BLK1 BLKb.
  step. zstep. zstep. zstep. step.
  pose proof SHWA as SHWA1. pose proof SHWS as SHWS1. shw_now SHWA1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memcpy IC) with (D := A' + len) (S := SRC) (n := n) (lo := lo) (src := src);
      first [ rng_tac | exact BLKn | exact SRCB | exact LEN | exact MI0 | exact AE1 | exact PC | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHWA1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWA1)) | lia | lia | lia])
            | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1))
            | (split; [exact (proj2 (proj2 SHWS1))| split; lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
    | post_call asegs mm ] end.
  clear SHWA1 SHWS1 AE AE1.
  step. step. zstep. step. fix_lit_store. zstep. zstep. zstep.
  pose proof SHWA as SHWA1. shw_now SHWA1 MU.
  pose proof (proj1 SHWA1 (A' + (len + n)) ltac:(lia)) as HACC. clear SHWA1.
  acc_chk 11 (A' + (len + n)) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; zstep; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: zstep.
  all: replace (A' + (len + n))%Z with (A' + len + n)%Z by lia.
  all: remember (A' + len + n)%Z as V eqn:EV.
  all: step; fix_lit_store.
  all: subst V.
  all: assert (BLK : rw_cells asegs m2 A' [CB (Z.to_nat (cap' + 1)) (firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs)])
    by (lazymatch type of BLKc with rw_cells _ _ _ [?c3; ?c4] =>
      pose proof (proj2 (rw_cells_app asegs m2 (A' + len) [CB (Z.to_nat n) src] [c3; c4])) as J1;
      cbn [cells_size csize Nat.add] in J1; rewrite Nat.add_0_r, Z2Nat.id in J1 by lia;
      specialize (J1 (conj PC2 BLKc)); cbn [app] in J1;
      pose proof (proj2 (rw_cells_app asegs m2 A' [CB (Z.to_nat len) (firstn (Z.to_nat len) bs)] [CB (Z.to_nat n) src; c3; c4])) as J2;
      cbn [cells_size csize Nat.add] in J2; rewrite Nat.add_0_r, Z2Nat.id in J2 by lia;
      specialize (J2 (conj BLKa J1)); cbn [app] in J2;
      pose proof (rw_cells_merge asegs m2 A' [] [CB (Z.to_nat len) (firstn (Z.to_nat len) bs); CB (Z.to_nat n) src; c3; c4] []) as M
    end;
    rewrite !app_nil_r in M; cbn [app cells_size csize cells_bytes cbytes Nat.add] in M;
    specialize (M J2);
    replace (Z.to_nat len + (Z.to_nat n + S (Z.to_nat (cap' - len - n) + 0)))%nat with (Z.to_nat (cap' + 1)) in M by lia;
    replace (firstn (Z.to_nat (cap' - len - n)) (skipn 1 (skipn (Z.to_nat n) (skipn (Z.to_nat len) bs)))) with (skipn (Z.to_nat (len + n + 1)) bs) in M
      by (rewrite !skipn_skipn; replace (1 + Z.to_nat n + Z.to_nat len)%nat with (Z.to_nat (len + n + 1)) by lia; symmetry; apply firstn_all2; rewrite length_skipn; lia);
    rewrite app_nil_r in M; exact M).
  all: clear PC2 BLKa BLKc.
  all: zstep.
  all: do 14 step.
  all: env_now AE0 MU WM; release_to q; step.
  all: apply evt_done; unfold isegM_post, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 15 eexists; split; [reflexivity|]; repeat (split; [eassumption|]); exact BLK.
Qed.

#[using="Type"] Lemma isegZ : forall (lo MB SRC A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < SRC < 2^64 -> 0 <= len <= cap -> cap + 8 <= 2^28 ->
  evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' MB (mbuf_cells A len cap))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz 0) (wz len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c404) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC A len cap ra q gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL ACC WK HS HLC HNC. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 112%nat ST.
  do 14 (step; fix_lit_store).
  step. step. step.
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC1.
  zstep. zstep. zstep. acc_chk0 20 (MB + 8) ACC1. step. step. lit_branch.
  step. zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. lit_branch.
  zstep. do 14 step. env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC. do 15 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). exact MBC.
Qed.
End W.
