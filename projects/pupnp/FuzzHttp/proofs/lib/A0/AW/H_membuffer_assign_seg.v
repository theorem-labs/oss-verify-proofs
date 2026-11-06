(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
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

Notation AFR m q s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
  (rw_cells asegs m q [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition asegA_post (lo MB SRC n A len cap : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
    (t0 t1 t2 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (x1 a0' a1' a2' a3' x24 x25 x26 : word) (pc nsz : Z),
    ms' = MS (mkR x1 (wz (q + -96)) gp tp t0 t1 t2 (wz MB) (wz n) a0' a1' a2' a3' a4 a5 a6 a7
                  (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3))
                  (wz (Z.shiftr (MB + 16) 3 + 2147450880)) x24 x25 x26 s11 t3 t4 t5 t6)
             F (wz pc) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -96)
    /\ AFR m' (q + -96) s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
    /\ rw_cells asegs m' MB (mbuf_cells A len cap)
    /\ ( (pc = 0x8c2d8 /\ nsz = cap /\ a1' = wz SRC /\ n <= cap)
       \/ (pc = A0_realloc /\ x1 = wz 0x8c29c /\ a0' = wz A /\ a1' = wz (nsz + 1) /\ x24 = wz SRC
           /\ x25 = wz (Z.shiftr MB 3 + 2147450880) /\ x26 = wz nsz /\ n <= nsz /\ nsz <= cap + n + 5 /\ 0 <= nsz) ).

Ltac asegA_leaf :=
  apply evt_done; unfold asegA_post, A0_realloc, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 11 eexists; split; [reflexivity|];
  repeat (split; [eassumption|]).

#[using="Type"] Lemma asegA : forall (lo MB SRC n A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 96 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < SRC < 2^64 -> 0 <= len <= cap -> 0 <= n -> cap + n + 8 <= 2^28 -> 0 <= A < 2^64 ->
  evt asegs (asegA_post lo MB SRC n A len cap ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 t0 t1 t2 a4 a5 a6 a7 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_assign_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A len cap ra q gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL ACC WK HS HLC HN HNC HA. unfold membuffer_assign_entryA. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 96%nat ST.
  do 13 (step; fix_lit_store).
  zstep. step. step. step. zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC1.
  zstep. zstep. zstep. acc_chk0 21 (MB + 8) ACC1. step. step. lit_branch.
  zstep. zstep. zstep. acc_chk0 23 (MB + 16) ACC1. step. step. lit_branch.
  step. step. zstep.
  zstep. if_cases K1; zify_cond K1.
  -
    zstep. if_cases K2; zify_cond K2.
    +
      asegA_leaf. left. repeat split; try reflexivity; lia.
    +
      zstep. zstep. zstep. acc_chk0 13 (MB + 24) ACC1. step. step. lit_branch.
      step. zstep. zstep. if_cases K3; zify_cond K3.
      * zstep. zstep. acc_chk0 25 MB ACC1. step. step. lit_branch.
        zstep. step. zstep. step.
        asegA_leaf. right. repeat split; try reflexivity; lia.
      * zstep. zstep. zstep. acc_chk0 25 MB ACC1. step. step. lit_branch.
        zstep. step. zstep. step.
        asegA_leaf. right. repeat split; try reflexivity; lia.
  -
    zstep. zstep. zstep. acc_chk0 12 (MB + 24) ACC1. step. step. lit_branch.
    step. zstep. zstep. if_cases K3; zify_cond K3.
    + asegA_leaf. left. repeat split; try reflexivity; lia.
    + zstep. zstep. zstep. acc_chk0 25 MB ACC1. step. step. lit_branch.
      zstep. step. zstep. step.
      asegA_leaf. right. repeat split; try reflexivity; lia.
Qed.

Definition asegS_post (lo MB SRC n B len nsz : Z) (q : Z) (gp tp : word) (x21 x22 x23 x25 : word)
    (t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (fr : list cell)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (a0' a2' : word),
    ms' = MS (mkR (wz 0x8c29c) (wz (q + -96)) gp tp t0 t1 t2 (wz MB) (wz n) a0' (wz SRC) a2' a3 a4 a5 a6 a7
                  (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) x21 x22 x23 (wz SRC) x25 (wz nsz) s11 t3 t4 t5 t6)
             F (wz 0x8c2d8) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -96) /\ rw_cells asegs m' (q + -96) fr
    /\ rw_cells asegs m' MB (mbuf_cells B len nsz).

#[using="Type"] Lemma asegS : forall (lo MB SRC n A B len cap nsz : Z) (q : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (fr : list cell) m,
  stk asegs m lo (q + -96) -> alloc_ceiling <= lo -> lo <= q - 96 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -96) fr -> cells_size fr = 96%nat ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < B < 2^64 ->
  evt asegs (asegS_post lo MB SRC n B len nsz q gp tp x21 x22 (wz (Z.shiftr (MB + 16) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
               t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 F fc fr m)
    (MS (mkR (wz 0x8c29c) (wz (q + -96)) gp tp t0 t1 t2 (wz MB) (wz n) (wz B) a1 a2 a3 a4 a5 a6 a7
             (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) x21 x22 (wz (Z.shiftr (MB + 16) 3 + 2147450880)) (wz SRC)
             (wz (Z.shiftr MB 3 + 2147450880)) (wz nsz) s11 t3 t4 t5 t6)
        F (wz 0x8c29c) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A B len cap nsz q gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 s11 t3 t4 t5 t6 F fc fr m.
  intros ST CLO LO QHI MI FR FRS MBC MBLO MBHI AL ACC WK HB. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K; [| exfalso; lia].
  acc_chk0 25 MB ACC. step. step. lit_branch.
  step. fix_lit_store.
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(unfold win_ok in WK; app_ivs_tac)) as ACC1.
  acc_chk0 23 (MB + 16) ACC1. step. step. lit_branch.
  zstep. step. fix_lit_store.
  apply evt_done. unfold asegS_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). exact MBC.
Qed.

Definition asegM_post (lo MB A' n cap' : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list ivl) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' MB (mbuf_cells A' n cap').

#[using="Type"] Lemma asegM0 : forall (lo MB SRC A' len' cap' : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 x1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 x24 x25 x26 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -96) -> alloc_ceiling <= lo -> lo <= q - 96 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  AFR m (q + -96) s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
  rw_cells asegs m MB (mbuf_cells A' len' cap') -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 ->
  evt asegs (asegM_post lo MB A' 0 cap' ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(MB, MB + 32); (lo, q)] m)
    (MS (mkR x1 (wz (q + -96)) gp tp t0 t1 t2 (wz MB) (wz 0) a0 (wz SRC) a2 a3 a4 a5 a6 a7
             (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3))
             (wz (Z.shiftr (MB + 16) 3 + 2147450880)) x24 x25 x26 s11 t3 t4 t5 t6)
        F (wz 0x8c2d8) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC A' len' cap' ra q gp tp t0 t1 t2 s0 s1 x1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 x24 x25 x26 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR MBC MBLO MBHI AL ACC. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. lit_branch.
  acc_chk0 21 (MB + 8) ACC. step. step. lit_branch.
  step. fix_lit_store.
  do 13 step. env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold asegM_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. do 15 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). exact MBC.
Qed.

#[using="IC"] Lemma asegM1 : forall (lo MB SRC n A' len' cap' : Z) (src bs' : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 x1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 x24 x25 x26 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -96) -> alloc_ceiling <= lo -> lo <= q - 96 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  AFR m (q + -96) s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
  rw_cells asegs m MB (mbuf_cells A' len' cap') -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  shw m MB 32 ->
  1 <= n <= cap' -> cap' + 1 < 2^32 ->
  rw_cells asegs m A' [CB (Z.to_nat (cap' + 1)) bs'] -> shw m A' (cap' + 1) ->
  0x609000 <= A' -> A' + (cap' + 1) <= alloc_ceiling -> A' mod 8 = 0 ->
  (MB + 32 <= A' \/ A' + (cap' + 1) <= MB) ->
  bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> shw m SRC n ->
  (SRC + n <= alloc_ceiling \/ (q <= SRC /\ SRC + n < 2^47)) -> (SRC + n <= MB \/ MB + 32 <= SRC) -> (SRC + n <= A' \/ A' + (cap' + 1) <= SRC) ->
  evt asegs (fun ms' => exists bs'', asegM_post lo MB A' n cap' ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                          [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)] m ms'
                        /\ (exists m', ms_mem ms' = m' /\ rw_cells asegs m' A' [CB (Z.to_nat (cap' + 1)) bs''])
                        /\ firstn (Z.to_nat (n + 1)) bs'' = src ++ [Z_to_bv 8 0])
    (MS (mkR x1 (wz (q + -96)) gp tp t0 t1 t2 (wz MB) (wz n) a0 (wz SRC) a2 a3 a4 a5 a6 a7
             (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3))
             (wz (Z.shiftr (MB + 16) 3 + 2147450880)) x24 x25 x26 s11 t3 t4 t5 t6)
        F (wz 0x8c2d8) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A' len' cap' src bs' ra q gp tp t0 t1 t2 s0 s1 x1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 x24 x25 x26 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR MBC MBLO MBHI AL SHWM HN HC32 BLK SHWA AHI ACE AAL DJM SRCB LEN SHWS SLO DJS DJA.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *. unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BB.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. acc_chk0 22 MB (proj1 SHWM). step. step. lit_branch.
  step. zstep. step.
  apply (rw_cells_split_CB asegs m A' [] (Z.to_nat (cap' + 1)) bs' [] [Z.to_nat n; Z.to_nat (cap' + 1 - n)]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2] =>
    destruct (proj1 (rw_cells_app asegs m A' [c1] [c2]) BLK) as [BLK1 BLK2] end. clear BLK.
  cbn [cells_size csize] in BLK2. rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
  pose proof (shw_win_ok _ _ _ SHWM) as WKM. unfold win_ok in WKM.
  pose proof SHWA as SHWA1. pose proof SHWS as SHWS1. shw_now SHWA1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memcpy IC) with (D := A') (S := SRC) (n := n) (lo := lo) (src := src);
      first [ rng_tac | exact BLK1 | exact SRCB | exact LEN | exact MI | exact AE | exact ST | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHWA1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWA1)) | lia | lia | lia])
            | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1))
            | (split; [exact (proj2 (proj2 SHWS1))| split; lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
    | post_call asegs mm ] end.
  clear SHWA1 SHWS1 SHR.
  step. zstep. zstep. zstep.
  pose proof SHWA as SHWA1. shw_now SHWA1 MU.
  pose proof (proj1 SHWA1 (A' + n) ltac:(lia)) as HACC. clear SHWA1.
  acc_chk 11 (A' + n) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; zstep; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: apply (rw_cells_split_CB asegs _ (A' + n) [] (Z.to_nat (cap' + 1 - n)) _ [] [1%nat; Z.to_nat (cap' - n)]) in BLK2; [| cbn; lia].
  all: cbn [app mk_CB_cells] in BLK2.
  all: lazymatch type of BLK2 with rw_cells _ ?mm _ [?c1; ?c2] =>
         destruct (proj1 (rw_cells_app asegs mm (A' + n) [c1] [c2]) BLK2) as [BLK2a BLK2b] end; clear BLK2.
  all: cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in BLK2b.
  all: remember (A' + n)%Z as V eqn:EV.
  all: step; fix_lit_store.
  all: subst V.
  all: pose proof SHWM as SHWM1; shw_now SHWM1 MU.
  all: acc_chk0 21 (MB + 8) (proj1 SHWM1); clear SHWM1.
  all: step; step; lit_branch.
  all: step; fix_lit_store.
  all: do 13 step.
  all: env_now AE0 MU WM; release_to q; step.
  all: change (Z.of_nat 1) with 1 in BLK2b.
  all: pose proof (rw_cells_join3 asegs _ A' _ _ _ _ _ (Z.to_nat (cap' + 1))
                    ltac:(eassumption) ltac:(rewrite Z2Nat.id by lia; exact BLK2a) ltac:(rewrite Z2Nat.id by lia; exact BLK2b) ltac:(lia)) as BLKF.
  all: apply evt_done; eexists; split; [| split].
  all: try (unfold asegM_post, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 15 eexists; split; [reflexivity|]; repeat (split; [eassumption|]); exact MBC).
  all: try (eexists; split; [reflexivity| exact BLKF]).
  all: rewrite firstn_app, firstn_all2 by lia; replace (Z.to_nat (n + 1) - length src)%nat with 1%nat by lia; reflexivity.
Qed.
End W.
