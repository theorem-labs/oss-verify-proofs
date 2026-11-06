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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Notation DFRA m q s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
  (rw_cells asegs m q [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

#[using="Type"] Lemma dsegZ : forall (lo MB A idx num cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 80 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A 0 cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' MB (mbuf_cells A 0 cap))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz idx) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_delete_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB A idx num cap ra q gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL SHWM.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, membuffer_delete_entryA in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 80%nat ST.
  walk_lia_to 0x8c8c8%Z.
  env_now AE0 MU WM. release_to q. step.
  apply evt_done. do 16 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Definition dsegA_post (lo MB A idx num len cap : Z) (bs : list byte) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' : word) (pc nsz : Z),
    ms' = MS (mkR x1 (wz (q + -80)) gp tp t0' t1' t2' (wz MB) (wz (MB + 8)) a0' a1' a2' a3' a4' a5' a6' a7'
                  (wz (MB + 16)) x19 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
                  (wz (len - num)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) s9 s10 s11 t3' t4' t5' t6')
             F (wz pc) fc None m' (seg_rom asegs)
    /\ munch [(A, A + (cap + 1)); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -80) /\ DFRA m' (q + -80) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
    /\ rw_cells asegs m' MB (mbuf_cells A len cap)
    /\ rw_cells asegs m' A [CB (Z.to_nat (cap + 1)) (del_bytesA bs idx num len)]
    /\ ( (pc = 0x8c86c /\ nsz = cap)
       \/ (pc = A0_realloc /\ x1 = wz 0x8c834 /\ a0' = wz A /\ a1' = wz (nsz + 1) /\ x19 = wz nsz /\ nsz = len - num + 5 /\ nsz < cap /\ 1 <= num) ).

Ltac dsegA_leaf :=
  apply evt_done; unfold dsegA_post, A0_realloc, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 20 eexists; split; [reflexivity|];
  repeat (split; [eassumption|]).

#[using="IC"] Lemma dsegA : forall (lo MB A idx num len cap : Z) (bs : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 80 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  1 <= len <= cap -> cap + 8 <= 2^28 -> 0 <= idx -> 0 <= num -> idx + num <= len ->
  rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs] -> shw m A (cap + 1) -> 0x609000 <= A -> A + (cap + 1) <= alloc_ceiling ->
  A mod 8 = 0 -> (MB + 32 <= A \/ A + (cap + 1) <= MB) ->
  evt asegs (dsegA_post lo MB A idx num len cap bs ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz idx) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_delete_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB A idx num len cap bs ra q gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL SHWM HLC HNC HI HN HIN BLK SHWA ALO AHI AAL DJM.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, membuffer_delete_entryA in *. unfold A0_RT_STACK in LO.
  a0_prologue AE0 [(A, A + (cap + 1)); (lo, q)]%Z m.
  assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; tauto).
  carve_frame 80%nat ST.
  walk_lia_to 0x8c79c%Z.
  replace (len <? len - (num + idx)) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z Z.add]. change ((-1) mod 18446744073709551616) with (Z.ones 64).
  rewrite (Z.land_comm (Z.ones 64)), Z.land_ones, Z.mod_small by lia.
  step.
  pose proof SHWA as SHWA1. shw_now SHWA1 MU. env_now AE0 MU WM.
  pose proof (u8arr_of_rw_cells asegs _ _ _ _ BLK) as ARR. clear BLK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memmove IC) with (D := A + idx) (S := A + idx + num) (n := len - (num + idx)) (U := A) (us := bs) (lo := lo);
      first [ rng_tac | exact ARR | exact MI | exact AE | exact ST | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHWA1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWA1)) | lia | lia | lia])
            | (rewrite ?LBS; lia) | (unfold A0_RT_STACK; lia) ]
    | post_call asegs mm ] end.
  clear SHWA1 AE.
  replace (A + idx - A) with idx in POST by lia. replace (A + idx + num - A) with (idx + num) in POST by lia.
  replace (len - (num + idx)) with (len - idx - num) in POST by lia.
  pose proof (rw_cells_of_u8arr asegs _ _ _ POST) as BLK1. clear POST.
  assert (LD : length (upd_bytes bs (Z.to_nat idx) (firstn (Z.to_nat (len - idx - num)) (skipn (Z.to_nat (idx + num)) bs))) = Z.to_nat (cap + 1)).
  { rewrite upd_bytes_length; [exact LBS|]. rewrite length_firstn, length_skipn. lia. }
  rewrite LD in BLK1.
  walk_lia_to 0x8c7c8%Z.
  cstep. if_cases KN; zify_cond KN.
  -
    walk_lia_to 0x8c86c%Z.
    dsegA_leaf. left. split; reflexivity.
  -
    walk_lia_to 0x8c7e8%Z.
    cstep. if_cases KS; zify_cond KS.
    +
      dsegA_leaf. left. split; reflexivity.
    + walk_lia_to 0x8c830%Z. step.
      dsegA_leaf. right. repeat split; try reflexivity; lia.
Qed.

Definition dsegS_post (lo MB B len nsz nl : Z) (q : Z) (gp tp : word) (s9 s10 s11 : word)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (fr : list cell)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (a0' a1' : word),
    ms' = MS (mkR (wz 0x8c834) (wz (q + -80)) gp tp t0 t1 t2 (wz MB) (wz (MB + 8)) a0' a1' a2 a3 a4 a5 a6 a7
                  (wz (MB + 16)) (wz nsz) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
                  (wz nl) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x8c86c) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -80) /\ rw_cells asegs m' (q + -80) fr
    /\ rw_cells asegs m' MB (mbuf_cells B len nsz).

#[using="Type"] Lemma dsegS : forall (lo MB A B len cap nsz nl : Z) (q : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (fr : list cell) m,
  stk asegs m lo (q + -80) -> alloc_ceiling <= lo -> lo <= q - 80 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -80) fr -> cells_size fr = 80%nat ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 -> 0 < B < 2^64 ->
  evt asegs (dsegS_post lo MB B len nsz nl q gp tp s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc fr m)
    (MS (mkR (wz 0x8c834) (wz (q + -80)) gp tp t0 t1 t2 (wz MB) (wz (MB + 8)) (wz B) a1 a2 a3 a4 a5 a6 a7
             (wz (MB + 16)) (wz nsz) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
             (wz nl) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c834) fc None m (seg_rom asegs)).
Proof.
  intros lo MB A B len cap nsz nl q gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc fr m.
  intros ST CLO LO QHI MI FR FRS MBC MBLO MBHI AL ACC WK HB. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8c86c%Z.
  apply evt_done. unfold dsegS_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). exact MBC.
Qed.

Definition nul_atA (bs : list byte) (nl : Z) : list byte := firstn (Z.to_nat nl) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (nl + 1)) bs.

Definition dsegM_post (lo MB A' nl cap' : Z) (bs2 : list byte) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' MB (mbuf_cells A' nl cap')
    /\ rw_cells asegs m' A' [CB (Z.to_nat (cap' + 1)) (nul_atA bs2 nl)].

#[using="Type"] Lemma dsegM : forall (lo MB A' lenX nl cap' : Z) (bs2 : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 x1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x19 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -80) -> alloc_ceiling <= lo -> lo <= q - 80 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  DFRA m (q + -80) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
  rw_cells asegs m MB (mbuf_cells A' lenX cap') -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  0 <= nl <= cap' -> cap' + 1 < 2^32 ->
  rw_cells asegs m A' [CB (Z.to_nat (cap' + 1)) bs2] -> shw m A' (cap' + 1) ->
  0x609000 <= A' -> A' + (cap' + 1) <= alloc_ceiling -> A' mod 8 = 0 -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB) ->
  evt asegs (dsegM_post lo MB A' nl cap' bs2 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (q + -80)) gp tp t0 t1 t2 (wz MB) (wz (MB + 8)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (MB + 16)) x19 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
             (wz nl) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c86c) fc None m (seg_rom asegs)).
Proof.
  intros lo MB A' lenX nl cap' bs2 ra q gp tp t0 t1 t2 s0 s1 x1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x19 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR MBC MBLO MBHI AL SHWM HNL HC32 BLK SHWA ALO AHI AAL DJM.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32); (A', A' + (cap' + 1)); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LBS : length bs2 = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; tauto).

  apply (rw_cells_split_CB asegs m A' [] (Z.to_nat (cap' + 1)) bs2 [] [Z.to_nat nl; 1%nat; Z.to_nat (cap' - nl)]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
    destruct (proj1 (rw_cells_app asegs m A' [c1] [c2; c3]) BLK) as [BLKa BLKb];
    cbn [cells_size csize] in BLKb; rewrite Nat.add_0_r, Z2Nat.id in BLKb by lia end.
  clear BLK.
  walk_lia_to 0x8c890%Z.
  pose proof (shw_win_ok _ _ _ SHWM) as WKM. unfold win_ok in WKM.
  pose proof SHWA as SHWA1. shw_now SHWA1 MU.
  pose proof (proj1 SHWA1 (A' + nl) ltac:(lia)) as HACC. clear SHWA1.
  acc_chk 11 (A' + nl) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  1: (step; step; lit_branch).
  2: (step; step; rewrite (sxb_small k) by lia; if_cases K3; zify_cond K3; [| exfalso; lia];
      zstep; zstep; if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia]).
  all: remember (A' + nl)%Z as V eqn:EV.
  all: step; fix_lit_store.
  all: subst V.
  all: assert (BLK : rw_cells asegs m1 A' [CB (Z.to_nat (cap' + 1)) (nul_atA bs2 nl)])
    by (lazymatch type of BLKb with rw_cells _ _ _ [?c2; ?c3] =>
          destruct (proj1 (rw_cells_app asegs m1 (A' + nl) [c2] [c3]) BLKb) as [B2 B3];
          cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in B3 end;
        unfold nul_atA;
        replace (skipn (Z.to_nat (nl + 1)) bs2) with (firstn (Z.to_nat (cap' - nl)) (skipn 1 (skipn (Z.to_nat nl) bs2)))
          by (rewrite skipn_skipn; replace (1 + Z.to_nat nl)%nat with (Z.to_nat (nl + 1)) by lia; apply firstn_all2; rewrite length_skipn; lia);
        eapply (rw_cells_join3 asegs m1 A' (Z.to_nat nl) _ _ (Z.to_nat (cap' - nl)) _ _ BLKa);
        [ rewrite Z2Nat.id by lia; exact B2 | rewrite Z2Nat.id by lia; exact B3 | lia ]).
  all: clear BLKa BLKb.
  all: walk_lia_to 0x8c8c8%Z.
  all: env_now AE0 MU WM; release_to q; step.
  all: apply evt_done; unfold dsegM_post, mbuf_cells, MEMBUF_DEF_SIZE_INC; do 16 eexists; split; [reflexivity|]; repeat (split; [eassumption|]); exact BLK.
Qed.
End W.
