(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AObj InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BIface U2BGlue InfBBase InfBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma leave_progress : forall cx st lf cf,
  sinv cx st lf cf -> 0 <= c_cin0 cx <= c_n cx -> c_n cx < 67108864 ->
  (c_n cx - c_cin0 cx <> c_n cx - t_cin st \/ t_out st <> c_osz cx - t_cout st) -> M2 cx st < M2e cx.
Proof.
  intros cx st lf cf (R & _ & P & _) C0 NR H. unfold IDefs.RNG in R. cbv zeta in R. unfold PROG in P. unfold M2, M2e, Wm in *.
  destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & _).
  destruct P as (P1 & P2 & P3). destruct P3 as [P3|[P3 _]]; lia.
Qed.
Lemma leave_wm : forall cx st lf cf, sinv cx st lf cf -> Wm cx st <= c_W0 cx.
Proof.
  intros cx st lf cf (R & _ & P & _). unfold IDefs.RNG in R. cbv zeta in R. unfold PROG, Wm in *.
  destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & _). destruct P as (P1 & _). lia.
Qed.
Lemma ainv_of_sinv : forall cx st lf cf, sinv cx st lf cf -> ainv cx st lf cf.
Proof. intros cx st lf cf (R & W & _ & M). split; [exact R| split; [exact W| exact M]]. Qed.

Lemma shr3_lin8 : forall X, 0 <= X -> X mod 8 = 0 -> exists q, Z.shiftr X 3 = q /\ 8 * q = X.
Proof. intros X H0 H8. exists (Z.shiftr X 3). split; [reflexivity|]. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section AI.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB0 F := (mkABlock (ABFake 0) F 64).

Lemma inf_client_outside : forall L RNG st LB m F FLG lo SP a,
  AHEAP AI L RNG st (FB0 F :: LB) m ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ablk F (F + 64) -> F mod 8 = 0 ->
  ablk FLG (FLG + 1) ->
  (forall b, In b (FB0 F :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG) ->
  ~ in_ranges CI FLG ->
  ATOP + 4096 <= lo -> lo <= SP ->
  aclient_addr CI LB SP a ->
  ~ (lo <= a < SP) /\ ~ (F <= a < F + 64) /\ ~ (Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + 8) /\ a <> FLG.
Proof.
  intros L RNG st LB m F FLG lo SP a AH LBH FH F8 GH GBL GCI LOC LOSP Ha.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP).
  { intros b Hb. apply (AI_block_bounds AI _ _ _ _ _ b AH). right. exact Hb. }
  assert (NFB : ~ In (FB0 F) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND as [|x l NI0 N3]. exact NI0. }
  assert (BLK : forall b, In b LB -> ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b).
  { intros b Hb.
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ (FB0 F) b AH ltac:(left; reflexivity) ltac:(right; exact Hb)
                  ltac:(intros E; apply NFB; rewrite E; exact Hb)) as D. cbn [ab_addr ab_size] in D. lia. }
  atop_facts.
  assert (SHB : KLS <= Z.shiftr F 3 + 2147450880 /\ Z.shiftr F 3 + 2147450880 + 8 <= 0x10007fff8000).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
  destruct Ha as [HSP|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  -
    split; [lia|]. split; [lia|]. split; [unfold KLS in *; lia|]. lia.
  -
    pose proof (AI_aci_img AI iv Hiv) as X. unfold AIMG_HI in *. split; [lia|]. split; [lia|]. split; [unfold KLS in *; lia|].
    intros ->. apply GCI. exists iv. split; [exact Hiv| exact Hr].
  -
    pose proof (BLK _ Hb) as D. pose proof (LBH _ Hb) as LB1. pose proof (BB _ Hb) as (B1 & B2 & B3).
    split; [lia|]. split; [lia|].
    split; [intros X; eapply (ablk_clear_band _ _ a LB1); [unfold KLS in *; lia| exact Hr]|].
    pose proof (GBL b ltac:(right; exact Hb)). lia.
  -
    assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia
        | pose proof (BB _ Hb') as BX; cbn [ab_addr ab_size] in BX; unfold AIMG_HI in *; lia]. }
    assert (OUTF : ~ (F <= a' < F + 64)).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); unfold AIMG_HI in *; lia|].
      pose proof (BLK _ Hb') as D. cbn [ab_addr ab_size] in D. lia. }
    pose proof (shad_in_band a' A47) as SB.
    split; [unfold KLS in *; lia|].
    split; [intros X; eapply (ablk_clear_band _ _ _ FH); [| exact X]; unfold KLS in *; lia|].
    split; [rewrite shad_div in *; unfold ASHOFF in *; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
            clear - A47 OUTF F8 FHa FHb; Z.div_mod_to_equations; lia|].
    intros X. apply (ablk_clear_band _ _ (shad a') GH); [unfold KLS in *; lia| lia].
Qed.


Lemma aheap_pres_f16arr : forall LB SP m m' A n f,
  aheap_pres CI LB SP m m' -> f16arr bsegs m A n f -> aclient_range CI LB SP A (2 * Z.of_nat n) -> f16arr bsegs m' A n f.
Proof.
  intros LB SP m m' A n f HP [HB HW] HR. unfold f16arr, u16arr. rewrite fws_length in *. split.
  - eapply aheap_pres_bytes_at; [exact HP| exact HB|]. rewrite u16s_length, fws_length.
    replace (Z.of_nat (2 * n)) with (2 * Z.of_nat n) by lia. exact HR.
  - eapply aheap_pres_wr_at; [exact HP| exact HW| exact HR].
Qed.
Lemma aheap_pres_f32arr : forall LB SP m m' A n f,
  aheap_pres CI LB SP m m' -> f32arr bsegs m A n f -> aclient_range CI LB SP A (4 * Z.of_nat n) -> f32arr bsegs m' A n f.
Proof.
  intros LB SP m m' A n f HP [HB HW] HR. unfold f32arr, u32arr. rewrite fws_length in *. split.
  - eapply aheap_pres_bytes_at; [exact HP| exact HB|]. rewrite u32s_length, fws_length.
    replace (Z.of_nat (4 * n)) with (4 * Z.of_nat n) by lia. exact HR.
  - eapply aheap_pres_wr_at; [exact HP| exact HW| exact HR].
Qed.
Lemma aheap_pres_f8arr : forall LB SP m m' A n f,
  aheap_pres CI LB SP m m' -> f8arr bsegs m A n f -> aclient_range CI LB SP A (Z.of_nat n) -> f8arr bsegs m' A n f.
Proof.
  intros LB SP m m' A n f HP [HB HW] HR. unfold f8arr, u8arr. rewrite length_map, length_seq in *. split.
  - eapply aheap_pres_bytes_at; [exact HP| exact HB|]. rewrite length_map, length_seq. exact HR.
  - eapply aheap_pres_wr_at; [exact HP| exact HW| exact HR].
Qed.
Lemma sh_pres_range : forall LB SP m m' s1 s2 f,
  aheap_pres CI LB SP m m' -> aclient_range CI LB SP s1 (s2 - s1) ->
  shadow_bytes m s1 s2 f -> shadow_bytes m' s1 s2 f.
Proof.
  intros LB SP m m' s1 s2 f HP HR SBm. pose proof SBm as (A & B & _).
  eapply shadow_bytes_agree; [exact SBm|]. intros s Hs.
  destruct (HP s ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR| lia])) as [E _]. exact E.
Qed.
Lemma shadow_bytes_magree : forall (P : Z -> Prop) m m' s1 s2 f,
  magree bsegs P m m' -> shadow_bytes m s1 s2 f -> (forall a, s1 <= a < s2 -> P a) -> shadow_bytes m' s1 s2 f.
Proof.
  intros P m m' s1 s2 f HP SB HR. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
  intros s Hs. destruct (HP s ltac:(lia) (HR s Hs)) as [E _]. exact E.
Qed.
Lemma acrS_fake : forall LB SP c F n lo hi, In (mkABlock (ABFake c) F n) LB -> F <= lo -> hi <= F + n -> aclient_range CI LB SP lo (hi - lo).
Proof. intros LB SP c F n lo hi H A B. left. right. right. exists c, F, n. split; [exact H| lia]. Qed.
Lemma acrS_block : forall LB SP b lo hi, In b LB -> ab_addr b <= lo -> hi <= ab_addr b + ab_size b -> aclient_range CI LB SP lo (hi - lo).
Proof. intros LB SP b lo hi H A B. right. left. exists b. split; [exact H| lia]. Qed.
Lemma acrS_stack : forall LB SP lo hi, SP <= lo -> hi <= 2^47 -> aclient_range CI LB SP lo (hi - lo).
Proof. intros LB SP lo hi A B. left. left. lia. Qed.
Lemma acr_ci_sh : forall LB SP iv s1 s2, In iv CI -> 8 * (s1 - 2147450880) >= fst iv -> 8 * (s2 - 2147450880) <= snd iv ->
  aclient_range CI LB SP s1 (s2 - s1).
Proof. intros LB SP iv s1 s2 Hiv A B. right. right. right. left. exists iv. split; [exact Hiv|]. unfold ASHOFF. lia. Qed.
Lemma acr_ci : forall LB SP iv lo hi, In iv CI -> fst iv <= lo -> hi <= snd iv -> aclient_range CI LB SP lo (hi - lo).
Proof. intros LB SP iv lo hi Hiv A B. left. right. left. exists iv. split; [exact Hiv| lia]. Qed.

End AI.
End CANSEC1.
