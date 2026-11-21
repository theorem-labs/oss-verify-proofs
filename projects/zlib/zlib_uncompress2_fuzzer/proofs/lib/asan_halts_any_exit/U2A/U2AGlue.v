(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma shadE : forall a, shad a = Z.shiftr a 3 + 2147450880.
Proof. intros a. unfold shad, ASHOFF. lia. Qed.

Lemma ablock_sh0 : forall m A n, ablock_shadow m A n -> n mod 8 = 0 -> 0 <= n -> 0 <= A -> A + n <= 2^47 ->
  shadow_bytes m (Z.shiftr A 3 + 2147450880) (Z.shiftr A 3 + 2147450880 + n / 8) (fun _ => 0).
Proof.
  intros m A n H N8 N0 A0 AN. rewrite <- shadE.
  assert (0 <= shad A) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  split; [lia|]. split. { rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  intros s Hs. specialize (H (s - shad A) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)).
  replace (shad A + (s - shad A)) with s in H by lia. rewrite H. f_equal. f_equal.
  destruct (Z.leb_spec (8 * (s - shad A) + 8) n); [reflexivity|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

Section AI.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Lemma fake_sh_pres : forall LB SP m m' c F n X N f,
  aheap_pres CI LB SP m m' -> In (mkABlock (ABFake c) F n) LB ->
  X mod 8 = 0 -> 0 <= X -> F <= X -> X + 8 * N <= F + n -> X + 8 * N <= 2^47 ->
  shadow_bytes m (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N) f ->
  shadow_bytes m' (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N) f.
Proof.
  intros LB SP m m' c F n X N f HP HIN X8 X0 FX XN X47 (A & B & H). split; [exact A|]. split; [exact B|].
  intros s Hs. rewrite <- (H s Hs).
  rewrite Z.shiftr_div_pow2 in Hs by lia. change (2^3) with 8 in Hs.
  set (a' := 8 * (s - 2147450880)).
  assert (E : s = shad a') by (subst a'; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  rewrite E. apply (aheap_pres_shadow CI LB SP m m' a' HP).
  - right. right. exists c, F, n. split; [exact HIN|]. subst a'. Z.div_mod_to_equations. lia.
  - rewrite <- E. lia.
Qed.

Lemma fake_shwr_pres : forall LB SP m m' c F n,
  aheap_pres CI LB SP m m' -> In (mkABlock (ABFake c) F n) LB -> F mod 8 = 0 -> 0 <= F -> n mod 8 = 0 -> 0 <= n ->
  wr_at asegs m (shad F) (n / 8) -> wr_at asegs m' (shad F) (n / 8).
Proof.
  intros LB SP m m' c F n HP HIN F8 F0 N8 N0 W. eapply aheap_pres_wr_at; [exact HP| exact W|].
  right. right. right. right. exists c, F, n. split; [exact HIN|].
  rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Lemma client_agree_munch : forall LB SP WR W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ in_ranges WR a -> outside W a) ->
  client_agree AI LB SP WR m m'.
Proof.
  intros LB SP WR W m m' MU WM H a Ha [HC HN].
  exact (magree_of_munch asegs W m m' MU WM a Ha (H a Ha HC HN)).
Qed.
Lemma client_agree_pres : forall LB LB' SP SP' WR m m',
  aheap_pres CI LB' SP' m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') -> client_agree AI LB SP WR m m'.
Proof.
  intros LB LB' SP SP' WR m m' HP HS HL a Ha [HC _].
  exact (aheap_pres_weaken CI LB' LB SP' SP m m' HP HS HL a Ha HC).
Qed.
Lemma client_agree_trans : forall LB SP WR m1 m2 m3,
  client_agree AI LB SP WR m1 m2 -> client_agree AI LB SP WR m2 m3 -> client_agree AI LB SP WR m1 m3.
Proof. intros LB SP WR m1 m2 m3. apply magree_trans. Qed.

Lemma aclient_addr_cases : forall L RNG st LB m SP a,
  AHEAP AI L RNG st LB m -> aclient_addr CI LB SP a ->
  SP <= a \/ a < AIMG_HI \/ (exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b) \/ KLS <= a < 0x10007fff8000.
Proof.
  intros L RNG st LB m SP a AH [H|[(iv & Hiv & H)|[H|(a' & Ha' & ->)]]].
  - left. lia.
  - right. left. pose proof (AI_aci_img AI iv Hiv). lia.
  - right. right. left. exact H.
  - right. right. right. atop_facts.
    assert (0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & X)|(c & A & n & Hb & X)]].
      - lia.
      - pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as (B1 & B2 & B3). cbn in B1, B2, B3. unfold AIMG_HI in *. lia. }
    pose proof (shad_in_band a' H0). unfold KLS in *. lia.
Qed.

Lemma acr_stack : forall LB lo hi, ATOP + 4096 <= lo -> hi <= 2^47 -> aclient_range CI LB (ATOP + 4096) lo (hi - lo).
Proof. intros. left. left. lia. Qed.
Lemma acr_block : forall LB b lo hi, In b LB -> ab_addr b <= lo -> hi <= ab_addr b + ab_size b -> aclient_range CI LB (ATOP + 4096) lo (hi - lo).
Proof. intros LB b lo hi H A B. right. left. exists b. split; [exact H| lia]. Qed.
Lemma acr_fake : forall LB c F n lo hi, In (mkABlock (ABFake c) F n) LB -> F <= lo -> hi <= F + n -> aclient_range CI LB (ATOP + 4096) lo (hi - lo).
Proof. intros LB c F n lo hi H A B. left. right. right. exists c, F, n. split; [exact H| lia]. Qed.
Lemma acr_fake_sh : forall LB c F n X N,
  In (mkABlock (ABFake c) F n) LB -> X mod 8 = 0 -> 0 <= X -> F <= X -> X + 8 * N <= F + n ->
  aclient_range CI LB (ATOP + 4096) (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N - (Z.shiftr X 3 + 2147450880)).
Proof.
  intros LB c F n X N H X8 X0 A B. right. right. right. right. exists c, F, n. split; [exact H|].
  unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma in_hb_ids : forall LB p A n, In (HB p A n) LB -> In p (hb_ids LB).
Proof.
  intros LB p A n H. unfold hb_ids. apply in_flat_map. exists (HB p A n). split; [exact H| left; reflexivity].
Qed.
Lemma hb_same_id : forall LB p A n A' n', List.NoDup (hb_ids LB) -> In (HB p A n) LB -> In (HB p A' n') LB -> HB p A n = HB p A' n'.
Proof.
  induction LB as [|b LB IH]; intros p A n A' n' ND H1 H2; [destruct H1|].
  unfold hb_ids in ND. cbn [flat_map] in ND. fold (hb_ids LB) in ND.
  destruct H1 as [->|H1], H2 as [E2|H2].
  - exact E2.
  - cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. exfalso. apply NI. eapply in_hb_ids; exact H2.
  - subst b. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. exfalso. apply NI. eapply in_hb_ids; exact H1.
  - apply (IH p A n A' n'); [| exact H1| exact H2]. destruct (ab_kind b); [cbn [app] in ND; apply NoDup_cons_iff in ND; tauto| exact ND].
Qed.
Lemma in_lb_remove : forall p LB b, In b LB -> ab_kind b <> ABHeap p -> In b (lb_remove p LB).
Proof.
  intros p LB b H NE. induction LB as [|c LB IH]; [destruct H|].
  unfold lb_remove in *. rewrite filter_cons. destruct (decide _) as [Y|N].
  - destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H].
  - destruct H as [->|H]; [| apply IH; exact H]. exfalso. apply N.
    destruct b as [[q|cc] bA bn]; cbn [ab_kind abkind_eqb negb] in *; [| exact I].
    destruct (N.eqb_spec q p) as [->|]; [exfalso; apply NE; reflexivity| exact I].
Qed.
Lemma lb_remove_sub : forall p LB b, In b (lb_remove p LB) -> In b LB.
Proof.
  intros p LB b. induction LB as [|c LB IH]; intros H; [exact H|].
  unfold lb_remove in *. rewrite filter_cons in H. destruct (decide _) as [Y|N].
  - destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H].
  - right. apply IH. exact H.
Qed.

Lemma uchain_munch : forall W m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr -> munch W m m' ->
  (forall a, frame - 16 <= a < top -> outside W a) -> 0 <= frame - 16 -> top <= 2^64 ->
  uchain m' top pc prev frame k tr.
Proof.
  intros W m m' top pc prev frame k tr U MU H F0 T. eapply uchain_frame; [exact U|].
  intros a Ha. specialize (MU (wa a)). unfold wa in *. rewrite Z_to_bv_unsigned in MU.
  rewrite bv_wrap_small in MU by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  apply MU. apply H. exact Ha.
Qed.

End AI.
End CANSEC1.
