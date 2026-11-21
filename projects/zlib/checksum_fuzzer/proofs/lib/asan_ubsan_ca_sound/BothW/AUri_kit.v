(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg AProto AMalloc_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Notation MA := (Monad.M APS).

Section CANSEC1. Context {rc : runConstT}.
Definition implMA {A} (RNG : footprint) (c : MA A) (s : APS)
    (Q : A -> APS -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.

Section ImplMA.

Lemma implMA_fold : forall {A} RNG (c : MA A) s Q ms,
  implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMA RNG c s Q ms.
Proof. intros. exact H. Qed.
Lemma implMA_unfold : forall {A} RNG (c : MA A) s Q ms,
  implMA RNG c s Q ms -> implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.
Proof. intros. exact H. Qed.

Lemma implMA_ret : forall {A} RNG (a : A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q a s RNG) ms -> implMA RNG (mret a) s Q ms.
Proof. intros A RNG a s Q ms H. unfold implMA, mret. apply implF_ret_ok. exact H. Qed.

Lemma implMA_unr : forall {A} RNG (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG (munr (A:=A)) s Q ms.
Proof. intros. unfold implMA, munr. apply implF_ret_unr. Qed.

Lemma implMA_bind : forall {A B} RNG (ma : MA A) (f : A -> MA B) (s : APS)
    (Q1 : A -> APS -> footprint -> machine_state -> Prop) (Q : B -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG ma s Q1 ms ->
  (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMA RNG' (f a) s' Q ms') ->
  implMA RNG (mbind ma f) s Q ms.
Proof.
  intros A B RNG ma f s Q1 Q ms Hm Hf. unfold implMA, mbind in *.
  eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implMA_mono : forall {A} RNG (ma : MA A) (s : APS) (Q Q' : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG ma s Q ms -> (forall a s' RNG' ms', Q a s' RNG' ms' -> Q' a s' RNG' ms') -> implMA RNG ma s Q' ms.
Proof.
  intros A RNG ma s Q Q' ms H HQ. unfold implMA in *. eapply implF_epost_mono; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
Qed.

Lemma implMA_evtF : forall {A} RNG (ma : MA A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) P ms,
  evtF bsegs RNG P ms -> (forall ms', P ms' -> implMA RNG ma s Q ms') -> implMA RNG ma s Q ms.
Proof. intros A RNG ma s Q P ms H K. unfold implMA in *. eapply implF_evtF; eauto. Qed.

Lemma implMA_from_evtF : forall {A} RNG (ma : MA A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (fun ms' => implMA RNG ma s Q ms') ms -> implMA RNG ma s Q ms.
Proof. intros A RNG ma s Q ms H. eapply implMA_evtF; [exact H|]. cbv beta. intros ms' H'; exact H'. Qed.


Lemma implMA_get : forall RNG (s : APS) (Q : APS -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q s s RNG) ms -> implMA RNG mget s Q ms.
Proof. intros. unfold implMA, mget. apply implF_ret_ok. exact H. Qed.
Lemma implMA_upd : forall RNG f (s : APS) (Q : unit -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q tt (f s) RNG) ms -> implMA RNG (mupd f) s Q ms.
Proof. intros. unfold implMA, mupd. apply implF_ret_ok. exact H. Qed.



Lemma implMA_alift : forall {R} RNG (t : AM R) (s : APS) (Q : R -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP t) (epostF (fun r RNG' ms' => Q r s RNG' ms')) ms ->
  implMA RNG (alift t) s Q ms.
Proof.
  intros R RNG t s Q ms AT H. unfold implMA, alift. rewrite AT. eapply implF_ebind; [exact H|].
  intros r RNG' ms' HQ. apply implF_ret_ok. cbn. apply evtF_done. exact HQ.
Qed.

Lemma implMA_amalloc : forall RNG n (s : APS) (Q : option AsanCtrl.aptr -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP (AsanCtrl.amalloc ATOP (aps_resv s) (aps_m s) n))
        (epostF (fun (r : astate * option AsanCtrl.aptr) RNG' ms' => Q (snd r) (aset_m (fst r) s) RNG' ms')) ms ->
  implMA RNG (amalloc_M n) s Q ms.
Proof.
  intros RNG n s Q ms AT H. unfold amalloc_M.
  eapply (implMA_bind RNG mget _ s (fun s0 s' RNG' ms' => s0 = s /\ s' = s /\ RNG' = RNG /\ ms' = ms)).
  { apply implMA_get. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros s0 s' RNG1 ms1 (-> & -> & -> & ->).
  eapply (implMA_bind RNG (alift _) _ s (fun x s' RNG' ms' => s' = s /\ Q (snd x) (aset_m (fst x) s) RNG' ms')).
  { apply implMA_alift; [exact AT|]. rewrite AT. eapply implF_epost_mono; [exact H|]. cbv beta. intros; split; [reflexivity| assumption]. }
  cbv beta. intros x s2 RNG2 ms2 [-> H2].
  eapply (implMA_bind RNG2 (mupd _) _ s (fun _ s' RNG' ms' => s' = aset_m (fst x) s /\ RNG' = RNG2 /\ ms' = ms2)).
  { apply implMA_upd. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros [] s3 RNG3 ms3 (-> & -> & ->).
  apply implMA_ret. apply evtF_done. exact H2.
Qed.

Lemma implMA_afree : forall RNG p (s : APS) (Q : unit -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP (AsanCtrl.afree (aps_m s) (Some p)))
        (epostF (fun (st' : astate) RNG' ms' => Q tt (aset_m st' s) RNG' ms')) ms ->
  implMA RNG (afree_M p) s Q ms.
Proof.
  intros RNG p s Q ms AT H. unfold afree_M.
  eapply (implMA_bind RNG mget _ s (fun s0 s' RNG' ms' => s0 = s /\ s' = s /\ RNG' = RNG /\ ms' = ms)).
  { apply implMA_get. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros s0 s' RNG1 ms1 (-> & -> & -> & ->).
  eapply (implMA_bind RNG (alift _) _ s (fun x s' RNG' ms' => s' = s /\ Q tt (aset_m x s) RNG' ms')).
  { apply implMA_alift; [exact AT|]. eapply implF_epost_mono; [exact H|]. cbv beta. intros; split; [reflexivity| assumption]. }
  cbv beta. intros x s2 RNG2 ms2 [-> H2].
  apply implMA_upd. apply evtF_done. exact H2.
Qed.


Definition aps_rest (s : APS) := (aps_so s, aps_resv s, aps_atop s).
Lemma aps_so_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_so s' = aps_so s.
Proof. intros s' s H. exact (f_equal (fun x => fst (fst x)) H). Qed.
Lemma aps_resv_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_resv s' = aps_resv s.
Proof. intros s' s H. exact (f_equal (fun x => snd (fst x)) H). Qed.
Lemma aps_atop_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_atop s' = aps_atop s.
Proof. intros s' s H. exact (f_equal snd H). Qed.
Definition aps_ok (L : alayout) (s : APS) : Prop := aresv_ok L (aps_resv s) /\ aps_atop s = ATOP.
Lemma aps_ok_rest : forall L s' s, aps_rest s' = aps_rest s -> aps_ok L s -> aps_ok L s'.
Proof. intros L s' s H [R A]. split; [rewrite (aps_resv_of_rest _ _ H); exact R| rewrite (aps_atop_of_rest _ _ H); exact A]. Qed.

End ImplMA.



Lemma ablock_shadow_block : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> shadow_block m A n.
Proof.
  intros m A n H HA A0 N0 AN. split; [exact HA|]. split; [exact A0|]. split; [exact N0|]. split; [exact AN|].
  split. { rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  split. { rewrite shad_div, nshad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  intros s Hs. unfold ablock_shadow in H.
  specialize (H (s - shad A) ltac:(lia) ltac:(rewrite nshad_div in Hs; Z.div_mod_to_equations; lia)).
  replace (shad A + (s - shad A)) with s in H by lia. rewrite H. reflexivity.
Qed.

Lemma ablock_unpoisoned : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof. intros. apply shadow_block_unpoisoned. apply ablock_shadow_block; assumption. Qed.


Definition hull_lo (A : Z) : Z := A - A mod 64 - 64.
Definition hull_hi (A n : Z) : Z := A + n + (- (A + n)) mod 64 + 64.

Lemma hull_props : forall A n, 0 <= n ->
  hull_lo A <= A /\ A + n <= hull_hi A n /\ hull_lo A mod 64 = 0 /\ hull_hi A n mod 64 = 0
  /\ A - 128 < hull_lo A /\ hull_hi A n < A + n + 128.
Proof. intros A n Hn. unfold hull_lo, hull_hi. Z.div_mod_to_equations. lia. Qed.

Lemma hull_in_arena : forall A n RLO RHI, 0 <= n ->
  RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI ->
  RLO <= hull_lo A /\ hull_hi A n <= RHI.
Proof. intros A n RLO RHI Hn R1 R2 R3 R4. unfold hull_lo, hull_hi. Z.div_mod_to_equations. lia. Qed.

Lemma shad_sub_range : forall RLO RHI lo hi,
  RLO <= lo -> lo <= hi -> hi <= RHI -> RLO mod 8 = 0 -> lo mod 8 = 0 -> hi mod 8 = 0 -> RHI mod 8 = 0 ->
  shad RLO <= shad lo /\ shad hi <= shad RHI /\ shad lo <= shad hi
  /\ shad hi - shad lo = (hi - lo) / 8 /\ shad RHI - shad RLO = (RHI - RLO) / 8.
Proof. intros. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

Lemma shlen_div : forall L, shlen L = L / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma wr_at_sub : forall m s n s' n', wr_at bsegs m s n -> s <= s' -> 0 <= n' -> s' + n' <= s + n -> wr_at bsegs m s' n'.
Proof.
  intros m s n s' n' (A & B & W) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (s' + i) with (s + (s' - s + i)) by lia. apply W. lia.
Qed.

Lemma block_hull : forall (RNG : footprint) m A n RLO RHI,
  0 <= n -> RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI -> 64 <= A ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at bsegs m (shad RLO) (shlen (RHI - RLO)) ->
  rng RNG (shad (hull_lo A)) (shad (hull_hi A n) - shad (hull_lo A))
  /\ wr_at bsegs m (shad (hull_lo A)) (shad (hull_hi A n) - shad (hull_lo A))
  /\ hull_lo A <= A /\ A + n <= hull_hi A n /\ hull_lo A mod 64 = 0 /\ hull_hi A n mod 64 = 0 /\ 0 <= hull_lo A /\ hull_hi A n <= RHI.
Proof.
  intros RNG m A n RLO RHI Hn R1 R2 R3 R4 A64 RR WR.
  pose proof (hull_props A n Hn) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (hull_in_arena A n RLO RHI Hn R1 R2 R3 R4) as [Q1 Q2].
  pose proof (shad_sub_range RLO RHI (hull_lo A) (hull_hi A n) Q1 ltac:(lia) Q2
                ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
    as (S1 & S2 & S3 & S4 & S5).
  rewrite shlen_div in RR, WR.
  split; [| split; [| repeat split; lia]].
  - eapply rng_sub'; [exact RR| lia].
  - eapply wr_at_sub; [exact WR| lia| lia| lia].
Qed.


Section AllocCalls.
Variable AI : AMallocIface.









Lemma aheap_pres_of_munch : forall CI LB SP W m m',
  munch W m m' -> wmono bsegs m m' ->
  (forall a, aclient_addr CI LB SP a -> outside W a) ->
  aheap_pres CI LB SP m m'.
Proof.
  intros CI LB SP W m m' MU WM HO a Ha Hc. split; [apply MU; rewrite wa_unsigned by lia; apply HO; exact Hc| intros Hw; apply WM; exact Hw].
Qed.

Lemma aheap_pres_stack_writes : forall (CI : list (Z * Z)) L RNG st LB m0 W m m' SP lo,
  AHEAP AI L RNG st LB m0 ->
  (forall b, In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP) ->
  (forall iv, In iv CI -> snd iv <= AIMG_HI) ->
  munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= SP) W -> ATOP <= lo ->
  aheap_pres CI LB SP m m'.
Proof.
  intros CI L RNG st LB m0 W m m' SP lo AH BB CIB MU WM FW CL.
  assert (OUT : forall a, a < lo \/ SP <= a -> outside W a).
  { clear MU WM. intros a HA. induction W as [|[wlo whi] W IH]; [exact I|]. cbn. inversion FW as [|x l [F1 F2] FW']; subst. cbn in F1, F2.
    split; [lia| apply IH; exact FW']. }
  eapply aheap_pres_of_munch; [exact MU| exact WM|].
  intros a Hc. apply OUT. unfold AIMG_HI in *.
  assert (HA : a < lo \/ SP <= a).
  { destruct Hc as [H|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - right; lia.
    - left. pose proof (CIB iv Hiv). lia.
    - left. pose proof (BB b Hb). lia.
    - left. rewrite shad_div. unfold ASHOFF.
      assert (A47 : a' < 2^47) by (destruct Ha' as [H|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); lia| pose proof (BB _ Hb); cbn in *; lia]).
      clear - A47 CL. Z.div_mod_to_equations. lia. }
  exact HA.
Qed.

End AllocCalls.



Lemma lb_remove_notin : forall p LB, ~ In p (hb_ids LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros NI; [reflexivity|].
  unfold lb_remove in *. rewrite filter_cons. unfold hb_ids in NI. cbn [flat_map] in NI. rewrite in_app_iff in NI.
  destruct (decide _) as [Y|N].
  - f_equal. apply IH. intros H; apply NI; right; exact H.
  - exfalso. apply N. destruct b as [[q|c] bA bn]; cbn [ab_kind abkind_eqb negb] in *; [| exact I].
    destruct (N.eqb_spec q p); [| exact I]. exfalso. apply NI. left. left. exact e.
Qed.

Lemma lb_remove_headA : forall p A n LB, List.NoDup (hb_ids (HB p A n :: LB)) -> lb_remove p (HB p A n :: LB) = LB.
Proof.
  intros p A n LB ND. unfold hb_ids in ND. cbn [flat_map ab_kind app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N].
  - exfalso. revert Y. cbn [ab_kind abkind_eqb]. rewrite N.eqb_refl. cbn. intros Y; exact Y.
  - apply lb_remove_notin. exact NI.
Qed.

Lemma lb_remove_secondA : forall p A n b0 LB, List.NoDup (hb_ids (b0 :: HB p A n :: LB)) -> lb_remove p (b0 :: HB p A n :: LB) = b0 :: LB.
Proof.
  intros p A n b0 LB ND.
  assert (ND' : List.NoDup (hb_ids (HB p A n :: LB)) /\ ~ (exists q, ab_kind b0 = ABHeap q /\ q = p)).
  { unfold hb_ids in *. cbn [flat_map] in ND |- *. destruct b0 as [[q|c] bA bn]; cbn [ab_kind app] in *.
    - apply NoDup_cons_iff in ND. destruct ND as [NI ND]. split; [exact ND|]. intros (q' & E & ->). inversion E; subst. apply NI. left. reflexivity.
    - split; [exact ND|]. intros (q' & E & _). discriminate. }
  destruct ND' as [ND1 NB0].
  unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N].
  - f_equal. apply lb_remove_headA. exact ND1.
  - exfalso. apply N. destruct b0 as [[q|c] bA bn]; cbn [ab_kind abkind_eqb negb] in *; [| exact I].
    destruct (N.eqb_spec q p); [| exact I]. exfalso. apply NB0. exists q. auto.
Qed.











End CANSEC1.
