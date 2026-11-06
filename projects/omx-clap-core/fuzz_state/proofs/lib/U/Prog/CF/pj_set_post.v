From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Module YK11 := YK11.
Module YM05 := YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition set_post (dd : nat) L A regs mem md Lam peak cnt fail b o w ms tv D Dw kids keys n cap kname :=
      (fun c' => exists L' A' regs' mem' md' Lam' peak' fail' res (c : nat) Lr Do,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw))
           L' A' regs' mem' md' /\
         rd_cells B mem' /\
         getr regs' 10 = Z_to_bv 64 res /\
         ledger B L' A' mem' Lam' peak' (cnt + Z.of_nat c) fail' /\
         fail_after cnt fail c fail' /\
         Permutation Lam (D ++ Dw ++ Lr) /\ Permutation Lam' (Do ++ Lr) /\
         pj_zero segs mem' w /\
         ((fail < cnt \/ cnt + 2 < fail) -> res = 0) /\
         ( (In (zb kname) (map fst ms) /\ c = 0%nat /\ res = 0 /\ peak' = peak /\
            (exists i vi Di Dr, nth_error ms i = Some (zb kname, vi) /\
               (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> zb kname) /\
               pj_node segs mem (lin Lam) (kids + 56 * Z.of_nat i) vi Di /\
               Permutation D (Di ++ Dr) /\ Permutation Do (Dr ++ Dw) /\
               (exists Di', Permutation Di Di' /\ rf_ok F A' (rf_frees F b Di')) /\
               Z.of_nat (length Do) = Z.of_nat (length (D ++ Dw)) - Z.of_nat (length Di) /\
               lsum Do = lsum (D ++ Dw) - lsum Di) /\
            pj_node segs mem' (lin Lam') o (JObj (pj_set_model ms (zb kname) tv)) Do)
         \/ (~ In (zb kname) (map fst ms) /\
             ~ (cnt <= fail < cnt + Z.of_nat (length (set_trace n cap (Z.of_nat (length kname))))) /\
             c = length (set_trace n cap (Z.of_nat (length kname))) /\ res = 0 /\
             peak' = Z.max peak (lsum Lam') /\
             rf_ok F A' (rf_run F b (set_trace n cap (Z.of_nat (length kname)))) /\
             Z.of_nat (length Do) = Z.of_nat (length (D ++ Dw)) + nlive (set_trace n cap (Z.of_nat (length kname))) /\
             lsum Do = lsum (D ++ Dw) + held (set_trace n cap (Z.of_nat (length kname))) /\
             (exists Dold Dnew Dr a, Permutation D (Dold ++ Dr) /\
                Permutation Do (Dnew ++ (a, Z.of_nat (length kname) + 1) :: Dr ++ Dw) /\
                (forall a' k', In (a', k') (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) ->
                   In (a', k') Dold \/ ~ In (a' - 16, k' + 16) (blocks L A)) /\
                (n < cap /\ Dold = [] /\ Dnew = [] \/
                 n = cap /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
                   exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)])) /\
             pj_node segs mem' (lin Lam') o (JObj (pj_set_model ms (zb kname) tv)) Do)
         \/ (~ In (zb kname) (map fst ms) /\
             cnt <= fail < cnt + Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) /\
             Z.of_nat c = fail - cnt + 1 /\ res = -1 /\
             peak' = Z.max peak (lsum Lam' + lsum Dw) /\
             (exists Dw', Permutation Dw Dw' /\
                rf_ok F A' (rf_frees F (rf_run F b (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname))))) Dw')) /\
             Z.of_nat (length Do) = Z.of_nat (length D) + nlive (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) /\
             lsum Do = lsum D + held (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) /\
             (exists Dold Dnew Dr, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
                new_blks L A Dnew /\
                (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
                 n = cap /\ c = 2%nat /\ Dold = kids_blk kids cap /\ (exists k', Dnew = [(k', 56 * cap2 cap)]) \/
                 n = cap /\ c = 3%nat /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
                   exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)])) /\
             pj_freeable segs mem' (lin Lam') o Do /\
             (Z.of_nat c = Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) ->
                pj_node segs mem' (lin Lam') o (JObj ms) Do)) )).

End K.

Lemma st_cap2 : forall cap, 0 <= cap -> 0 < cap2 cap /\ cap < cap2 cap.
Proof. intros cap H. unfold cap2. destruct (Z.eqb_spec cap 0); lia. Qed.

Lemma st_kids_lsum : forall kids cap, 0 <= cap -> lsum (kids_blk kids cap) = 56 * cap.
Proof. intros kids cap H. unfold kids_blk. destruct (Z.eqb_spec cap 0); cbn [lsum]; lia. Qed.

Lemma st_keys_lsum : forall keys cap, 0 <= cap -> lsum (keys_blk 6 keys cap) = 8 * cap.
Proof. intros keys cap H. unfold keys_blk. destruct (Z.eqb_spec cap 0); cbn; lia. Qed.

Lemma st_gone : forall a n i o w D Dw, 0 <= i < n -> freed (D ++ Dw) a n -> pj_set_writes o w D Dw (a + i).
Proof. intros a n i o w D Dw Hi Hf. right; right; left. exists (a + 16), (n - 16). split; [exact Hf | lia]. Qed.

Lemma st_lt : forall n cap kl, n < cap -> set_trace n cap kl = [EAlloc (Z.to_nat (kl + 1))].
Proof. intros n cap kl H. unfold set_trace. rewrite (proj2 (Z.eqb_neq n cap)) by lia. reflexivity. Qed.

Lemma st_eq : forall cap kl, set_trace cap cap kl =
  [EGrow (Z.to_nat (56 * cap)) (Z.to_nat (56 * cap2 cap)); EGrow (Z.to_nat (8 * cap)) (Z.to_nat (8 * cap2 cap));
   EAlloc (Z.to_nat (kl + 1))].
Proof. intros cap kl. unfold set_trace. rewrite Z.eqb_refl. reflexivity. Qed.

Section Tr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable F : ResForm.

Lemma st_lt_facts : forall b n cap kl, n < cap -> 0 <= kl ->
  length (set_trace n cap kl) = 1%nat /\ rf_run F b (set_trace n cap kl) = rf_malloc F b (kl + 17) /\
  nlive (set_trace n cap kl) = 1 /\ held (set_trace n cap kl) = kl + 1 /\
  rf_run F b (firstn 0 (set_trace n cap kl)) = b /\ nlive (firstn 0 (set_trace n cap kl)) = 0 /\
  held (firstn 0 (set_trace n cap kl)) = 0 /\
  (room_run F b (set_trace n cap kl) -> rf_room F b (kl + 17) /\ kl + 17 <= 2 ^ 28).
Proof.
  intros b n cap kl H Hk. rewrite (st_lt n cap kl H).
  unfold rf_run. cbn [length fold_left rf_ev nlive nlive_ev held held_ev firstn room_run is_call esize].
  rewrite Z2Nat.id by lia.
  split; [reflexivity|]. split; [f_equal; lia|]. split; [lia|]. split; [lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros (H1 & _). destruct (H1 eq_refl) as (H2 & H3).
  split; [replace (kl + 17) with (kl + 1 + 16) by lia; exact H2 | lia].
Qed.

Lemma st_eq_run : forall b cap kl, 0 <= cap -> 0 <= kl ->
  length (set_trace cap cap kl) = 3%nat /\
  rf_run F b (firstn 0 (set_trace cap cap kl)) = b /\
  rf_run F b (firstn 1 (set_trace cap cap kl)) = rf_grow F b (56 * cap) (56 * cap2 cap) /\
  rf_run F b (firstn 2 (set_trace cap cap kl)) =
    rf_grow F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap) (8 * cap2 cap) /\
  rf_run F b (set_trace cap cap kl) =
    rf_malloc F (rf_grow F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap) (8 * cap2 cap)) (kl + 17) /\
  held (firstn 0 (set_trace cap cap kl)) = 0 /\
  held (firstn 1 (set_trace cap cap kl)) = 56 * cap2 cap - 56 * cap /\
  held (firstn 2 (set_trace cap cap kl)) = 64 * cap2 cap - 64 * cap /\
  held (set_trace cap cap kl) = 64 * cap2 cap - 64 * cap + kl + 1.
Proof.
  intros b cap kl H Hk. pose proof (st_cap2 cap H) as Hc2. rewrite (st_eq cap kl). unfold rf_run.
  cbn [length firstn fold_left rf_ev held held_ev].
  rewrite !Z2Nat.id by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [f_equal; lia|]. split; [reflexivity|]. split; [lia|]. split; lia.
Qed.

Lemma st_eq_nl : forall cap kl kids keys, 0 <= cap ->
  exists z0, Z.of_nat (length (kids_blk kids cap)) = 1 - z0 /\ Z.of_nat (length (keys_blk 6 keys cap)) = 1 - z0 /\
    nlive (firstn 0 (set_trace cap cap kl)) = 0 /\ nlive (firstn 1 (set_trace cap cap kl)) = z0 /\
    nlive (firstn 2 (set_trace cap cap kl)) = 2 * z0 /\ nlive (set_trace cap cap kl) = 2 * z0 + 1.
Proof.
  intros cap kl kids keys H. rewrite (st_eq cap kl). destruct (Z.eqb_spec cap 0) as [->|Hc].
  - exists 1. unfold kids_blk, keys_blk. cbn. repeat split; lia.
  - assert (E1 : Z.to_nat (56 * cap) = S (Z.to_nat (56 * cap) - 1)) by lia.
    assert (E2 : Z.to_nat (8 * cap) = S (Z.to_nat (8 * cap) - 1)) by lia.
    rewrite E1, E2. exists 0. unfold kids_blk, keys_blk. rewrite (proj2 (Z.eqb_neq cap 0) Hc).
    cbn [orb negb Z.eqb Pos.eqb length firstn nlive nlive_ev]. repeat split; lia.
Qed.

Lemma st_eq_room : forall b cap kl, 0 <= cap -> 0 <= kl -> room_run F b (set_trace cap cap kl) ->
  rf_room F b (56 * cap2 cap + 16) /\ 56 * cap2 cap + 16 <= 2 ^ 28 /\
  rf_room F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap2 cap + 16) /\
  rf_room F (rf_grow F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap) (8 * cap2 cap)) (kl + 17) /\
  kl + 17 <= 2 ^ 28.
Proof.
  intros b cap kl H Hk HR. pose proof (st_cap2 cap H) as Hc2. rewrite (st_eq cap kl) in HR.
  cbn [room_run is_call esize rf_ev] in HR. rewrite !Z2Nat.id in HR by lia.
  destruct HR as (H1 & H2 & H3 & _). destruct (H1 eq_refl) as (R1 & R2). destruct (H2 eq_refl) as (R3 & _).
  destruct (H3 eq_refl) as (R4 & R5).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [replace (kl + 17) with (kl + 1 + 16) by lia; exact R4 | lia].
Qed.

End Tr.
