(* proves no function (rule 24; kind: invariant lemma): RI_write_skip and RI_write_push at RINV := fr_RINV, image B *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) twin of the two write rows of
   lib/A/ReplyRINV_a3.v at 5467eb8cd0d (a working branch), relocated onto lib/B/ReplyRINVB.v's fr_RINV
   and lib/B/W_LLVMFuzzerTestOneInput_write.v's records at the B top e43cf0c7bef (a working branch).
   RI_write_skip_b and RI_write_push_b are the Section hypotheses RI_write_skip (_write.v :256) and RI_write_push
   (_write.v :262) with RINV := ReplyRINVB.fr_RINV, in the text of the Section hypotheses of the same names in
   lib/B/ReplyBTop.v (a working branch).
   What is here, each with its source:
     bw_in_byte_range, bw_wr_k, bw_wr_x_len         A twin a3_in_byte_range :83, a3_wr_k :92, a3_wr_x_len :110
     bw_pending_push, bw_nopen_wset                 A twin a3_pending_push :173, a3_nopen_wset :182
     bw_wpair, bw_cost_wpair                        A twin a3_wpair :192, a3_cost_wpair :195
     bw_Forall2_r, bw_Forall2_map                   lib/A/ReplyRINV.v at f57b3e2d0ca fr_Forall2_r :590, fr_Forall2_map :777
                                                    (ReplyRINVB.v has neither)
     RI_write_skip_b, RI_write_push_b               A twin RI_write_skip_holds :114, RI_write_push_holds :219
   A -> B swaps: the imports are lib/B/ReplyRINVB.v's (its header lists them against lib/A/ReplyRINV.v), then lib/B's
   W_LLVMFuzzerTestOneInput_write and ReplyRINVB for lib/A's; fr_RINV, fr_pair_ok, fr_cost, fr_step_k are ReplyRINVB.v's
   (the same text as ReplyRINV.v's); wr_*, set_pending, set_ev, set_nth and its three lemmas are lib/B's _write.v's (the
   same text as lib/A's); the Section has ReplyRINVB.v's Context and Variables (the twin's LS is not one of them, and no
   lemma here names it).  The constants the proofs read are the byte bound 256, fuzz_u16's bound 65535 and
   SlotInv.WRITE_MAX = 65535 (lib/Prog/SlotInv.v :25, one file for both images). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinv_write.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).

Lemma bw_in_byte_range : forall cx i, 0 <= in_byte cx i < 256.
Proof.
  intros cx i. unfold in_byte.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma bw_wr_k : forall cx m, 0 <= lm_k m < c_n cx ->
  lm_k m + 1 <= wr_k1 cx m /\ wr_k1 cx m <= c_n cx /\ 0 <= wr_c cx m /\ 0 <= wr_n cx m <= SlotInv.WRITE_MAX /\
  wr_k2 cx m = wr_k1 cx m + wr_c cx m + wr_n cx m /\ wr_k1 cx m + wr_c cx m + wr_n cx m <= c_n cx.
Proof.
  intros cx m Hk.
  assert (K1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof (bw_in_byte_range cx (wr_k1 cx m)) as B1.
  pose proof (bw_in_byte_range cx (wr_k1 cx m + 1)) as B2.
  assert (HU : 0 <= wr_u cx m <= 65535).
  { unfold wr_u. destruct (2 <=? wr_rem cx m); [lia|]. destruct (wr_rem cx m =? 1); lia. }
  assert (HR : wr_rem cx m = c_n cx - wr_k1 cx m) by reflexivity.
  assert (HC : wr_c cx m = Z.min 2 (wr_rem cx m)) by reflexivity.
  assert (HN : wr_n cx m = Z.min (wr_u cx m) (wr_rem cx m - wr_c cx m)) by reflexivity.
  unfold wr_k2, SlotInv.WRITE_MAX. lia.
Qed.

Lemma bw_wr_x_len : forall cx m, 0 <= wr_n cx m -> Z.of_nat (length (wr_x cx m)) <= wr_n cx m.
Proof. intros cx m Hn. unfold wr_x. rewrite length_firstn. lia. Qed.

Lemma RI_write_skip_b : forall (cx : lfcx) (t : Z) (m : lmod), ReplyRINVB.fr_RINV cx t m ->
  0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_write.wr_kb cx m) = None \/ W_LLVMFuzzerTestOneInput_write.wr_n cx m = 0 ->
  ReplyRINVB.fr_RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)).
Proof.
  intros cx t m H Hk _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold wr_skip. cbn [lm_k]. pose proof (bw_wr_k cx m Hk). lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

Lemma bw_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
Lemma bw_Forall2_map : forall (T1 T2 T3 : Type) (R : T1 -> T2 -> Prop) (R' : T1 -> T3 -> Prop) (g : T2 -> T3) l1 l2,
  (forall x y, R x y -> R' x (g y)) -> Forall2 R l1 l2 -> Forall2 R' l1 (map g l2).
Proof. intros T1 T2 T3 R R' g l1 l2 H HF. induction HF; cbn [map]; constructor; auto. Qed.

Lemma bw_pending_push : forall h l' x d, hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] ->
  (length (pending_stream (set_pending h l')) <= length (pending_stream h) + length x)%nat.
Proof.
  intros h l' x d E. unfold pending_stream, set_pending. cbn [hs_pending hs_off]. rewrite E.
  destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [app].
  - cbn [map concat snd length]. rewrite app_nil_r, length_skipn. lia.
  - rewrite List.map_app, concat_app, !length_app. cbn [map concat snd]. rewrite app_nil_r. lia.
Qed.
Lemma bw_nopen_wset : forall hs i x y, nth i hs None = Some y -> (i < length hs)%nat ->
  nopen (W_LLVMFuzzerTestOneInput_write.set_nth i (Some x) hs) = nopen hs.
Proof.
  intros hs i x y. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. reflexivity.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [W_LLVMFuzzerTestOneInput_write.set_nth List.filter length]; lia.
Qed.
Definition bw_wpair (l' : hlist) (si : nat) (p : hsrc * nat) : hsrc * nat :=
  if Nat.eqb (snd p) si then (set_pending (fst p) l', snd p) else p.
Lemma bw_cost_wpair : forall l' si w es hj, 0 <= w ->
  (forall p, In p hj -> snd p = si ->
     Z.of_nat (length (pending_stream (set_pending (fst p) l'))) <= Z.of_nat (length (pending_stream (fst p))) + w) ->
  List.NoDup (map snd hj) ->
  fr_cost es (map (bw_wpair l' si) hj) <= fr_cost es hj + w.
Proof.
  intros l' si w es. unfold fr_cost. induction es as [|e es IH]; intros hj Hw0 Hw Hnd; [cbn; lia|].
  destruct hj as [|p hj]; [cbn; lia|].
  cbn [map combine fold_right fst snd]. cbn [map] in Hnd.
  apply NoDup_cons_iff in Hnd as [Hp Hnd].
  assert (Eg : bw_wpair l' si p = if Nat.eqb (snd p) si then (set_pending (fst p) l', snd p) else p)
    by reflexivity.
  rewrite Eg. destruct (Nat.eqb (snd p) si) eqn:E.
  - apply Nat.eqb_eq in E.
    assert (Et : map (bw_wpair l' si) hj = hj).
    { transitivity (map (fun q => q) hj); [|apply map_id].
      apply map_ext_in. intros q Hq. unfold bw_wpair.
      destruct (Nat.eqb (snd q) si) eqn:Eq; [|reflexivity].
      apply Nat.eqb_eq in Eq. exfalso. apply Hp. rewrite E, <- Eq. apply in_map. exact Hq. }
    rewrite Et. pose proof (Hw p (or_introl eq_refl) E) as Hb.
    unfold fr_pair_cost. cbn [fst]. lia.
  - pose proof (IH hj Hw0 (fun q Hq => Hw q (or_intror Hq)) Hnd). lia.
Qed.

Lemma RI_write_push_b : forall (cx : lfcx) (t : Z) (m : lmod) (si : nat) (h : hsrc) (l' : hlist) (d ev : Z),
  ReplyRINVB.fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) -> 0 <= ev < 2 ^ 32 ->
  ReplyRINVB.fr_RINV cx (t + 1)
    (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si
       (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev).
Proof.
  intros cx t m si h l' d ev HRI Hk _ (_ & Hsi & Hh) Hn Hrecs _ _.
  pose proof HRI as ((HC & Hnfd) & HR & Hcn26 & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  pose proof (bw_wr_k cx m Hk) as (K1 & K1n & Kc & (Kn0 & KnW) & K2 & K2n).
  pose proof (bw_wr_x_len cx m Kn0) as Hx.
  pose proof (bw_pending_push h l' (wr_x cx m) d Hrecs) as Hpp.
  assert (Hsil : (si < length (lm_hs m))%nat) by (rewrite Hlen; exact Hsi).
  assert (Hrow : forall e p, fr_pair_ok m t e p -> snd p = si -> fst p = h).
  { intros e p Hp E. destruct Hp as (_ & Hn0 & _). rewrite E, Hh in Hn0. injection Hn0 as Ef.
    exact (eq_sym Ef). }
  assert (Esnd : map snd (map (bw_wpair l' si) hj) = map snd hj).
  { rewrite List.map_map. apply List.map_ext. intros [h0 j0]. unfold bw_wpair. cbn [fst snd].
    destruct (Nat.eqb j0 si); reflexivity. }
  split; [|split; [|split; [exact Hcn26|]]].
  - unfold fr_count, wr_push. cbn [lm_nfd lm_hs].
    rewrite (bw_nopen_wset _ _ _ _ Hh Hsil). lia.
  - unfold fr_relay, wr_push. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite W_LLVMFuzzerTestOneInput_write.set_nth_length; exact Hlen|].
    split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists (map (bw_wpair l' si) hj).
    split.
    { apply (bw_Forall2_map _ _ _ (fr_pair_ok m t)); [|exact HF].
      intros e [h0 j0] Hp. unfold bw_wpair. cbn [fst snd].
      destruct (Nat.eqb j0 si) eqn:Ej.
      - apply Nat.eqb_eq in Ej. subst j0.
        assert (E0 : h0 = h) by exact (Hrow e (h0, si) Hp eq_refl). subst h0.
        destruct Hp as (H1 & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        cbn [fst snd] in H1, H3, H4, H5, H6, H7, H8, H9, H10, H11.
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_same _ si _ (lm_hs m) None Hsil).
        refine (conj H1 (conj eq_refl (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))).
        unfold SlotInv.WRITE_MAX in *. lia.
      - apply Nat.eqb_neq in Ej.
        destruct Hp as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        cbn [fst snd] in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11.
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_other _ si j0 _ _ None (not_eq_sym Ej)).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia. }
    split; [rewrite Esnd; exact HNDs|].
    split.
    { intros i Hi Ho. unfold SlotInv.slot_open in Ho. rewrite Esnd in Ho.
      pose proof (Hcl i Hi Ho) as Hc0.
      assert (Hne : si <> i) by (intros E; subst i; rewrite Hh in Hc0; discriminate Hc0).
      rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_other _ si i _ _ None Hne). exact Hc0. }
    assert (Hcw : fr_cost (lm_es m) (map (bw_wpair l' si) hj) <= fr_cost (lm_es m) hj + wr_n cx m).
    { apply bw_cost_wpair; [lia | | exact (proj1 (NoDup_ListNoDup _) HNDs)].
      intros p Hp E. destruct (bw_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
      rewrite (Hrow e p HRp E). lia. }
    split; lia.
  - unfold fr_gone, wr_push, set_ev. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact HG.
Qed.

End rinv_write.
