(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's representation after an inlined record(FN), one argument
   and the fold into g_rec.state (rec_stub_mix with one argument), for lv2_refusals_forget's ASan walk
   (plugin-hostd/fuzz_command); the representation is lib/A/Prog/CmdRep.v's (after lib/Prog/RecInv.v), the
   kept-memory lemmas follow lib/A/Prog/answer_code.v. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/lv2_refusals_forget_s2.v (an earlier version,
   the same 91-instruction walk for lv2_refusals_forget, generic in FN) for descriptors_add's walk. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() picks for a table of n calls *)
Definition lrf_c (n : Z) : Z := if n =? 16 then A_REC_SPILL else A_G_REC + OFF_CALLS + CALL_SIZE * n.
(* the layout after the call: the new argument block in the new slot *)
Definition lrf_lay (Q : rlay) (n : nat) (pn : Z * Z) : rlay :=
if Nat.ltb n 16 then RLay (l_calls Q ++ [[pn]]) (l_spill Q) (l_answer Q) (l_reply Q)
else RLay (l_calls Q) [pn] (l_answer Q) (l_reply Q).

Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma aanswer_at_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 8 -> rd' (gr + OFF_ANSWER + i) = rd (gr + OFF_ANSWER + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. destruct t as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Ha; lia]|].
  split; [exact A2|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A4|]. split; [|exact A6].
  apply (rastr_kept rd); [exact A5 | intros i Hi; apply (Hp pn i eq_refl); lia].
- apply (aval_mem_kept rd); [exact H | intros k Hk; apply Ha; lia].
Qed.
Lemma areply_at_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 16 -> rd' (gr + OFF_REPLY + i) = rd (gr + OFF_REPLY + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold OFF_REPLY_SIZE, OFF_REPLY in *.
destruct y as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia]|].
  split; [exact A3|]. split; [exact A4|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A6|]. split; [|exact A8].
  apply (rabytes_kept rd); [exact A7 | intros i Hi; apply (Hp pn i eq_refl); lia].
- destruct H as (A1 & A2).
  split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  apply (aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia].
Qed.

(* every block the layout names is a live block of the representation *)
Lemma arep_lay_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) ->
In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _ & _) Hin.
destruct HC as (_ & HlQ & _ & HCi & HSp & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- HlQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  destruct (HCi i c P Ec Hi) as [(_ & _ & HlP & _ & _ & _ & H7) _].
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (H7 k s pn Es Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HSp as (_ & _ & HlP & _ & _ & _ & H7).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (H7 k s pn Es Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
  + apply in_app_or in Hin as [Hin | Hin].
    * destruct (l_answer Q) as [q|] eqn:Eq; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R) as [x|]; cbn in HA; [|destruct HA].
      destruct HA as (_ & _ & A3 & A4 & _). split; [exact A3 | lia].
    * destruct (l_reply Q) as [q|] eqn:Eq; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R) as [x|]; cbn in HR; [|destruct HR].
      destruct HR as (_ & _ & _ & A4 & A5 & A6 & _). split; [exact A5|].
      destruct x as [|b x]; [exfalso; exact (A4 eq_refl)|]. cbn [length] in A6. lia.
Qed.
Lemma lrf_nodup_insert : forall (A : Type) (l1 l2 : list A) a, NoDup (l1 ++ l2) -> ~ In a (l1 ++ l2) -> NoDup (l1 ++ a :: l2).
Proof.
intros A l1 l2 a H Ha. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
apply (Permutation_NoDup (l := a :: l1 ++ l2)); [apply Permutation_middle | constructor; assumption].
Qed.

(* a fresh block apart from every block of the layout has a start no block of the layout has *)
Lemma lrf_fresh_fst : forall bl rd gr sc R Q p L, arep_at bl rd gr sc R Q -> 1 <= L ->
Forall (fun qk => iv_apart p L (fst qk) (snd qk)) bl -> ~ In p (map fst (lay_blocks Q)).
Proof.
intros bl rd gr sc R Q p L HA HL HF Hin. apply in_map_iff in Hin as (pn & Hp & Hin).
destruct (arep_lay_in bl rd gr sc R Q pn HA Hin) as [Hbl Hn].
pose proof (proj1 (Forall_forall _ _) HF pn Hbl) as Hap. unfold iv_apart in Hap. lia.
Qed.

Lemma lrf_rep_post : forall (bl0 blF : list (Z * Z)) (rd0 rdF : reader) (Rb : rstate) (Qb : rlay) (fn p L : Z) (x : list byte),
arep_at bl0 rd0 A_G_REC A_REC_SPILL Rb Qb ->
((length (r_calls Rb) < 16)%nat -> aval_mem rdF (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls Rb)) + 1)) ->
((16 <= length (r_calls Rb))%nat -> snd (r_spill Rb) = []) ->
0 <= fn < REC_FN_COUNT ->
aval_mem rdF (lrf_c (Z.of_nat (length (r_calls Rb)))) 4 fn ->
aval_mem rdF (lrf_c (Z.of_nat (length (r_calls Rb))) + 4) 4 1 ->
aval_mem rdF (lrf_c (Z.of_nat (length (r_calls Rb))) + 8) 8 p ->
aval_mem rdF (A_G_REC + OFF_STATE) 8 (mixcall (r_state Rb) fn [x]) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (lrf_c (Z.of_nat (length (r_calls Rb))) <= a < lrf_c (Z.of_nat (length (r_calls Rb))) + 16) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  ~ ((length (r_calls Rb) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdF a = rd0 a) ->
(forall q k i, In (q, k) bl0 -> 0 <= i < k -> rdF (q + i) = rd0 (q + i)) ->
(forall pn, In pn bl0 -> In pn blF) -> In (p, L) blF ->
L = Z.of_nat (length x) + 1 -> Z.of_nat (length x) <= LMAX -> p <> 0 -> astr_atR rdF p x ->
Forall (fun qk => iv_apart p L (fst qk) (snd qk)) bl0 ->
iv_apart p L A_G_REC REC_SIZE -> iv_apart p L A_REC_SPILL SC_SIZE ->
arep_at blF rdF A_G_REC A_REC_SPILL (rec_mix (rec_record Rb fn [x]) (fn, [x])) (lrf_lay Qb (length (r_calls Rb)) (p, L)).
Proof.
intros bl0 blF rd0 rdF Rb Qb fn p L x HA HNC1 HSP0 Hfn Vfn Vna Varg Vst HK HKB Hbl HinF HL Hx Hp0 Hstr HFr HapG HapS.
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAN & HRP & HSC & HOWN).
destruct HC as (Hlen16 & HlQ & HNC & HCi & HSp & HSpM).
destruct HSC as (S1 & S2 & S3 & S4 & S5 & R1 & R2 & R3 & R4 & R5).
destruct HOWN as (HND & HAP).
set (n := length (r_calls Rb)) in *.
assert (HL1 : 1 <= L) by lia.
assert (Hfresh : ~ In p (map fst (lay_blocks Qb))) by exact (lrf_fresh_fst bl0 rd0 _ _ Rb Qb p L HA HL1 HFr).
(* the bytes the layout's blocks hold are kept *)
assert (KLB : forall pn i, In pn (lay_blocks Qb) -> 0 <= i < snd pn -> rdF (fst pn + i) = rd0 (fst pn + i)).
{ intros [q k] i Hin Hi. destruct (arep_lay_in bl0 rd0 _ _ Rb Qb (q, k) HA Hin) as [Hb _]. exact (HKB q k i Hb Hi). }
assert (LBin : forall pn, In pn (lay_blocks Qb) -> In pn blF).
{ intros pn Hin. apply Hbl. exact (proj1 (arep_lay_in bl0 rd0 _ _ Rb Qb pn HA Hin)). }
(* the fixed words of g_rec are kept *)
assert (KG : forall o, (0 <= o < 8 \/ 912 <= o < 944 \/ 952 <= o < 960) -> rdF (A_G_REC + o) = rd0 (A_G_REC + o)).
{ intros o Ho. apply HK; [left; unfold REC_SIZE; lia | | unfold OFF_STATE; lia | unfold OFF_NCALLS; lia].
  unfold lrf_c. destruct (Z.eqb_spec (Z.of_nat n) 16); unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE in *; lia. }
(* a recorded call of the table kept *)
assert (KC : forall i c P, (i < n)%nat -> nth_error (r_calls Rb) i = Some c -> nth_error (l_calls Qb) i = Some P ->
  acall_at blF rdF (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
{ intros i c P Hi Ec EP. destruct (HCi i c P Ec EP) as [HAc HFc]. split; [|exact HFc].
  apply (acall_at_kept bl0 blF rd0 rdF); [exact HAc | | |].
  - intros pn Hpn. apply LBin. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
    split; [exact (nth_error_In _ _ EP) | exact Hpn].
  - intros j Hj. pose proof HAc as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj.
    assert (Hj56 : 0 <= j < CALL_SIZE) by (unfold CALL_SIZE; lia).
    rewrite <- Z.add_assoc, <- Z.add_assoc. apply HK.
    + left. unfold REC_SIZE, OFF_CALLS, CALL_SIZE in *. lia.
    + unfold lrf_c. destruct (Z.eqb_spec (Z.of_nat n) 16);
      unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE in *; lia.
    + unfold OFF_STATE, OFF_CALLS, CALL_SIZE in *. lia.
    + unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE in *. lia.
  - intros pn j Hpn Hj. apply KLB; [|exact Hj]. unfold lay_blocks. apply in_or_app. left. apply in_concat.
    exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
(* the new call *)
assert (NC : forall a, a = lrf_c (Z.of_nat n) -> acall_at blF rdF a (fn, [x]) [(p, L)]).
{ intros a ->. split; [exact Hfn|]. split; [cbn; lia|]. split; [reflexivity|].
  split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact Vfn|]. split; [unfold CALL_OFF_NARGS; exact Vna|].
  split; [cbn; apply NoDup_ListNoDup; apply List.NoDup_cons; [cbn; tauto | apply List.NoDup_nil]|].
  intros k s pn Hs Hpn. destruct k as [|k]; [|destruct k; discriminate Hs].
  cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd]. unfold CALL_OFF_ARGS.
  split; [rewrite Z.mul_0_r, Z.add_0_r; exact Varg|]. split; [exact Hp0|]. split; [exact HinF|].
  split; [unfold LMAX in *; lia | exact Hstr]. }
assert (Hst : 0 <= mixcall (r_state Rb) fn [x] < 2 ^ 64) by (apply mixcall_range; lia).
(* the answer and the reply kept *)
assert (KAN : aanswer_at blF rdF A_G_REC (r_answer Rb) (l_answer Qb)).
{ apply (aanswer_at_kept bl0 blF rd0 rdF A_G_REC _ _ HAN).
  - intros pn Hq. apply LBin. unfold lay_blocks. rewrite Hq. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. left. reflexivity.
  - intros i Hi. unfold OFF_ANSWER. rewrite <- Z.add_assoc. apply KG. lia.
  - intros pn i Hq Hi. apply KLB; [|exact Hi]. unfold lay_blocks. rewrite Hq. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
assert (KRP : areply_at blF rdF A_G_REC (r_reply Rb) (l_reply Qb)).
{ apply (areply_at_kept bl0 blF rd0 rdF A_G_REC _ _ HRP).
  - intros pn Hq. apply LBin. unfold lay_blocks. rewrite Hq. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. left. reflexivity.
  - intros i Hi. unfold OFF_REPLY. rewrite <- Z.add_assoc. apply KG. lia.
  - intros pn i Hq Hi. apply KLB; [|exact Hi]. unfold lay_blocks. rewrite Hq. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
assert (KSC : forall o v k, aval_mem rd0 (A_G_REC + o) k v -> (0 <= o /\ o + Z.of_nat k <= 8 \/ 912 <= o /\ o + Z.of_nat k <= 944 \/ 952 <= o /\ o + Z.of_nat k <= 960) ->
  aval_mem rdF (A_G_REC + o) k v).
{ intros o v k H Ho. apply (aval_mem_kept rd0); [exact H|]. intros j Hj. rewrite <- Z.add_assoc. apply KG. lia. }
unfold rec_mix, rec_record. fold n. unfold lrf_lay. unfold arep_at, ag1_calls, ag1_scalars, ag1_own.
destruct (Nat.ltb_spec n 16) as [Hlt | Hge].
- (* a new slot of the table *)
  cbn [set_state set_calls r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host fst snd
       l_calls l_spill l_answer l_reply].
  split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
  split.
  { split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, HlQ; reflexivity|].
    split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact (HNC1 Hlt)|].
    split.
    - intros i c P Ec EP. destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
      + rewrite nth_error_app1 in Ec by lia. rewrite nth_error_app1 in EP by (rewrite HlQ; lia).
        exact (KC i c P Hi Ec EP).
      + rewrite nth_error_app2 in Ec by lia. rewrite nth_error_app2 in EP by (rewrite HlQ; lia).
        rewrite HlQ in EP. fold n in Ec, EP.
        destruct (i - n)%nat as [|j] eqn:Ej; [|destruct j; discriminate Ec].
        cbn in Ec, EP. injection Ec as <-. injection EP as <-.
        split; [|constructor; [cbn; lia | constructor]].
        apply NC. unfold lrf_c. replace (Z.of_nat n =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
        replace i with n by lia. reflexivity.
    - split; [|exact HSpM].
      apply (acall_at_kept bl0 blF rd0 rdF); [exact HSp | | |].
      + intros pn Hpn. apply LBin. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
      + intros j Hj. pose proof HSp as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj.
        apply HK; [right; unfold SC_SIZE; lia | | unfold A_REC_SPILL, A_G_REC, OFF_STATE; lia | unfold A_REC_SPILL, A_G_REC, OFF_NCALLS; lia].
        unfold lrf_c. replace (Z.of_nat n =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
        unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE in *; lia.
      + intros pn j Hpn Hj. apply KLB; [|exact Hj]. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  split; [exact KAN|]. split; [exact KRP|].
  split.
  { unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    split; [apply KSC; [exact S1 | cbn; lia]|]. split; [apply KSC; [exact S2 | cbn; lia]|].
    split; [apply KSC; [exact S3 | cbn; lia]|]. split; [exact Vst|]. split; [apply KSC; [exact S5 | cbn; lia]|].
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact Hst | exact R5]. }
  assert (EQ : lay_blocks (RLay (l_calls Qb ++ [[(p, L)]]) (l_spill Qb) (l_answer Qb) (l_reply Qb)) =
    concat (l_calls Qb) ++ (p, L) :: (l_spill Qb ++ oblk (l_answer Qb) ++ oblk (l_reply Qb))).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r, <- app_assoc. reflexivity. }
  assert (EQ0 : lay_blocks Qb = concat (l_calls Qb) ++ (l_spill Qb ++ oblk (l_answer Qb) ++ oblk (l_reply Qb))) by reflexivity.
  split.
  + rewrite EQ, map_app. cbn [map]. apply lrf_nodup_insert; rewrite <- map_app, <- EQ0; [exact HND | exact Hfresh].
  + intros pn Hin. rewrite EQ in Hin. apply in_app_or in Hin as [Hin | [<- | Hin]].
    * apply HAP. rewrite EQ0. apply in_or_app. left. exact Hin.
    * cbn [fst snd]. split; [exact HapG | exact HapS].
    * apply HAP. rewrite EQ0. apply in_or_app. right. exact Hin.
- (* record.spill *)
  assert (En : n = 16%nat) by lia.
  assert (Hsp0 : snd (r_spill Rb) = []) by (apply HSP0; lia).
  assert (HlS : l_spill Qb = []).
  { pose proof HSp as (_ & _ & HlP & _). rewrite Hsp0 in HlP. cbn in HlP. destruct (l_spill Qb); [reflexivity | discriminate HlP]. }
  cbn [set_state set_spill r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host fst snd
       l_calls l_spill l_answer l_reply].
  split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
  assert (Ecs : lrf_c (Z.of_nat n) = A_REC_SPILL) by (unfold lrf_c; rewrite En; reflexivity).
  split.
  { split; [exact Hlen16|]. split; [exact HlQ|].
    split; [apply (aval_mem_kept rd0); [exact HNC | intros k Hk; apply HK; [left; unfold OFF_NCALLS, REC_SIZE; lia | | unfold OFF_NCALLS, OFF_STATE; lia | intros [? _]; lia]];
      rewrite Ecs; unfold A_REC_SPILL, A_G_REC, OFF_NCALLS; lia|].
    split.
    - intros i c P Ec EP. apply (KC i c P); [|exact Ec | exact EP].
      apply nth_error_Some. rewrite Ec. discriminate.
    - split; [|constructor; [cbn; lia | constructor]].
      apply NC. unfold lrf_c. fold n. rewrite En. reflexivity. }
  split; [exact KAN|]. split; [exact KRP|].
  split.
  { unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    split; [apply KSC; [exact S1 | cbn; lia]|]. split; [apply KSC; [exact S2 | cbn; lia]|].
    split; [apply KSC; [exact S3 | cbn; lia]|]. split; [exact Vst|]. split; [apply KSC; [exact S5 | cbn; lia]|].
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact Hst | exact R5]. }
  assert (EQ : lay_blocks (RLay (l_calls Qb) [(p, L)] (l_answer Qb) (l_reply Qb)) =
    concat (l_calls Qb) ++ (p, L) :: (oblk (l_answer Qb) ++ oblk (l_reply Qb))) by reflexivity.
  assert (EQ0 : lay_blocks Qb = concat (l_calls Qb) ++ (oblk (l_answer Qb) ++ oblk (l_reply Qb)))
    by (unfold lay_blocks; rewrite HlS; reflexivity).
  split.
  + rewrite EQ, map_app. cbn [map]. apply lrf_nodup_insert; rewrite <- map_app, <- EQ0; [exact HND | exact Hfresh].
  + intros pn Hin. rewrite EQ in Hin. apply in_app_or in Hin as [Hin | [<- | Hin]].
    * apply HAP. rewrite EQ0. apply in_or_app. left. exact Hin.
    * cbn [fst snd]. split; [exact HapG | exact HapS].
    * apply HAP. rewrite EQ0. apply in_or_app. right. exact Hin.
Qed.
