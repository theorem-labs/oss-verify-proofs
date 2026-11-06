(* Modified by Theorem Labs, 2026-10: the recorder-model steps of sup_pool_config's ASan walk (plugin-hostd/fuzz_command),
   second part: the spill arm's split of the recorder's blocks, rec_calls_free's premises on record.spill, and the whole
   record() + two-argument step from the state before record() to the state at answer's call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep sup_pool_config_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------- list facts (`NoDup` is stdpp's, as in CmdRep's ag1_own; the proofs go through List.NoDup) ---------- *)
Lemma spc5_nodup_disj : forall (A : Type) (l1 l2 : list A) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1 l2 x H. apply NoDup_ListNoDup in H. revert l2 x H.
induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [app] in H. apply List.NoDup_cons_iff in H. destruct H as [Hn Hd]. destruct H1 as [<-|H1].
- apply Hn. apply in_or_app. right. exact H2.
- exact (IH l2 x Hd H1 H2).
Qed.

Lemma spc5_fst_disj : forall (X Y : list (Z * Z)) pn, NoDup (map fst (X ++ Y)) -> In pn X -> In pn Y -> False.
Proof.
intros X Y pn H HX HY. rewrite map_app in H.
exact (spc5_nodup_disj Z (map fst X) (map fst Y) (fst pn) H (in_map fst X pn HX) (in_map fst Y pn HY)).
Qed.

Lemma spc5_fst_disj3 : forall (X M Y : list (Z * Z)) pn, NoDup (map fst (X ++ M ++ Y)) -> In pn M -> In pn Y -> False.
Proof.
intros X M Y pn H HM HY. rewrite app_assoc in H.
apply (spc5_fst_disj (X ++ M) Y pn H); [apply in_or_app; right; exact HM | exact HY].
Qed.

(* the recorder's blocks with the two new argument blocks b1, b2 put between X and W *)
Lemma spc5_iff2 : forall (O X W : list (Z * Z)) (b1 b2 : Z * Z), (forall pn, In pn O <-> In pn (X ++ W)) ->
forall pn, In pn (O ++ [b1; b2]) <-> In pn (X ++ [b1; b2] ++ W).
Proof.
intros O X W b1 b2 HO pn. specialize (HO pn). split; intros H.
- apply in_app_or in H. destruct H as [H|H].
  + apply (proj1 HO) in H. apply in_app_or in H. destruct H as [H|H]; apply in_or_app;
      [left; exact H | right; apply in_or_app; right; exact H].
  + apply in_or_app. right. apply in_or_app. left. exact H.
- apply in_app_or in H. destruct H as [H|H].
  + apply in_or_app. left. apply (proj2 HO). apply in_or_app. left. exact H.
  + apply in_app_or in H. destruct H as [H|H].
    * apply in_or_app. right. exact H.
    * apply in_or_app. left. apply (proj2 HO). apply in_or_app. right. exact H.
Qed.

Lemma spc5_own2 : forall (X W : list (Z * Z)) p1 n1 p2 n2,
NoDup (map fst (X ++ W)) ->
(forall pn, In pn (X ++ W) ->
   iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) ->
~ In p1 (map fst (X ++ W)) -> ~ In p2 (map fst (X ++ W)) -> p1 <> p2 ->
iv_apart p1 n1 A_G_REC REC_SIZE -> iv_apart p1 n1 A_REC_SPILL SC_SIZE ->
iv_apart p2 n2 A_G_REC REC_SIZE -> iv_apart p2 n2 A_REC_SPILL SC_SIZE ->
NoDup (map fst (X ++ [(p1, n1); (p2, n2)] ++ W)) /\
(forall pn, In pn (X ++ [(p1, n1); (p2, n2)] ++ W) ->
   iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
Proof.
intros X W p1 n1 p2 n2 HND HAP F1 F2 P12 A11 A12 A21 A22. split.
- rewrite map_app in HND, F1, F2.
  pose proof (spc_nodup_ins _ _ p2 HND F2) as N2.
  assert (F1' : ~ In p1 (map fst X ++ p2 :: map fst W)).
  { intros Hi. apply in_app_or in Hi. destruct Hi as [Hi|[Hi|Hi]].
    - apply F1. apply in_or_app. left. exact Hi.
    - exact (P12 (eq_sym Hi)).
    - apply F1. apply in_or_app. right. exact Hi. }
  pose proof (spc_nodup_ins _ _ p1 N2 F1') as N1.
  rewrite !map_app. exact N1.
- intros pn Hpn. apply in_app_or in Hpn. destruct Hpn as [Hpn|Hpn]; [apply HAP; apply in_or_app; left; exact Hpn|].
  cbn [app In] in Hpn. destruct Hpn as [<-|[<-|Hpn]]; cbn [fst snd];
    [split; assumption | split; assumption | apply HAP; apply in_or_app; right; exact Hpn].
Qed.

(* ---------- a call holding fn and the two arguments in the blocks (p1, n1), (p2, n2) ---------- *)
Lemma spc5_aval_eq : forall (rd : reader) a b n v, a = b -> aval_mem rd a n v -> aval_mem rd b n v.
Proof. intros rd a b n v -> H. exact H. Qed.

Lemma spc5_call2 : forall bl (rd : reader) e FN x d p1 n1 p2 n2,
0 <= FN < REC_FN_COUNT ->
aval_mem rd (e + CALL_OFF_FN) 4 FN -> aval_mem rd (e + CALL_OFF_NARGS) 4 2 ->
aval_mem rd (e + CALL_OFF_ARGS) 8 p1 -> aval_mem rd (e + CALL_OFF_ARGS + 8) 8 p2 ->
astr_atR rd p1 x -> astr_atR rd p2 d ->
Z.of_nat (length x) + 1 <= n1 <= LMAX + 2 -> Z.of_nat (length d) + 1 <= n2 <= LMAX + 2 ->
p1 <> 0 -> p2 <> 0 -> p1 <> p2 -> In (p1, n1) bl -> In (p2, n2) bl ->
acall_at bl rd e (FN, [x; d]) [(p1, n1); (p2, n2)].
Proof.
intros bl rd e FN x d p1 n1 p2 n2 Hfn BF BA B1 B2 S1 S2 Z1 Z2 P1 P2 P12 I1 I2.
unfold acall_at. cbn [fst snd length map].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|]. split; [exact BF|]. split; [exact BA|].
split.
{ apply NoDup_ListNoDup. apply List.NoDup_cons.
  - intros [E|[]]. exact (P12 (eq_sym E)).
  - apply List.NoDup_cons; [intros [] | apply List.NoDup_nil]. }
intros k s pn Hs Hpn.
destruct k as [|[|k]].
- cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [apply (spc5_aval_eq rd (e + CALL_OFF_ARGS)); [lia | exact B1]|].
  split; [exact P1|]. split; [exact I1|]. split; [exact Z1 | exact S1].
- cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [apply (spc5_aval_eq rd (e + CALL_OFF_ARGS + 8)); [lia | exact B2]|].
  split; [exact P2|]. split; [exact I2|]. split; [exact Z2 | exact S2].
- exfalso. destruct k; cbn in Hs; discriminate.
Qed.

(* the recorder's blocks on record()'s spill arm: the spill's arguments (which rec_calls_free frees) and the rest *)
Lemma spc_spill_split : forall bl (rd : reader) R Q O,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
(forall pn, In pn (l_spill Q) -> In pn O) /\
(forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) <-> In pn O /\ ~ In pn (l_spill Q)).
Proof.
intros bl rd R Q O HA HO.
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & HND & _).
destruct Q as [lc ls la lr].
unfold lay_blocks in HO, HND. cbn [l_calls l_spill l_answer l_reply] in HO, HND |- *.
split.
- intros pn Hpn. apply (proj2 (HO pn)). apply in_or_app. right. apply in_or_app. left. exact Hpn.
- intros pn. split.
  + intros Hpn. split.
    * apply (proj2 (HO pn)). apply in_app_or in Hpn. destruct Hpn as [Hpn|Hpn]; apply in_or_app;
        [left; exact Hpn | right; apply in_or_app; right; exact Hpn].
    * intros Hs. apply in_app_or in Hpn. destruct Hpn as [Hpn|Hpn].
      -- apply (spc5_fst_disj (concat lc) (ls ++ oblk la ++ oblk lr) pn HND Hpn). apply in_or_app. left. exact Hs.
      -- exact (spc5_fst_disj3 (concat lc) ls (oblk la ++ oblk lr) pn HND Hs Hpn).
  + intros [Hpn Hs]. apply (proj1 (HO pn)) in Hpn. apply in_app_or in Hpn.
    destruct Hpn as [Hpn|Hpn]; [apply in_or_app; left; exact Hpn|].
    apply in_app_or in Hpn. destruct Hpn as [Hpn|Hpn]; [contradiction | apply in_or_app; right; exact Hpn].
Qed.

(* rec_calls_free's premises (rec_calls_free_c.v:80-87) for record.spill, as the recorder state gives them *)
Lemma spc_spill_rcf_pre : forall bl (rd : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (l_spill Q) <= 6)%nat /\ length (l_spill Q) = length (snd (r_spill R)) /\
aval_mem rd (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length (l_spill Q))) /\
(forall a pn, nth_error (l_spill Q) a = Some pn ->
   aval_mem rd (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\ In pn bl) /\
NoDup (map fst (l_spill Q)).
Proof.
intros bl rd R Q (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
destruct C5 as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
split; [lia|]. split; [exact H3|]. split; [rewrite H3; exact H5|].
split; [|exact H6].
intros a pn Hpn.
assert (Ha : (a < length (snd (r_spill R)))%nat) by (rewrite <- H3; apply nth_error_Some; rewrite Hpn; discriminate).
destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
destruct (H7 a s pn Es Hpn) as (G1 & _ & G3 & _). split; [exact G1 | exact G3].
Qed.

Section d.
Variable B : asyms.

(* record(FN) and two arguments x and d, from the state before record() (the entry on the table arm; the state after
   rec_calls_free emptied the spill on the spill arm) to the state at answer's call: the slot holds FN, nargs 2 and
   the two fresh copies; g_rec.ncalls is n + 1 on the table arm; every other byte of g_rec / record.spill and of the
   recorder's blocks is kept *)
Lemma spc_rep_final : forall lyB SB lyA SA (rdB rdA : reader) R O0 FN x d p1 n1 p2 n2,
(length (r_calls R) <= 16)%nat ->
rec_repA B lyB SB rdB (if Nat.ltb (length (r_calls R)) 16 then R else set_spill R (fst (r_spill R), [])) O0 ->
0 <= FN < REC_FN_COUNT ->
(forall pn, In pn O0 -> In pn (ablocks B lyA SA)) -> In (p1, n1) (ablocks B lyA SA) -> In (p2, n2) (ablocks B lyA SA) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ((length (r_calls R) < 16)%nat -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) ->
   ~ (spc_slot R <= a < spc_slot R + CALL_SIZE) -> rdA a = rdB a) ->
(forall pn i, In pn O0 -> 0 <= i < snd pn -> rdA (fst pn + i) = rdB (fst pn + i)) ->
((length (r_calls R) < 16)%nat -> aval_mem rdA (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) ->
aval_mem rdA (spc_slot R + CALL_OFF_FN) 4 FN -> aval_mem rdA (spc_slot R + CALL_OFF_NARGS) 4 2 ->
aval_mem rdA (spc_slot R + CALL_OFF_ARGS) 8 p1 -> aval_mem rdA (spc_slot R + CALL_OFF_ARGS + 8) 8 p2 ->
astr_atR rdA p1 x -> astr_atR rdA p2 d ->
Z.of_nat (length x) <= LMAX -> Z.of_nat (length d) <= LMAX ->
Z.of_nat (length x) + 1 <= n1 <= LMAX + 2 -> Z.of_nat (length d) + 1 <= n2 <= LMAX + 2 ->
p1 <> 0 -> p2 <> 0 -> p1 <> p2 ->
iv_apart p1 n1 A_G_REC REC_SIZE -> iv_apart p1 n1 A_REC_SPILL SC_SIZE ->
iv_apart p2 n2 A_G_REC REC_SIZE -> iv_apart p2 n2 A_REC_SPILL SC_SIZE ->
~ In p1 (map fst O0) -> ~ In p2 (map fst O0) ->
rec_repA B lyA SA rdA (rec_record R FN [x; d]) (O0 ++ [(p1, n1); (p2, n2)]).
Proof.
intros lyB SB lyA SA rdB rdA R O0 FN x d p1 n1 p2 n2 Hle HRep Hfn Hbl Hin1 Hin2 KG KB BN BF BA B1 B2 S1 S2 Lx Ld
  Z1 Z2 P1 P2 P12 A11 A12 A21 A22 F1 F2.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
- (* the table arm: g_rec.calls[n] *)
  assert (Eb : Nat.ltb (length (r_calls R)) 16 = true) by (apply Nat.ltb_lt; exact Hn).
  assert (HR : rec_repA B lyB SB rdB R O0) by (rewrite Eb in HRep; exact HRep).
  assert (Es : spc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold spc_slot; rewrite Eb; reflexivity).
  rewrite Es in KG, BF, BA, B1, B2. clear Es HRep.
  rewrite (rec_record_calls R FN [x; d] Hn).
  destruct HR as (Q & HA & HO).
  pose proof (spc_notin_iff O0 (lay_blocks Q) p1 HO F1) as F1'.
  pose proof (spc_notin_iff O0 (lay_blocks Q) p2 HO F2) as F2'.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B lyA SA) /\
    forall i, 0 <= i < snd pn -> rdA (fst pn + i) = rdB (fst pn + i)).
  { intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (KB pn i Hpn Hi)]. }
  destruct Q as [lc ls la lr].
  exists (RLay (lc ++ [[(p1, n1); (p2, n2)]]) ls la lr). split.
  2: { intros pn. rewrite spc_lay_last.
    exact (spc5_iff2 O0 (concat lc) (ls ++ oblk la ++ oblk lr) (p1, n1) (p2, n2) HO pn). }
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HND & HAP).
  cbn [l_calls l_spill l_answer l_reply] in C2, C4, C5.
  pose proof G3 as G3'. unfold iv_apart, REC_SIZE, SC_SIZE in G3'.
  unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in KG.
  assert (KR : forall y, A_G_REC <= y < A_G_REC + 8 \/ A_G_REC + 912 <= y < A_G_REC + 960 -> rdA y = rdB y).
  { intros y Hy. apply KG; [left; lia | intros _; lia | lia]. }
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn (ablocks B lyA SA) /\
    forall i, 0 <= i < snd pn -> rdA (fst pn + i) = rdB (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (spc_rest_keep _ _ rdB rdA R (RLay lc ls la lr) Ha Hr HX KR KO) as (RA & RP & RX).
  unfold arep_at, ag1_calls, ag1_own.
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
    rewrite spc_lay_last.
    exact (spc5_own2 (concat lc) (ls ++ oblk la ++ oblk lr) p1 n1 p2 n2 HND HAP F1' F2' P12 A11 A12 A21 A22). }
  split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, C2; reflexivity|].
  split; [rewrite length_app, Nat2Z.inj_add; exact (BN Hn)|].
  split.
  { intros i c P Ec EP.
    destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
    - rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
      destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      apply (spc_call_kept _ _ rdB rdA _ c P Hc).
      + intros y Hy. unfold OFF_CALLS, CALL_SIZE in Hy. apply KG; [left; lia | intros _; lia | lia].
      + intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn].
    - destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
      + rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
        rewrite nth_error_app2 in EP by (rewrite C2; lia). rewrite C2, Nat.sub_diag in EP. cbn in EP.
        injection EP as <-.
        split; [|cbn [snd]; constructor; [exact Lx | constructor; [exact Ld | constructor]]].
        exact (spc5_call2 _ rdA _ FN x d p1 n1 p2 n2 Hfn BF BA B1 B2 S1 S2 Z1 Z2 P1 P2 P12 Hin1 Hin2).
      + exfalso. assert (N : nth_error (r_calls R ++ [(FN, [x; d])]) i = None)
          by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
        rewrite N in Ec. discriminate. }
  split; [|exact C6].
  apply (spc_call_kept _ _ rdB rdA _ _ _ C5).
  + intros y Hy. apply KG; [right; lia | intros _; lia | lia].
  + intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. left. exact Hpn.
- (* the spill arm: record.spill, emptied by rec_calls_free *)
  assert (Hn16 : length (r_calls R) = 16%nat) by lia.
  assert (Eb : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; lia).
  assert (HR : rec_repA B lyB SB rdB (set_spill R (fst (r_spill R), [])) O0) by (rewrite Eb in HRep; exact HRep).
  assert (Es : spc_slot R = A_REC_SPILL) by (unfold spc_slot; rewrite Eb; reflexivity).
  rewrite Es in KG, BF, BA, B1, B2. clear Es HRep.
  rewrite (rec_record_spill R FN [x; d] Hn16).
  destruct HR as (Q & HA & HO).
  pose proof (spc_notin_iff O0 (lay_blocks Q) p1 HO F1) as F1'.
  pose proof (spc_notin_iff O0 (lay_blocks Q) p2 HO F2) as F2'.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B lyA SA) /\
    forall i, 0 <= i < snd pn -> rdA (fst pn + i) = rdB (fst pn + i)).
  { intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (KB pn i Hpn Hi)]. }
  destruct Q as [lc ls la lr].
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HND & HAP).
  cbn [set_spill r_calls r_spill l_calls l_spill l_answer l_reply] in C1, C2, C3, C4, C5.
  assert (Ls : ls = []).
  { destruct C5 as (_ & _ & L5 & _). cbn [snd length] in L5.
    destruct ls as [|q ls]; [reflexivity | cbn [length] in L5; discriminate]. }
  subst ls.
  exists (RLay lc [(p1, n1); (p2, n2)] la lr). split.
  2: { intros pn. exact (spc5_iff2 O0 (concat lc) (oblk la ++ oblk lr) (p1, n1) (p2, n2) HO pn). }
  pose proof G3 as G3'. unfold iv_apart, REC_SIZE, SC_SIZE in G3'.
  unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in KG.
  assert (KR : forall y, A_G_REC <= y < A_G_REC + 8 \/ A_G_REC + 912 <= y < A_G_REC + 960 -> rdA y = rdB y).
  { intros y Hy. apply KG; [left; lia | intros Hlt; lia | lia]. }
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn (ablocks B lyA SA) /\
    forall i, 0 <= i < snd pn -> rdA (fst pn + i) = rdB (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (spc_rest_keep _ _ rdB rdA (set_spill R (fst (r_spill R), [])) (RLay lc [] la lr) Ha Hr HX KR KO)
    as (RA & RP & RX).
  unfold arep_at, ag1_calls, ag1_own.
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
    exact (spc5_own2 (concat lc) (oblk la ++ oblk lr) p1 n1 p2 n2 HND HAP F1' F2' P12 A11 A12 A21 A22). }
  split; [exact C1|]. split; [exact C2|].
  split; [apply (spc_aval_in rdB); [exact C3 |
    intros y Hy; unfold OFF_NCALLS in Hy; apply KG; [left; lia | intros Hlt; lia | lia]]|].
  split.
  { intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (spc_call_kept _ _ rdB rdA _ c P Hc).
    - intros y Hy. unfold OFF_CALLS, CALL_SIZE in Hy. apply KG; [left; lia | intros Hlt; lia | lia].
    - intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
      apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
  split.
  { exact (spc5_call2 _ rdA _ FN x d p1 n1 p2 n2 Hfn BF BA B1 B2 S1 S2 Z1 Z2 P1 P2 P12 Hin1 Hin2). }
  constructor; [exact Lx | constructor; [exact Ld | constructor]].
Qed.

End d.
