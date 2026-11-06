(* sup_call's recorder step in the ASan build: from "the bytes of g_rec / record.spill now hold the new call" to the
   recorder's representation `rec_repA` (lib/A/Prog/CmdRep.v) of the model state after `rec_record`
   (lib/Prog/RecModel.v:38-39). Pure reasoning over the layout of lib/Prog/RecInv.v:9-37: no machine semantics.

   sc_rep_slot is record()'s table arm (recorder.c: g_rec.calls[n] = the call, ncalls = n + 1, n < 16);
   sc_rep_spill is its spill arm (the table holds 16 calls: rec_calls_free freed the spill's old argument blocks and
   the call went to record.spill). In both the call has two string arguments in two fresh blocks. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.

(* Frames: a field, a byte string or a recorded call reads the same through two readers that agree on its bytes. *)
Lemma sc_aval_frame : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H F k Hk. rewrite F by lia. exact (H k Hk). Qed.

Lemma sc_bytes_frame : forall (rd rd' : reader) p l, abytes_atR rd p l ->
(forall x, p <= x < p + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H F i Hi. rewrite F by lia. exact (H i Hi). Qed.

Lemma sc_str_frame : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H Hn] F. split; [|exact Hn].
apply (sc_bytes_frame rd); [exact H|]. intros x Hx. apply F. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sc_call_frame : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Fb Fs Fp.
unfold CALL_SIZE in Fs. unfold acall_at.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (sc_aval_frame rd); [exact H4 | intros x Hx; apply Fs; unfold CALL_OFF_FN in Hx; lia]|].
split; [apply (sc_aval_frame rd); [exact H5 | intros x Hx; apply Fs; unfold CALL_OFF_NARGS in Hx; lia]|].
split; [exact H6|].
intros k s pn Hs Hp. destruct (H7 k s pn Hs Hp) as (G1 & G2 & G3 & G4 & G5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
assert (Hin : In pn P) by (eapply nth_error_In; exact Hp).
split; [apply (sc_aval_frame rd); [exact G1 | intros x Hx; apply Fs; unfold CALL_OFF_ARGS in Hx; lia]|].
split; [exact G2|]. split; [exact (Fb pn Hin)|]. split; [exact G4|].
apply (sc_str_frame rd); [exact G5|]. intros x Hx. apply (Fp pn x Hin). lia.
Qed.

Lemma sc_answer_frame : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Fb Fg Fp.
destruct t as [x|], q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
- destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [apply (sc_aval_frame rd); [exact H1 | intros y Hy; apply Fg; lia]|].
  split; [exact H2|]. split; [exact (Fb pn eq_refl)|]. split; [exact H4|]. split; [|exact H6].
  apply (sc_str_frame rd); [exact H5|]. intros y Hy. apply (Fp pn y eq_refl). lia.
- apply (sc_aval_frame rd); [exact H | intros y Hy; apply Fg; lia].
Qed.

Lemma sc_reply_frame : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Fb Fg Fp. unfold OFF_REPLY in Fg.
destruct y as [x|], q as [pn|]; cbn [areply_at] in H |- *; try contradiction.
- destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [apply (sc_aval_frame rd); [exact H1 | intros z Hz; apply Fg; unfold OFF_REPLY in Hz; lia]|].
  split; [apply (sc_aval_frame rd); [exact H2 | intros z Hz; apply Fg; unfold OFF_REPLY_SIZE in Hz; lia]|].
  split; [exact H3|]. split; [exact H4|]. split; [exact (Fb pn eq_refl)|]. split; [exact H6|]. split; [|exact H8].
  apply (sc_bytes_frame rd); [exact H7|]. intros z Hz. apply (Fp pn z eq_refl). lia.
- destruct H as [H1 H2]. split.
  + apply (sc_aval_frame rd); [exact H1 | intros z Hz; apply Fg; unfold OFF_REPLY in Hz; lia].
  + apply (sc_aval_frame rd); [exact H2 | intros z Hz; apply Fg; unfold OFF_REPLY_SIZE in Hz; lia].
Qed.

Lemma sc_scalars_frame : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, (gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960) -> rd' x = rd x) ->
ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (H1 & H2 & H3 & H4 & H5 & H6) F. unfold ag1_scalars.
refine (conj _ (conj _ (conj _ (conj _ (conj _ H6))))); apply (sc_aval_frame rd); try eassumption;
intros x Hx; apply F; unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in Hx; lia.
Qed.

(* Every block the layout names is a live block of positive size. *)
Lemma sc_call_blocks : forall bl (rd : reader) a c P, acall_at bl rd a c P ->
forall pn, In pn P -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H7) pn Hin.
apply In_nth_error in Hin as [k Hk].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma sc_rep_blocks : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & (_ & HL & _ & HC & HS & _) & HA & HR & _) pn Hin.
unfold lay_blocks in Hin. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|[Hin|Hin]]].
- apply in_concat in Hin. destruct Hin as (P & HP & Hpn).
  apply In_nth_error in HP as [i Hi].
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + exact (sc_call_blocks _ _ _ _ _ (proj1 (HC i c P Hc Hi)) pn Hpn).
  + apply nth_error_None in Hc.
    assert (Hlt : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). lia.
- exact (sc_call_blocks _ _ _ _ _ HS pn Hin).
- destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn [aanswer_at oblk In] in HA, Hin; try contradiction.
  destruct Hin as [<-|[]]. destruct HA as (_ & _ & H3 & H4 & _). split; [exact H3 | lia].
- destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn [areply_at oblk In] in HR, Hin; try contradiction.
  destruct Hin as [<-|[]]. destruct HR as (_ & _ & _ & H4 & H5 & H6 & _). split; [exact H5|].
  destruct x as [|b x]; [exfalso; apply H4; reflexivity|]. cbn [length] in H6. lia.
Qed.

(* The layout without the spill's blocks. *)
Definition sc_rest (Q : rlay) : list (Z * Z) := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q).

Lemma sc_rest_in : forall Q pn, In pn (sc_rest Q) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold sc_rest in H. unfold lay_blocks.
apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right]. apply in_or_app; right; exact H.
Qed.

Lemma sc_rest_of : forall Q pn, In pn (lay_blocks Q) -> ~ In pn (l_spill Q) -> In pn (sc_rest Q).
Proof.
intros Q pn H N. unfold lay_blocks in H. unfold sc_rest.
apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right].
apply in_app_or in H as [H|H]; [contradiction | exact H].
Qed.

Lemma sc_rest_ans : forall Q pn, l_answer Q = Some pn -> In pn (sc_rest Q).
Proof.
intros Q pn E. unfold sc_rest. rewrite E. apply in_or_app; right. apply in_or_app; left. cbn [oblk]. left; reflexivity.
Qed.

Lemma sc_rest_rep : forall Q pn, l_reply Q = Some pn -> In pn (sc_rest Q).
Proof.
intros Q pn E. unfold sc_rest. rewrite E. apply in_or_app; right. apply in_or_app; right. cbn [oblk]. left; reflexivity.
Qed.

Lemma sc_rest_call : forall Q P pn, In P (l_calls Q) -> In pn P -> In pn (sc_rest Q).
Proof. intros Q P pn HP Hpn. unfold sc_rest. apply in_or_app; left. apply in_concat. exists P. split; assumption. Qed.

Lemma sc_rest_perm : forall Q, Permutation (lay_blocks Q) (l_spill Q ++ sc_rest Q).
Proof. intros Q. unfold lay_blocks, sc_rest. apply Permutation_app_swap_app. Qed.

Lemma sc_nodup_disj : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1 l2 x. induction l1 as [|y l1 IH]; intros HN H1 H2; [destruct H1|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [Hy HN']. destruct H1 as [<-|H1].
- apply Hy. apply in_or_app. right; exact H2.
- exact (IH HN' H1 H2).
Qed.

Lemma sc_rest_nodup : forall Q, List.NoDup (map fst (lay_blocks Q)) -> List.NoDup (map fst (sc_rest Q)).
Proof.
intros Q H. pose proof (Permutation_NoDup (Permutation_map fst (sc_rest_perm Q)) H) as H'.
rewrite map_app in H'. exact (List.NoDup_app_remove_l _ _ H').
Qed.

(* ag1_own's NoDup of the block starts is what keeps the spill's blocks out of the rest of the layout. *)
Lemma sc_rest_nsp : forall Q, List.NoDup (map fst (lay_blocks Q)) -> forall pn, In pn (sc_rest Q) -> ~ In pn (l_spill Q).
Proof.
intros Q H pn Hin Hsp. pose proof (Permutation_NoDup (Permutation_map fst (sc_rest_perm Q)) H) as H'.
rewrite map_app in H'. exact (sc_nodup_disj _ _ (fst pn) H' (in_map fst _ _ Hsp) (in_map fst _ _ Hin)).
Qed.

Lemma sc_slot_perm : forall Q P,
Permutation (lay_blocks (RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q))) (P ++ lay_blocks Q).
Proof.
intros Q P. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
rewrite app_nil_r, <- app_assoc. apply Permutation_app_swap_app.
Qed.

Lemma sc_spill_perm : forall Q P,
Permutation (lay_blocks (RLay (l_calls Q) P (l_answer Q) (l_reply Q))) (P ++ sc_rest Q).
Proof. intros Q P. unfold lay_blocks, sc_rest. cbn [l_calls l_spill l_answer l_reply]. apply Permutation_app_swap_app. Qed.

(* Two new blocks of positive size, apart from every live block and from each other, start where no block of the
   old layout starts. *)
Lemma sc_nodup_new : forall (L bl : list (Z * Z)) p1 n1 p2 n2,
List.NoDup (map fst L) -> (forall pn, In pn L -> In pn bl /\ 0 < snd pn) ->
Forall (fun qk => iv_apart p1 n1 (fst qk) (snd qk)) bl ->
Forall (fun qk => iv_apart p2 n2 (fst qk) (snd qk)) ((p1, n1) :: bl) ->
0 < n1 -> 0 < n2 ->
List.NoDup (map fst ([(p1, n1); (p2, n2)] ++ L)).
Proof.
intros L bl p1 n1 p2 n2 HN HL H1 H2 Hn1 Hn2. rewrite Forall_forall in H1, H2. cbn [app map fst].
apply List.NoDup_cons; [|apply List.NoDup_cons; [|exact HN]].
- intros [E|Hin].
  + specialize (H2 (p1, n1) (or_introl eq_refl)). cbn [fst snd] in H2. unfold iv_apart in H2. lia.
  + apply in_map_iff in Hin. destruct Hin as (pn & Ep & Hpn). destruct (HL pn Hpn) as [Hb Hs].
    specialize (H1 pn Hb). unfold iv_apart in H1. lia.
- intros Hin. apply in_map_iff in Hin. destruct Hin as (pn & Ep & Hpn). destruct (HL pn Hpn) as [Hb Hs].
  specialize (H2 pn (or_intror Hb)). unfold iv_apart in H2. lia.
Qed.

(* The new call (REC_CALL, [s1; s2]) at a: both arms store it the same way. *)
Lemma sc_call_new : forall bl (rd : reader) a s1 s2 p1 p2 n1 n2,
Z.of_nat (length s1) + 1 <= n1 <= LMAX + 2 -> Z.of_nat (length s2) + 1 <= n2 <= LMAX + 2 ->
In (p1, n1) bl -> In (p2, n2) bl -> iv_apart p2 n2 p1 n1 ->
4096 <= p1 -> 4096 <= p2 -> Z.of_nat (length s1) <= LMAX -> Z.of_nat (length s2) <= LMAX ->
aval_mem rd (a + CALL_OFF_FN) 4 REC_CALL -> aval_mem rd (a + CALL_OFF_NARGS) 4 2 ->
aval_mem rd (a + CALL_OFF_ARGS) 8 p1 -> aval_mem rd (a + CALL_OFF_ARGS + 8) 8 p2 ->
astr_atR rd p1 s1 -> astr_atR rd p2 s2 ->
acall_at bl rd a (REC_CALL, [s1; s2]) [(p1, n1); (p2, n2)] /\
Forall (fun s => Z.of_nat (length s) <= LMAX) [s1; s2].
Proof.
intros bl rd a s1 s2 p1 p2 n1 n2 En1 En2 Hb1 Hb2 Hap Hp1 Hp2 Hl1 Hl2 Hfn Hna Ha1 Ha2 Hst1 Hst2.
split; [|constructor; [exact Hl1 | constructor; [exact Hl2 | constructor]]].
unfold acall_at. cbn [fst snd length map].
split; [unfold REC_CALL, REC_FN_COUNT; lia|].
split; [lia|]. split; [reflexivity|].
split; [exact Hfn|]. split; [exact Hna|].
split.
{ apply NoDup_ListNoDup. apply List.NoDup_cons; [|apply List.NoDup_cons; [intros [] | apply List.NoDup_nil]].
  intros [E|[]]. unfold iv_apart in Hap. lia. }
intros k s pn Hs Hpn. destruct k as [|[|k]].
3:{ exfalso. destruct k; cbn in Hs; discriminate. }
- cbn [nth_error] in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [replace (a + CALL_OFF_ARGS + 8 * Z.of_nat 0) with (a + CALL_OFF_ARGS) by lia; exact Ha1|].
  split; [lia|]. split; [exact Hb1|]. split; [lia|]. exact Hst1.
- cbn [nth_error] in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [replace (a + CALL_OFF_ARGS + 8 * Z.of_nat 1) with (a + CALL_OFF_ARGS + 8) by lia; exact Ha2|].
  split; [lia|]. split; [exact Hb2|]. split; [lia|]. exact Hst2.
Qed.

Section d.
Variable B : asyms.

(* record() stored the new call in slot n of g_rec's table (n < 16): the table now holds one call more,
   with the two argument blocks (p1, n1) and (p2, n2). *)
Lemma sc_rep_slot : forall ly S (rd : reader) ly' S' (rd' : reader) (R : rstate) (Q : rlay) (O : list (Z * Z))
  (s1 s2 : list byte) (p1 p2 n1 n2 : Z),
let n := Z.of_nat (length (r_calls R)) in
let c := A_G_REC + OFF_CALLS + CALL_SIZE * n in
arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
(length (r_calls R) < 16)%nat ->
Permutation (ablocks B ly' S') ((p2, n2) :: (p1, n1) :: ablocks B ly S) ->
Forall (fun qk => iv_apart p1 n1 (fst qk) (snd qk)) (ablocks B ly S) ->
Forall (fun qk => iv_apart p2 n2 (fst qk) (snd qk)) ((p1, n1) :: ablocks B ly S) ->
iv_apart p1 n1 A_G_REC REC_SIZE -> iv_apart p1 n1 A_REC_SPILL SC_SIZE ->
iv_apart p2 n2 A_G_REC REC_SIZE -> iv_apart p2 n2 A_REC_SPILL SC_SIZE ->
4096 <= p1 -> 4096 <= p2 ->
Z.of_nat (length s1) + 1 <= n1 <= LMAX + 2 -> Z.of_nat (length s2) + 1 <= n2 <= LMAX + 2 ->
Z.of_nat (length s1) <= LMAX -> Z.of_nat (length s2) <= LMAX ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (n + 1) ->
aval_mem rd' (c + CALL_OFF_FN) 4 REC_CALL ->
aval_mem rd' (c + CALL_OFF_NARGS) 4 2 ->
aval_mem rd' (c + CALL_OFF_ARGS) 8 p1 ->
aval_mem rd' (c + CALL_OFF_ARGS + 8) 8 p2 ->
astr_atR rd' p1 s1 -> astr_atR rd' p2 s2 ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
   ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p m i, In (p, m) (ablocks B ly S) -> 0 <= i < m -> rd' (p + i) = rd (p + i)) ->
exists O', rec_repA B ly' S' rd' (rec_record R REC_CALL [s1; s2]) O' /\
  (forall pn, In pn O' <-> (In pn O \/ pn = (p1, n1) \/ pn = (p2, n2))).
Proof.
intros ly S rd ly' S' rd' R Q O s1 s2 p1 p2 n1 n2 n c
  HR HO Hlt Hperm Hap1 Hap2 Hg1 Hs1 Hg2 Hs2 Hp1 Hp2 En1 En2 Hl1 Hl2 Hnc Hfn Hna Ha1 Ha2 Hst1 Hst2 Fg Fs Fb.
assert (En : n = Z.of_nat (length (r_calls R))) by reflexivity.
assert (Ec : c = A_G_REC + OFF_CALLS + CALL_SIZE * n) by reflexivity.
clearbody n c.
assert (ER : rec_record R REC_CALL [s1; s2] = set_calls R (r_calls R ++ [(REC_CALL, [s1; s2])])).
{ unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16); [reflexivity | lia]. }
rewrite ER. clear ER.
pose proof (sc_rep_blocks _ _ _ _ _ _ HR) as HQb.
destruct HR as (Hgm & Hsm & Hgs & (HC1 & HC2 & HC3 & HC4 & HC5 & HC6) & HA & HRp & HSc & HN & HOwn).
apply NoDup_ListNoDup in HN.
assert (HQin : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by (intros pn H; exact (proj1 (HQb pn H))).
assert (Hin' : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')).
{ intros pn Hin. apply (Permutation_in _ (Permutation_sym Hperm)). right; right; exact Hin. }
assert (Hb1 : In (p1, n1) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym Hperm)). right; left; reflexivity. }
assert (Hb2 : In (p2, n2) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym Hperm)). left; reflexivity. }
assert (Fb' : forall pn x, In pn (ablocks B ly S) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros [p m] x Hin Hx. cbn [fst snd] in Hx. replace x with (p + (x - p)) by lia. apply (Fb p m); [exact Hin | lia]. }
assert (Hap21 : iv_apart p2 n2 p1 n1) by exact (proj1 (Forall_forall _ _) Hap2 (p1, n1) (or_introl eq_refl)).
pose proof (sc_slot_perm Q [(p1, n1); (p2, n2)]) as HPQ.
exists (lay_blocks (RLay (l_calls Q ++ [[(p1, n1); (p2, n2)]]) (l_spill Q) (l_answer Q) (l_reply Q))).
split.
2:{ intros pn. split.
  - intros Hin. apply (Permutation_in _ HPQ) in Hin. destruct Hin as [<-|[<-|Hin]].
    + right; left; reflexivity.
    + right; right; reflexivity.
    + left. exact (proj2 (HO pn) Hin).
  - intros [Hin|[ -> | -> ]]; apply (Permutation_in _ (Permutation_sym HPQ)).
    + right; right. exact (proj1 (HO pn) Hin).
    + left; reflexivity.
    + right; left; reflexivity. }
unfold rec_repA. exists (RLay (l_calls Q ++ [[(p1, n1); (p2, n2)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
split; [|intros pn; apply iff_refl].
unfold arep_at. split; [exact Hgm|]. split; [exact Hsm|]. split; [exact Hgs|].
split.
{ unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, HC2; reflexivity|].
  split.
  { replace (Z.of_nat (length (r_calls R ++ [(REC_CALL, [s1; s2])]))) with (n + 1)
      by (rewrite length_app; cbn [length]; lia).
    exact Hnc. }
  split.
  { intros i cc P Hc HP.
    destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
    - rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP by (rewrite HC2; exact Hi).
      destruct (HC4 i cc P Hc HP) as [Hcall Hf]. split; [|exact Hf].
      apply (sc_call_frame (ablocks B ly S) _ rd); [exact Hcall | | |].
      + intros pn Hpn. exact (Hin' pn (proj1 (sc_call_blocks _ _ _ _ _ Hcall pn Hpn))).
      + intros x Hx. apply Fg; unfold OFF_CALLS, CALL_SIZE, OFF_NCALLS, REC_SIZE in *; lia.
      + intros pn x Hpn Hx. exact (Fb' pn x (proj1 (sc_call_blocks _ _ _ _ _ Hcall pn Hpn)) Hx).
    - rewrite nth_error_app2 in Hc by exact Hi. rewrite nth_error_app2 in HP by (rewrite HC2; exact Hi).
      rewrite HC2 in HP.
      assert (Ei : i = length (r_calls R)).
      { revert Hc. case_eq (i - length (r_calls R))%nat; [intros E _; lia|].
        intros k E Hc. destruct k; cbn in Hc; discriminate Hc. }
      subst i. rewrite Nat.sub_diag in Hc, HP. cbn [nth_error] in Hc, HP.
      injection Hc as <-. injection HP as <-.
      rewrite <- En, <- Ec.
      exact (sc_call_new _ _ c s1 s2 p1 p2 n1 n2 En1 En2 Hb1 Hb2 Hap21 Hp1 Hp2 Hl1 Hl2 Hfn Hna Ha1 Ha2 Hst1 Hst2). }
  split; [|exact HC6].
  apply (sc_call_frame (ablocks B ly S) _ rd); [exact HC5 | | |].
  - intros pn Hpn. exact (Hin' pn (proj1 (sc_call_blocks _ _ _ _ _ HC5 pn Hpn))).
  - intros x Hx. apply Fs. unfold SC_SIZE, CALL_SIZE in *; lia.
  - intros pn x Hpn Hx. exact (Fb' pn x (proj1 (sc_call_blocks _ _ _ _ _ HC5 pn Hpn)) Hx). }
split.
{ apply (sc_answer_frame (ablocks B ly S) _ rd); [exact HA | | |].
  - intros pn Hq. exact (Hin' pn (HQin pn (sc_rest_in Q pn (sc_rest_ans Q pn Hq)))).
  - intros x Hx. apply Fg; unfold OFF_ANSWER, OFF_CALLS, CALL_SIZE, OFF_NCALLS, REC_SIZE in *; lia.
  - intros pn x Hq Hx. exact (Fb' pn x (HQin pn (sc_rest_in Q pn (sc_rest_ans Q pn Hq))) Hx). }
split.
{ apply (sc_reply_frame (ablocks B ly S) _ rd); [exact HRp | | |].
  - intros pn Hq. exact (Hin' pn (HQin pn (sc_rest_in Q pn (sc_rest_rep Q pn Hq)))).
  - intros x Hx. apply Fg; unfold OFF_REPLY, OFF_CALLS, CALL_SIZE, OFF_NCALLS, REC_SIZE in *; lia.
  - intros pn x Hq Hx. exact (Fb' pn x (HQin pn (sc_rest_in Q pn (sc_rest_rep Q pn Hq))) Hx). }
split.
{ apply (sc_scalars_frame rd); [exact HSc|]. intros x Hx.
  apply Fg; unfold OFF_CALLS, CALL_SIZE, OFF_NCALLS, REC_SIZE in *; lia. }
unfold ag1_own. split.
- apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HPQ))).
  apply (sc_nodup_new (lay_blocks Q) (ablocks B ly S)); try assumption; lia.
- intros pn Hin. apply (Permutation_in _ HPQ) in Hin. destruct Hin as [<-|[<-|Hin]].
  + cbn [fst snd]. split; assumption.
  + cbn [fst snd]. split; assumption.
  + exact (HOwn pn Hin).
Qed.

(* record()'s spill arm (the table holds 16 calls): rec_calls_free freed the spill's old argument blocks
   (l_spill Q) and the new call was stored in record.spill. *)
Lemma sc_rep_spill : forall ly S (rd : reader) ly' S' (rd' : reader) (R : rstate) (Q : rlay) (O : list (Z * Z))
  (s1 s2 : list byte) (p1 p2 n1 n2 : Z),
arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
length (r_calls R) = 16%nat ->
(forall pn, In pn (ablocks B ly' S') <->
   ((In pn (ablocks B ly S) /\ ~ In pn (l_spill Q)) \/ pn = (p1, n1) \/ pn = (p2, n2))) ->
(forall qk, In qk (ablocks B ly S) -> ~ In qk (l_spill Q) -> iv_apart p1 n1 (fst qk) (snd qk)) ->
iv_apart p2 n2 p1 n1 ->
(forall qk, In qk (ablocks B ly S) -> ~ In qk (l_spill Q) -> iv_apart p2 n2 (fst qk) (snd qk)) ->
iv_apart p1 n1 A_G_REC REC_SIZE -> iv_apart p1 n1 A_REC_SPILL SC_SIZE ->
iv_apart p2 n2 A_G_REC REC_SIZE -> iv_apart p2 n2 A_REC_SPILL SC_SIZE ->
4096 <= p1 -> 4096 <= p2 ->
Z.of_nat (length s1) + 1 <= n1 <= LMAX + 2 -> Z.of_nat (length s2) + 1 <= n2 <= LMAX + 2 ->
Z.of_nat (length s1) <= LMAX -> Z.of_nat (length s2) <= LMAX ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_CALL ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 2 ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS) 8 p1 ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS + 8) 8 p2 ->
astr_atR rd' p1 s1 -> astr_atR rd' p2 s2 ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall p m i, In (p, m) (ablocks B ly S) -> ~ In (p, m) (l_spill Q) -> 0 <= i < m -> rd' (p + i) = rd (p + i)) ->
exists O', rec_repA B ly' S' rd' (rec_record R REC_CALL [s1; s2]) O' /\
  (forall pn, In pn O' <-> ((In pn O /\ ~ In pn (l_spill Q)) \/ pn = (p1, n1) \/ pn = (p2, n2))).
Proof.
intros ly S rd ly' S' rd' R Q O s1 s2 p1 p2 n1 n2
  HR HO Hlen Hbl Hap1 Hap21 Hap2 Hg1 Hs1 Hg2 Hs2 Hp1 Hp2 En1 En2 Hl1 Hl2 Hfn Hna Ha1 Ha2 Hst1 Hst2 Fg Fb.
assert (ER : rec_record R REC_CALL [s1; s2] = set_spill R (REC_CALL, [s1; s2])).
{ unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
rewrite ER. clear ER.
pose proof (sc_rep_blocks _ _ _ _ _ _ HR) as HQb.
destruct HR as (Hgm & Hsm & Hgs & (HC1 & HC2 & HC3 & HC4 & HC5 & HC6) & HA & HRp & HSc & HN & HOwn).
apply NoDup_ListNoDup in HN.
pose proof (sc_rest_nsp Q HN) as Hnsp.
assert (Hin' : forall pn, In pn (sc_rest Q) -> In pn (ablocks B ly' S')).
{ intros pn Hin. apply Hbl. left. split; [exact (proj1 (HQb pn (sc_rest_in Q pn Hin))) | exact (Hnsp pn Hin)]. }
assert (Fb' : forall pn x, In pn (sc_rest Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros [p m] x Hin Hx. cbn [fst snd] in Hx. replace x with (p + (x - p)) by lia.
  apply (Fb p m); [exact (proj1 (HQb _ (sc_rest_in Q _ Hin))) | exact (Hnsp _ Hin) | lia]. }
assert (Hb1 : In (p1, n1) (ablocks B ly' S')) by (apply Hbl; right; left; reflexivity).
assert (Hb2 : In (p2, n2) (ablocks B ly' S')) by (apply Hbl; right; right; reflexivity).
pose proof (sc_spill_perm Q [(p1, n1); (p2, n2)]) as HPQ.
exists (lay_blocks (RLay (l_calls Q) [(p1, n1); (p2, n2)] (l_answer Q) (l_reply Q))).
split.
2:{ intros pn. split.
  - intros Hin. apply (Permutation_in _ HPQ) in Hin. destruct Hin as [<-|[<-|Hin]].
    + right; left; reflexivity.
    + right; right; reflexivity.
    + left. split; [exact (proj2 (HO pn) (sc_rest_in Q pn Hin)) | exact (Hnsp pn Hin)].
  - intros [[Hin Hsp]|[ -> | -> ]]; apply (Permutation_in _ (Permutation_sym HPQ)).
    + right; right. exact (sc_rest_of Q pn (proj1 (HO pn) Hin) Hsp).
    + left; reflexivity.
    + right; left; reflexivity. }
unfold rec_repA. exists (RLay (l_calls Q) [(p1, n1); (p2, n2)] (l_answer Q) (l_reply Q)).
split; [|intros pn; apply iff_refl].
unfold arep_at. split; [exact Hgm|]. split; [exact Hsm|]. split; [exact Hgs|].
split.
{ unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill].
  split; [exact HC1|]. split; [exact HC2|].
  split; [apply (sc_aval_frame rd); [exact HC3 | intros x Hx; apply Fg; unfold OFF_NCALLS, REC_SIZE in *; lia]|].
  split.
  { intros i cc P Hc HP. destruct (HC4 i cc P Hc HP) as [Hcall Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    assert (HPin : forall pn, In pn P -> In pn (sc_rest Q)).
    { intros pn Hpn. apply (sc_rest_call Q P pn); [eapply nth_error_In; exact HP | exact Hpn]. }
    apply (sc_call_frame (ablocks B ly S) _ rd); [exact Hcall | | |].
    - intros pn Hpn. exact (Hin' pn (HPin pn Hpn)).
    - intros x Hx. apply Fg. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia.
    - intros pn x Hpn Hx. exact (Fb' pn x (HPin pn Hpn) Hx). }
  exact (sc_call_new _ _ A_REC_SPILL s1 s2 p1 p2 n1 n2 En1 En2 Hb1 Hb2 Hap21 Hp1 Hp2 Hl1 Hl2 Hfn Hna Ha1 Ha2 Hst1 Hst2). }
split.
{ apply (sc_answer_frame (ablocks B ly S) _ rd); [exact HA | | |].
  - intros pn Hq. exact (Hin' pn (sc_rest_ans Q pn Hq)).
  - intros x Hx. apply Fg. unfold OFF_ANSWER, REC_SIZE in *; lia.
  - intros pn x Hq Hx. exact (Fb' pn x (sc_rest_ans Q pn Hq) Hx). }
split.
{ apply (sc_reply_frame (ablocks B ly S) _ rd); [exact HRp | | |].
  - intros pn Hq. exact (Hin' pn (sc_rest_rep Q pn Hq)).
  - intros x Hx. apply Fg. unfold OFF_REPLY, REC_SIZE in *; lia.
  - intros pn x Hq Hx. exact (Fb' pn x (sc_rest_rep Q pn Hq) Hx). }
split.
{ apply (sc_scalars_frame rd); [exact HSc|]. intros x Hx. apply Fg. unfold REC_SIZE; lia. }
unfold ag1_own. split.
- apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HPQ))).
  apply (sc_nodup_new (sc_rest Q) (sc_rest Q)); [exact (sc_rest_nodup Q HN) | | | | lia | lia].
  + intros pn Hin. split; [exact Hin | exact (proj2 (HQb pn (sc_rest_in Q pn Hin)))].
  + apply Forall_forall. intros qk Hq. exact (Hap1 qk (proj1 (HQb qk (sc_rest_in Q qk Hq))) (Hnsp qk Hq)).
  + constructor; [exact Hap21|]. apply Forall_forall. intros qk Hq.
    exact (Hap2 qk (proj1 (HQb qk (sc_rest_in Q qk Hq))) (Hnsp qk Hq)).
- intros pn Hin. apply (Permutation_in _ HPQ) in Hin. destruct Hin as [<-|[<-|Hin]].
  + cbn [fst snd]. split; assumption.
  + cbn [fst snd]. split; assumption.
  + exact (HOwn pn (sc_rest_in Q pn Hin)).
Qed.
End d.

Print Assumptions sc_rep_slot.
Print Assumptions sc_rep_spill.
