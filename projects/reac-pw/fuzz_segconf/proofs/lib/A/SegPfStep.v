(* segconf's printf grammar (lib/A/Rt/RtPFSeg.v: seg_piece, seg_parse, seg_step, seg_text, seg_prec_pos) one piece at a
   time, in the form lib/A/FMpfStep.v gives the released grammar (RtPFPf.v) to the route's per-piece arms:
   - seg_text is the steps one after the other (seg_text_step) and a step consumes a prefix of the arguments;
   - seg_code q is the format bytes seg_parse reads q from, so a parsed format is its pieces' codes (seg_parse_split),
     every piece has its code_ok and every byte of a parsed format is a nonzero byte (seg_parse_bytes);
   - the released pieces embed: at PRel p the step and the code are FMpfStep's pf_step / pf_code, seg_parse reads a
     format pf_parse reads to the same pieces under PRel, and seg_text / seg_prec_pos agree with pf_text /
     pf_prec_pos there.
   Pure: no machine state, no image value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMpfStep.
Import ListNotations.
Open Scope Z_scope.

Module PFS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMpfStep.

(* ---- the renderer, one piece ---- *)
Lemma seg_text_step : forall q qs args,
  seg_text (q :: qs) args =
  match seg_step q args with Some (c, a') => option_map (app c) (seg_text qs a') | None => None end.
Proof. reflexivity. Qed.

(* at PRel p the step is the released one *)
Lemma seg_step_PRel : forall p args, seg_step (PRel p) args = PFS.pf_step p args.
Proof.
intros p args. destruct p; cbn [seg_step PFS.pf_step]; [reflexivity | ..];
  destruct args as [|[v|u|s] [|[v'|u'|s'] a'']]; reflexivity.
Qed.

(* a step consumes a prefix of the arguments *)
Lemma seg_step_prefix : forall q args c a', seg_step q args = Some (c, a') -> exists used, args = used ++ a'.
Proof.
intros [p| | |] args c a' H.
- rewrite seg_step_PRel in H. exact (PFS.pf_step_prefix p args c a' H).
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as _ <-. exists [AInt v]. reflexivity.
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as _ <-. exists [AU64 u]. reflexivity.
- destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
  injection H as _ <-. exists [APtr s]. reflexivity.
Qed.

(* the text of released pieces is the released text *)
Lemma seg_text_PRel : forall ps args, seg_text (map PRel ps) args = pf_text ps args.
Proof.
induction ps as [|p ps IH]; intros args; [reflexivity|].
rewrite PFS.pf_text_step. cbn [map]. rewrite seg_text_step, seg_step_PRel.
destruct (PFS.pf_step p args) as [[c a']|]; [rewrite IH; reflexivity | reflexivity].
Qed.

(* a format the released parser reads, the segconf parser reads to the same pieces *)
Lemma seg_parse_PRel : forall f ps, pf_parse f = Some ps -> seg_parse f = Some (map PRel ps).
Proof.
fix IH 1. intros f ps H. destruct f as [|b r]; [cbn in H |- *; injection H as <-; reflexivity|].
cbn [pf_parse] in H. cbn [seg_parse].
assert (T : forall k k' r' (ps' : list pf_piece), k' = PRel k ->
          (forall q, pf_parse r' = Some q -> seg_parse r' = Some (map PRel q)) ->
          option_map (cons k) (pf_parse r') = Some ps' -> option_map (cons k') (seg_parse r') = Some (map PRel ps')).
{ intros k k' r' ps' -> HR E. destruct (pf_parse r') as [q|] eqn:Eq; [|discriminate E].
  cbn in E. injection E as <-. rewrite (HR q eq_refl). reflexivity. }
destruct (b =? 37).
- destruct r as [|c r1]; [discriminate H|].
  destruct (c =? 100); [exact (T _ _ _ _ eq_refl (IH r1) H)|].
  destruct (c =? 99); [exact (T _ _ _ _ eq_refl (IH r1) H)|].
  destruct (c =? 115); [exact (T _ _ _ _ eq_refl (IH r1) H)|].
  destruct (Z.eqb_spec c 117) as [->|N117]; [cbn in H; discriminate H|].
  destruct (c =? 48).
  + destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 52) && (c3 =? 120)); [exact (T _ _ _ _ eq_refl (IH r3) H)|].
    destruct ((c2 =? 50) && (c3 =? 120)); [exact (T _ _ _ _ eq_refl (IH r3) H) | discriminate H].
  + destruct (c =? 108).
    * destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
      destruct ((c2 =? 108) && (c3 =? 117)); [exact (T _ _ _ _ eq_refl (IH r3) H) | discriminate H].
    * destruct (Z.eqb_spec c 122) as [->|N122]; [cbn in H; discriminate H|].
      destruct (c =? 46); [|discriminate H].
      destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
      destruct ((c2 =? 42) && (c3 =? 115)); [exact (T _ _ _ _ eq_refl (IH r3) H) | discriminate H].
- destruct ((0 <? b) && (b <? 256)); [exact (T _ _ _ _ eq_refl (IH r) H) | discriminate H].
Qed.

Lemma seg_prec_pos_PRel : forall ps args, seg_prec_pos (map PRel ps) args <-> pf_prec_pos ps args.
Proof.
induction ps as [|p ps IH]; intros args; [split; intros _; exact I|].
destruct p; cbn [map].
1: cbn [seg_prec_pos pf_prec_pos]; apply IH.
1-6: destruct args as [|a args']; cbn [seg_prec_pos pf_prec_pos]; [split; intros _; exact I | apply IH].
destruct args as [|[k|u|s] [|a2 a'']]; cbn [seg_prec_pos pf_prec_pos]; try (split; intros _; exact I).
split; intros [H1 H2]; (split; [exact H1 | apply IH; exact H2]).
Qed.

(* ---- the parser, one piece ---- *)
Definition seg_code (q : seg_piece) : list Z :=
  match q with
  | PRel p => PFS.pf_code p | Pu => [37; 117] | Pzu => [37; 122; 117] | P24s => [37; 46; 50; 52; 115]
  end.

(* a literal byte is a nonzero byte other than '%' *)
Definition seg_code_ok (q : seg_piece) : Prop := match q with PRel p => PFS.pf_code_ok p | _ => True end.

Lemma seg_parse_nil : forall fmt, seg_parse fmt = Some [] -> fmt = [].
Proof.
intros [|b r] H; [reflexivity|]. exfalso. cbn [seg_parse] in H.
destruct (b =? 37).
- destruct r as [|c r1]; [discriminate H|].
  destruct (c =? 100); [destruct (seg_parse r1); discriminate H|].
  destruct (c =? 99); [destruct (seg_parse r1); discriminate H|].
  destruct (c =? 115); [destruct (seg_parse r1); discriminate H|].
  destruct (c =? 117); [destruct (seg_parse r1); discriminate H|].
  destruct (c =? 48).
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 52) && (c3 =? 120)); [destruct (seg_parse r3); discriminate H|].
    destruct ((c2 =? 50) && (c3 =? 120)); [destruct (seg_parse r3); discriminate H | discriminate H]. }
  destruct (c =? 108).
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 108) && (c3 =? 117)); [destruct (seg_parse r3); discriminate H | discriminate H]. }
  destruct (c =? 122).
  { destruct r1 as [|c2 r2]; [discriminate H|].
    destruct (c2 =? 117); [destruct (seg_parse r2); discriminate H | discriminate H]. }
  destruct (c =? 46); [|discriminate H].
  destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
  destruct ((c2 =? 42) && (c3 =? 115)); [destruct (seg_parse r3); discriminate H|].
  destruct ((c2 =? 50) && (c3 =? 52)); [|discriminate H].
  destruct r3 as [|c4 r4]; [discriminate H|].
  destruct (c4 =? 115); [destruct (seg_parse r4); discriminate H | discriminate H].
- destruct ((0 <? b) && (b <? 256)); [destruct (seg_parse r); discriminate H | discriminate H].
Qed.

Lemma seg_parse_split : forall fmt q qs, seg_parse fmt = Some (q :: qs) ->
  exists r, fmt = seg_code q ++ r /\ seg_parse r = Some qs /\ seg_code_ok q.
Proof.
intros [|b r] q qs H; [discriminate H|]. cbn [seg_parse] in H.
assert (T : forall k r', option_map (cons k) (seg_parse r') = Some (q :: qs) -> k = q /\ seg_parse r' = Some qs).
{ intros k r' E. destruct (seg_parse r'); cbn in E; [injection E as -> ->; split; reflexivity | discriminate E]. }
destruct (Z.eqb_spec b 37) as [->|N37].
- destruct r as [|c r1]; [discriminate H|].
  destruct (Z.eqb_spec c 100) as [->|_].
  { destruct (T _ _ H) as [<- E]. exists r1. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 99) as [->|_].
  { destruct (T _ _ H) as [<- E]. exists r1. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 115) as [->|_].
  { destruct (T _ _ H) as [<- E]. exists r1. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 117) as [->|_].
  { destruct (T _ _ H) as [<- E]. exists r1. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 48) as [->|_].
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 52) && (c3 =? 120)) eqn:E4.
    - apply andb_true_iff in E4 as [E4a E4b]. apply Z.eqb_eq in E4a, E4b. subst c2 c3.
      destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I].
    - destruct ((c2 =? 50) && (c3 =? 120)) eqn:E2; [|discriminate H].
      apply andb_true_iff in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
      destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 108) as [->|_].
  { destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct ((c2 =? 108) && (c3 =? 117)) eqn:E8; [|discriminate H].
    apply andb_true_iff in E8 as [E8a E8b]. apply Z.eqb_eq in E8a, E8b. subst c2 c3.
    destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 122) as [->|_].
  { destruct r1 as [|c2 r2]; [discriminate H|].
    destruct (Z.eqb_spec c2 117) as [->|_]; [|discriminate H].
    destruct (T _ _ H) as [<- E]. exists r2. split; [reflexivity|]. split; [exact E | exact I]. }
  destruct (Z.eqb_spec c 46) as [->|_]; [|discriminate H].
  destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
  destruct ((c2 =? 42) && (c3 =? 115)) eqn:E6.
  + apply andb_true_iff in E6 as [E6a E6b]. apply Z.eqb_eq in E6a, E6b. subst c2 c3.
    destruct (T _ _ H) as [<- E]. exists r3. split; [reflexivity|]. split; [exact E | exact I].
  + destruct ((c2 =? 50) && (c3 =? 52)) eqn:E5; [|discriminate H].
    apply andb_true_iff in E5 as [E5a E5b]. apply Z.eqb_eq in E5a, E5b. subst c2 c3.
    destruct r3 as [|c4 r4]; [discriminate H|].
    destruct (Z.eqb_spec c4 115) as [->|_]; [|discriminate H].
    destruct (T _ _ H) as [<- E]. exists r4. split; [reflexivity|]. split; [exact E | exact I].
- destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|discriminate H].
  apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
  destruct (T _ _ H) as [<- E]. exists r. split; [reflexivity|]. split; [exact E|]. cbn. lia.
Qed.

(* every piece of a parsed format has its code_ok *)
Lemma seg_parse_codes : forall qs fmt, seg_parse fmt = Some qs -> Forall seg_code_ok qs.
Proof.
induction qs as [|q qs IH]; intros fmt H; [constructor|].
destruct (seg_parse_split fmt q qs H) as (r & _ & Hr & Hok).
constructor; [exact Hok | exact (IH r Hr)].
Qed.

(* every byte of a piece's code is a nonzero byte *)
Lemma seg_code_bytes : forall q, seg_code_ok q -> Forall (fun c => 0 < c < 256) (seg_code q).
Proof.
intros [[b| | | | | | |]| | |] Hok; cbn [seg_code PFS.pf_code];
  [cbn [seg_code_ok PFS.pf_code_ok] in Hok; constructor; [cbv beta; lia | constructor] | ..];
  repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.
Qed.

(* every byte of a parsed format is a nonzero byte *)
Lemma seg_parse_bytes : forall fmt qs, seg_parse fmt = Some qs -> Forall (fun c => 0 < c < 256) fmt.
Proof.
intros fmt qs. revert fmt. induction qs as [|q qs IH]; intros fmt H.
- rewrite (seg_parse_nil fmt H). constructor.
- destruct (seg_parse_split fmt q qs H) as (r & -> & Hr & Hok).
  apply Forall_app. split; [exact (seg_code_bytes q Hok) | exact (IH r Hr)].
Qed.

(* a parsed format with its NUL is bytes *)
Lemma seg_parse_bytes0 : forall fmt qs, seg_parse fmt = Some qs -> Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof.
intros fmt qs H. apply Forall_app. split.
- eapply Forall_impl; [|exact (seg_parse_bytes fmt qs H)]. intros c Hc. cbv beta in *. lia.
- constructor; [lia | constructor].
Qed.

(* every piece's code is at least one byte long *)
Lemma seg_code_len : forall q, (1 <= length (seg_code q))%nat.
Proof. intros [[b| | | | | | |]| | |]; cbn; lia. Qed.
