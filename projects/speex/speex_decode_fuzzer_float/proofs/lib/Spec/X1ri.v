(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Export X1rk.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.
Definition INTERNAL_BUFSIZ : Z := 80.

Definition WRITEV_MAX : Z := 2^26.

Record stdout_st := mkStdout {
so_active : bool;
so_buf : list Z;
so_lbf_nl : bool;
so_first : bool
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.

Definition wv_iovs (buf s : list Z) : list (list Z) :=
match buf with [] => [s] | _ => [buf; s] end.

Definition wv_total (iovs : list (list Z)) : Z := zlength (concat iovs).

Definition wv_advance (cnt : Z) (iovs : list (list Z)) : list (list Z) :=
match iovs with
| [] => []
| v :: rest =>
if zlength v <? cnt
then match rest with
| [] => []
| v2 :: rest' => skipn (Z.to_nat (cnt - zlength v)) v2 :: rest'
end
else skipn (Z.to_nat cnt) v :: rest
end.

Section Stdio.
Context {St : Type}.
Let M := @M St.

Fixpoint stdio_wloop (fuel : nat) (fd : Z) (iovs : list (list Z)) : M unit :=
match fuel with
| O => munr
| S fuel' =>
cnt <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (wv_total iovs)) ;;
if cnt =? wv_total iovs then mret tt
else stdio_wloop fuel' fd (wv_advance cnt iovs)
end.

Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
if WRITEV_MAX <? zlength buf + zlength s then munr
else stdio_wloop (S (length buf + length s)) fd (wv_iovs buf s).

Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

Definition stdout_stdio_write (s : list Z) : M unit :=
so <- rd_so ;;
stdio_writev 1 (so_buf so) s ;;;
upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_writefn (s : list Z) : M unit :=
so <- rd_so ;;
(if so_first so then
upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
match r with
| SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
| SVal _ => munr
end
else mret tt) ;;;
stdout_stdio_write s.

Definition after_last_nl (s : list Z) : Z :=
fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
(combine (map Z.of_nat (seq 0 (length s))) s) 0.

Definition stdout_towrite : M unit :=
upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_fwritex (s : list Z) : M unit :=
stdout_towrite ;;;
so <- rd_so ;;
if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
then stdout_writefn s
else if so_lbf_nl so then
let i := after_last_nl s in
(if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
upd_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
else
upd_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Fixpoint out_pieces (ps : list (list Z)) : M unit :=
match ps with
| [] => mret tt
| p :: ps' => stdout_fwritex p ;;; out_pieces ps'
end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
stdout_towrite ;;; out_pieces pieces.

Definition stdout_exit_flush : M unit :=
so <- rd_so ;;
if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
match ps with
| [] => mret buf
| p :: ps' =>
if INTERNAL_BUFSIZ - zlength buf <? zlength p
then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
else stderr_pieces (buf ++ p) ps'
end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
buf <- stderr_pieces [] pieces ;;
stdio_writev 2 buf [].

Definition stderr_fwrite (s : list Z) : M unit :=
if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

Definition stdio_exit_model (code : Z) : M Empty_set :=
stdout_exit_flush ;;;
msys (NExit code) dec_exit.

End Stdio.

Abbreviation str := X1rk.str (only parsing).
Abbreviation str_str_bytes := X1rk.str_str_bytes (only parsing).
Abbreviation dec_text_aux := X1rk.dec_text_aux (only parsing).
Abbreviation dec_text := X1rk.dec_text (only parsing).
Abbreviation pieces_emit := X1rk.pieces_emit (only parsing).
Abbreviation pieces_usage := X1rk.pieces_usage (only parsing).
Abbreviation pieces_cannot_open := X1rk.pieces_cannot_open (only parsing).
Abbreviation pieces_read_error := X1rk.pieces_read_error (only parsing).
Abbreviation pieces_oom := X1rk.pieces_oom (only parsing).
Abbreviation pieces_too_big := X1rk.pieces_too_big (only parsing).
Abbreviation pieces_short_hdr := X1rk.pieces_short_hdr (only parsing).
Abbreviation pieces_cfg_overrun := X1rk.pieces_cfg_overrun (only parsing).
Abbreviation pieces_notify := X1rk.pieces_notify (only parsing).
Abbreviation pieces_warning := X1rk.pieces_warning (only parsing).
Abbreviation pieces_warning_int := X1rk.pieces_warning_int (only parsing).

Inductive diag_msg : Type :=
| DUsage (argv0 : list Z)
| DCannotOpen (path : list Z)
| DReadError (path : list Z)
| DOom
| DTooBig
| DShortHdr
| DCfgOverrun.

Section IO_S.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition s_diag (d : diag_msg) : M St unit :=
match d with
| DUsage argv0 => stderr_fprintf (pieces_usage argv0)
| DCannotOpen p => stderr_fprintf (pieces_cannot_open p)
| DReadError p => stderr_fprintf (pieces_read_error p)
| DOom => stderr_fwrite (concat pieces_oom)
| DTooBig => stderr_fprintf pieces_too_big
| DShortHdr => stderr_fwrite (concat pieces_short_hdr)
| DCfgOverrun => stderr_fwrite (concat pieces_cfg_overrun)
end.

Definition s_emit (rc : Z) : M St unit := stdout_vprintf get_so set_so (pieces_emit rc).

Definition s_notify (s : list Z) : M St unit := stderr_fprintf (pieces_notify s).
Definition s_warning (s : list Z) : M St unit := stderr_fprintf (pieces_warning s).
Definition s_warning_int (s : list Z) (i : Z) : M St unit := stderr_fprintf (pieces_warning_int s i).
End IO_S.

Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite firstn_map. reflexivity. Qed.

Lemma concat_map_to_bytes : forall iovs, concat (map to_bytes iovs) = to_bytes (concat iovs).
Proof. induction iovs as [|v iovs IH]; [reflexivity|]. cbn. rewrite to_bytes_app, IH. reflexivity. Qed.

Lemma wv_total_nonneg : forall iovs, 0 <= wv_total iovs.
Proof. intros. unfold wv_total, zlength. lia. Qed.

Lemma wv_iovs_concat : forall buf s, concat (wv_iovs buf s) = buf ++ s.
Proof. intros. unfold wv_iovs. destruct buf; cbn; rewrite ?app_nil_r; reflexivity. Qed.
Lemma wv_iovs_total : forall buf s, wv_total (wv_iovs buf s) = zlength buf + zlength s.
Proof. intros. unfold wv_total. rewrite wv_iovs_concat. unfold zlength. rewrite length_app. lia. Qed.
Lemma wv_iovs_length : forall buf s, (length (wv_iovs buf s) <= 2)%nat.
Proof. intros. unfold wv_iovs. destruct buf; cbn; lia. Qed.

Lemma wv_advance_concat : forall cnt iovs, (length iovs <= 2)%nat -> 0 <= cnt < wv_total iovs ->
concat (wv_advance cnt iovs) = skipn (Z.to_nat cnt) (concat iovs).
Proof.
intros cnt iovs L H. unfold wv_total, zlength in H.
destruct iovs as [|v [|v2 [|v3 rest]]]; cbn [length] in L; [| | |lia]; cbn [wv_advance concat] in *; unfold zlength;
rewrite ?app_nil_r in *.
- cbn in H. lia.
- destruct (Z.ltb_spec (Z.of_nat (length v)) cnt); [lia|]. cbn [concat]. rewrite app_nil_r. reflexivity.
- rewrite length_app in H. destruct (Z.ltb_spec (Z.of_nat (length v)) cnt).
+ cbn [concat]. rewrite app_nil_r, skipn_app, (skipn_all2 v) by lia. cbn [app]. f_equal. lia.
+ cbn [concat]. rewrite app_nil_r, skipn_app. replace (Z.to_nat cnt - length v)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma wv_advance_length : forall cnt iovs, (length (wv_advance cnt iovs) <= length iovs)%nat.
Proof.
intros cnt [|v [|v2 rest]]; cbn [wv_advance length]; [lia| |]; destruct (zlength v <? cnt); cbn; lia.
Qed.

Lemma wv_advance_total : forall cnt iovs, (length iovs <= 2)%nat -> 0 <= cnt < wv_total iovs ->
wv_total (wv_advance cnt iovs) = wv_total iovs - cnt.
Proof.
intros cnt iovs L H. pose proof H as H'. unfold wv_total, zlength in H |- *.
rewrite (wv_advance_concat cnt iovs L H'), length_skipn. lia.
Qed.

Section LoopFacts.
Context {St : Type}.

#[using="Type"] Lemma map_to_bytes_total : forall iovs, Z.of_nat (length (concat (map to_bytes iovs))) = wv_total iovs.
Proof. intros. rewrite concat_map_to_bytes, to_bytes_length. reflexivity. Qed.

#[using="Type"] Lemma stdio_wloop_tpath : forall fuel fd iovs (st : St) mo tr x mo',
(length iovs <= 2)%nat -> wv_total iovs < 2^64 -> (Z.to_nat (wv_total iovs) < fuel)%nat ->
tpath nstep (stdio_wloop fuel fd iovs st) mo tr x mo' ->
x = Ok (tt, st) /\ mo' = mo /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iovs)).
Proof.
induction fuel as [|fuel IH]; intros fd iovs st mo tr x mo' L B F P; [lia|].
cbn [stdio_wloop] in P. unfold mbind in P. apply tpath_ebind in P.
pose proof (map_to_bytes_total iovs) as LEN. pose proof (wv_total_nonneg iovs) as T0.
destruct P as [[P ->] | (tr1 & [cnt st1] & mo1 & tr2 & P1 & P2 & ->)].
- exfalso. unfold msys in P. apply tpath_enode in P. destruct P as (rsp & ST & E).
destruct (nstep_dec_writev fd (map to_bytes iovs) mo rsp mo' tr ltac:(lia) ST) as (k & D & _).
rewrite LEN in D. rewrite D in E. discriminate.
- unfold msys in P1. apply tpath_enode in P1. destruct P1 as (rsp & ST & E).
destruct (nstep_dec_writev fd (map to_bytes iovs) mo rsp mo1 tr1 ltac:(lia) ST) as (k & D & Hk & Hk1 & -> & ->).
rewrite LEN in D. rewrite D in E. injection E as -> ->. cbn [fst snd] in P2. rewrite LEN in Hk. rewrite concat_map_to_bytes.
destruct (Z.eqb_spec k (wv_total iovs)) as [->|NE].
+ cbn in P2. destruct P2 as (<- & -> & ->). rewrite app_nil_r.
rewrite firstn_all2 by (rewrite to_bytes_length; unfold wv_total, zlength; lia). auto.
+ assert (Hk' : 0 <= k < wv_total iovs) by lia.
pose proof (wv_advance_total k iovs L Hk') as T.
destruct (IH fd (wv_advance k iovs) st mo tr2 x mo' ltac:(pose proof (wv_advance_length k iovs); lia)
ltac:(lia) ltac:(lia) P2) as (-> & -> & ->).
split; [reflexivity|]. split; [reflexivity|].
rewrite (wv_advance_concat k iovs L Hk'), to_bytes_skipn, <- map_app, firstn_skipn. reflexivity.
Qed.

#[using="Type"] Lemma stdio_wloop_haspath : forall fuel fd iovs (st : St) mo,
wv_total iovs < 2^64 -> (0 < fuel)%nat ->
tpath nstep (stdio_wloop fuel fd iovs st) mo (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iovs))) (Ok (tt, st)) mo.
Proof.
intros [|fuel] fd iovs st mo B F; [lia|]. cbn [stdio_wloop]. unfold mbind. apply tpath_ebind. right.
pose proof (map_to_bytes_total iovs) as LEN. pose proof (wv_total_nonneg iovs) as T0.
exists (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iovs))), (wv_total iovs, st), mo, [].
split.
- unfold msys. apply tpath_enode. exists (eff0 (Z_to_bv 64 (wv_total iovs))). split.
+ cbn [nstep]. split; [reflexivity|]. rewrite <- concat_map_to_bytes.
destruct (Nat.eqb_spec (length (concat (map to_bytes iovs))) 0) as [E0|NE].
* replace (wv_total iovs) with 0 by lia. split; [reflexivity|].
destruct (concat (map to_bytes iovs)); [reflexivity| cbn in E0; lia].
* exists (length (concat (map to_bytes iovs))). split; [lia|]. split; [rewrite ecore_eff0, LEN; reflexivity|].
rewrite firstn_all. reflexivity.
+ unfold dec_writev, eff0. rewrite (dec_count_val (wv_total iovs) (wv_total iovs)) by lia. reflexivity.
- rewrite Z.eqb_refl. cbn. rewrite app_nil_r. auto.
Qed.

#[using="Type"] Lemma stdio_wloop_notexit : forall fuel fd iovs (st : St) mo tr, ~ texit nstep nexit (stdio_wloop fuel fd iovs st) mo tr.
Proof.
induction fuel as [|fuel IH]; intros fd iovs st mo tr X; cbn [stdio_wloop] in X; [exact X|].
unfold mbind in X. apply texit_ebind in X. destruct X as [X | (tr1 & [cnt st1] & mo1 & tr2 & _ & X & _)].
- unfold msys in X. apply texit_enode in X. destruct X as (code & mo' & X & _). exact X.
- cbn [fst snd] in X. destruct (cnt =? wv_total iovs); [exact X | exact (IH _ _ _ _ _ X)].
Qed.

#[using="Type"] Lemma stdio_wloop_mspec : forall fuel (P : assn St) fd iovs,
(length iovs <= 2)%nat -> wv_total iovs < 2^64 -> (Z.to_nat (wv_total iovs) < fuel)%nat ->
mspec P (stdio_wloop fuel fd iovs) (fun _ => P).
Proof.
induction fuel as [|fuel IH]; intros P fd iovs L B F; [lia|].
cbn [stdio_wloop]. pose proof (map_to_bytes_total iovs) as LEN. pose proof (wv_total_nonneg iovs) as T0.
eapply mspec_bind.
{ eapply (mspec_sys (NWritev fd (map to_bytes iovs)) (dec_writev (wv_total iovs)) P
(fun cnt s mo => (0 <= cnt <= wv_total iovs /\ (wv_total iovs = 0 \/ 1 <= cnt)) /\ P s mo)).
intros s mo HP. split; [exact I|]. intros rsp mo' evs ST.
destruct (nstep_dec_writev fd (map to_bytes iovs) mo rsp mo' evs ltac:(lia) ST) as (k & D & Hk & Hk1 & -> & ->).
rewrite LEN in D. exists k. split; [exact D|]. split; [|exact HP]. lia. }
cbv beta. intros cnt. destruct (Z.eqb_spec cnt (wv_total iovs)) as [->|NE].
- apply mspec_ret. intros s mo [_ HP]. exact HP.
- apply mspec_pure_l. intros [Hk Hk1].
assert (Hk' : 0 <= cnt < wv_total iovs) by lia.
pose proof (wv_advance_total cnt iovs L Hk') as T.
apply IH; [pose proof (wv_advance_length cnt iovs); lia | lia | lia].
Qed.
End LoopFacts.

Section WritevFacts.
Context {St : Type}.

#[using="Type"] Theorem stdio_writev_tpath_ok : forall fd buf s (st : St) mo tr p mo',
tpath nstep (stdio_writev fd buf s st) mo tr (Ok p) mo' ->
p = (tt, st) /\ mo' = mo /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s)).
Proof.
intros fd buf s st mo tr p mo' P. unfold stdio_writev in P.
destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)) as [LT|GE]; [cbn in P; destruct P as (E & _); discriminate|].
unfold WRITEV_MAX in GE. pose proof (wv_iovs_total buf s) as T. unfold zlength in GE, T.
assert (F : (Z.to_nat (wv_total (wv_iovs buf s)) < S (length buf + length s))%nat) by (rewrite T; lia).
destruct (stdio_wloop_tpath _ fd (wv_iovs buf s) st mo tr (Ok p) mo' (wv_iovs_length buf s) ltac:(lia) F P) as (E & -> & ->).
injection E as ->. rewrite wv_iovs_concat. auto.
Qed.

#[using="Type"] Theorem stdio_writev_tpath : forall fd buf s (st : St) mo tr x mo',
zlength buf + zlength s <= WRITEV_MAX ->
tpath nstep (stdio_writev fd buf s st) mo tr x mo' ->
x = Ok (tt, st) /\ mo' = mo /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s)).
Proof.
intros fd buf s st mo tr x mo' BND P. unfold stdio_writev in P.
destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)) as [LT|GE]; [lia|].
unfold WRITEV_MAX in GE. pose proof (wv_iovs_total buf s) as T. unfold zlength in GE, T.
assert (F : (Z.to_nat (wv_total (wv_iovs buf s)) < S (length buf + length s))%nat) by (rewrite T; lia).
destruct (stdio_wloop_tpath _ fd (wv_iovs buf s) st mo tr x mo' (wv_iovs_length buf s) ltac:(lia) F P) as (-> & -> & ->).
rewrite wv_iovs_concat. auto.
Qed.

#[using="Type"] Theorem stdio_writev_haspath : forall fd buf s (st : St) mo,
zlength buf + zlength s <= WRITEV_MAX ->
tpath nstep (stdio_writev fd buf s st) mo (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))) (Ok (tt, st)) mo.
Proof.
intros fd buf s st mo BND. unfold stdio_writev.
destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)) as [LT|GE]; [lia|].
unfold WRITEV_MAX in GE. pose proof (wv_iovs_total buf s) as T. unfold zlength in GE, T.
rewrite <- wv_iovs_concat. apply stdio_wloop_haspath; lia.
Qed.

#[using="Type"] Theorem stdio_writev_notexit : forall fd buf s (st : St) mo tr, ~ texit nstep nexit (stdio_writev fd buf s st) mo tr.
Proof.
intros fd buf s st mo tr. unfold stdio_writev. destruct (WRITEV_MAX <? zlength buf + zlength s); [intros X; exact X|].
apply stdio_wloop_notexit.
Qed.

#[using="Type"] Theorem stdio_writev_mspec : forall (P : assn St) fd buf s,
zlength buf + zlength s <= WRITEV_MAX ->
mspec P (stdio_writev (St:=St) fd buf s) (fun _ => P).
Proof.
intros P fd buf s BND. unfold stdio_writev.
destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)) as [LT|GE]; [lia|].
unfold WRITEV_MAX in GE. pose proof (wv_iovs_total buf s) as T. unfold zlength in GE, T.
apply stdio_wloop_mspec; [apply wv_iovs_length | lia | rewrite T; lia].
Qed.

#[using="Type"] Theorem stdio_writev_mspec' : forall (P : assn St) fd buf s,
mspec (fun st mo => P st mo /\ zlength buf + zlength s <= WRITEV_MAX) (stdio_writev (St:=St) fd buf s) (fun _ => P).
Proof.
intros P fd buf s st mo [HP BND]. exact (stdio_writev_mspec P fd buf s BND st mo HP).
Qed.
End WritevFacts.
