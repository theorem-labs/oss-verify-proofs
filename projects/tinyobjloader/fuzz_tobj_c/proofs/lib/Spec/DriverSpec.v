(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Strings.Ascii Strings.String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition b8 (z : Z) : byte := Z_to_bv 8 z.

Definition byte_of_ascii (a : ascii) : byte := b8 (Z.of_N (N_of_ascii a)).

(* [comment removed for export] *)
Fixpoint str (s : string) : list byte :=
  match s with
  | EmptyString => []
  | String a s' => byte_of_ascii a :: str s'
  end.

(* [comment removed for export] *)
Definition nl : list byte := [b8 10].
Definition line (s : string) : list byte := str s ++ nl.

(* [comment removed for export] *)
Definition ch_stdout : word := Z_to_bv 64 1.
Definition ch_stderr : word := Z_to_bv 64 2.

(* [comment removed for export] *)
Definition wr (ch : Z) (s : list byte) : list event :=
  map (WriteEv (Z_to_bv 64 ch)) s.

(* [comment removed for export] *)
Definition ex (fs : Fs) (c : Z) : event := ExitEv (Z_to_bv 64 c) fs.

(* [comment removed for export] *)
Definition die (fs : Fs) (msg : list byte) : list event := wr 2 msg ++ [ex fs 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MAX_INPUT : Z := 67108864.      (* [comment removed for export] *)
Definition HDR_MIN : Z := 6.               (* [comment removed for export] *)
Definition CFG_COUNT_BIT : Z := 32768.     (* [comment removed for export] *)
Definition READ_CHUNK : Z := 65536.        (* [comment removed for export] *)
Definition PATH_MAX : nat := path_max.     (* [comment removed for export] *)

Lemma PATH_MAX_eq : PATH_MAX = 4096%nat.
Proof. reflexivity. Qed.

Definition msg_usage (argv0 : list byte) : list byte :=
  str "usage: " ++ argv0 ++ line " INPUT".
Definition msg_cannot_open (p : list byte) : list byte :=
  str "cli: cannot open " ++ p ++ nl.
Definition msg_oom : list byte := line "cli: out of memory".
Definition msg_read_error (p : list byte) : list byte :=
  str "cli: read error on " ++ p ++ nl.
Definition msg_refused : list byte := line "cli: input >= 67108864 bytes, refused".
Definition msg_short : list byte := line "cli: input shorter than header".
Definition msg_overrun : list byte := line "cli: config_len overruns input".
Definition msg_zero : list byte := line "0".

(* [comment removed for export] *)
Lemma msg_lengths :
  length (str "usage: ") = 7%nat /\ length (line " INPUT") = 7%nat /\
  length (str "cli: cannot open ") = 17%nat /\ length msg_oom = 19%nat /\
  length (str "cli: read error on ") = 19%nat /\ length msg_refused = 38%nat /\
  length msg_short = 31%nat /\ length msg_overrun = 31%nat /\ length msg_zero = 2%nat.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_dot (p : list byte) : bool := path_eqb p dot_path.

Definition open_may_succeed_b (p : list byte) (fs : Fs) : bool :=
  (length p <? PATH_MAX)%nat
  && negb (path_eqb p [])
  && (is_dot p || match fs_lookup fs p with Some _ => true | None => false end).

Definition open_may_succeed (p : list byte) (fs : Fs) : Prop :=
  (length p < PATH_MAX)%nat /\ p <> [] /\ (p = dot_path \/ fs_lookup fs p <> None).

Lemma open_may_succeed_b_iff : forall p fs,
  open_may_succeed_b p fs = true <-> open_may_succeed p fs.
Proof.
  intros p fs. unfold open_may_succeed_b, open_may_succeed, is_dot.
  rewrite !Bool.andb_true_iff, Bool.orb_true_iff, Bool.negb_true_iff, Nat.ltb_lt,
    path_eqb_eq.
  assert (Hnil : path_eqb p [] = false <-> p <> []).
  { split.
    - intros H E. subst. cbn in H. discriminate.
    - intros H. destruct (path_eqb p []) eqn:E; [|reflexivity].
      apply path_eqb_eq in E. contradiction. }
  rewrite Hnil.
  assert (Hlk : match fs_lookup fs p with Some _ => true | None => false end = true
                <-> fs_lookup fs p <> None).
  { destruct (fs_lookup fs p); split; congruence. }
  rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fbyte (F : list byte) (i : nat) : Z := bv_unsigned (nth i F (b8 0)).
Definition cfg_word (F : list byte) : Z := fbyte F 0 + 256 * fbyte F 1.
Definition counting (F : list byte) : bool := CFG_COUNT_BIT <=? cfg_word F.
Definition config_len (F : list byte) : Z := cfg_word F mod CFG_COUNT_BIT.
Definition calls (F : list byte) : Z :=
  1 + (if 0 <? config_len F then fbyte F 2 mod 4 else 0).
Definition payload_len (F : list byte) : Z :=
  Z.of_nat (length F) - HDR_MIN - config_len F.

Lemma config_len_range : forall F, 0 <= config_len F < CFG_COUNT_BIT.
Proof. intros F. unfold config_len, CFG_COUNT_BIT. apply Z.mod_pos_bound. lia. Qed.

Lemma fbyte_range : forall F i, 0 <= fbyte F i < 256.
Proof.
  intros F i. unfold fbyte.
  pose proof (bv_unsigned_in_range 8 (nth i F (b8 0))) as H.
  change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma calls_range : forall F, 1 <= calls F <= 4.
Proof.
  intros F. unfold calls. pose proof (fbyte_range F 2).
  destruct (0 <? config_len F); [|lia].
  pose proof (Z.mod_pos_bound (fbyte F 2) 4). lia.
Qed.

(* [comment removed for export] *)
Lemma config_len_bytes : forall F,
  config_len F = fbyte F 0 + 256 * (fbyte F 1 mod 128).
Proof.
  intros F. unfold config_len, cfg_word, CFG_COUNT_BIT.
  pose proof (fbyte_range F 0). pose proof (fbyte_range F 1).
  rewrite <- (Z.mod_small (fbyte F 0) 32768) at 2 by lia.
  rewrite Z.add_mod by lia.
  replace 32768 with (256 * 128) at 2 by reflexivity.
  rewrite Z.mul_mod_distr_l by lia.
  rewrite (Z.mod_small (fbyte F 0) 32768) by lia.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (fbyte F 1) 128). lia.
Qed.

Lemma counting_bytes : forall F, counting F = (128 <=? fbyte F 1).
Proof.
  intros F. unfold counting, cfg_word, CFG_COUNT_BIT.
  pose proof (fbyte_range F 0). pose proof (fbyte_range F 1).
  destruct (Z.leb_spec 128 (fbyte F 1)); destruct (Z.leb_spec 32768 (fbyte F 0 + 256 * fbyte F 1)); try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Definition zeros (n : Z) : list byte := concat (repeat msg_zero (Z.to_nat n)).

Lemma zeros_length : forall n, 0 <= n -> Z.of_nat (length (zeros n)) = 2 * n.
Proof.
  intros n Hn. unfold zeros.
  assert (E : forall k, length (concat (repeat msg_zero k)) = (2 * k)%nat).
  { induction k as [|k IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn. lia. }
  rewrite E. lia.
Qed.

Definition file_traces (fs : Fs) (F : list byte) : list (list event) :=
  let len := Z.of_nat (length F) in
  if MAX_INPUT <=? len then [die fs msg_refused]
  else if len <? HDR_MIN then [die fs msg_short]
  else if len <? HDR_MIN + config_len F then [die fs msg_overrun]
  else [wr 1 (zeros (calls F)) ++ [ex fs 0]].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition spec_traces (argv : list (list byte)) (fs : Fs) : list (list event) :=
  let argv0 := hd [] argv in
  if negb (Nat.eqb (length argv) 2) then [die fs (msg_usage argv0)]
  else
    let p := nth 1 argv [] in
    die fs (msg_cannot_open p)
    :: if open_may_succeed_b p fs then      (* [comment removed for export] *)
         if is_dot p then [die fs (msg_read_error p)]
         else match fs_lookup fs p with
              | Some F => file_traces fs F
              | None => []            (* [comment removed for export] *)
              end
       else [].

(* [comment removed for export] *)
Definition Spec (inp : ProcInput) (t : list event) : Prop :=
  In t (spec_traces (in_argv inp) (in_fs inp)).

Lemma Spec_iff : forall inp t,
  Spec inp t <-> In t (spec_traces (in_argv inp) (in_fs inp)).
Proof. intros; unfold Spec; tauto. Qed.

(* [comment removed for export] *)
Lemma file_traces_length_le : forall fs F, (length (file_traces fs F) <= 2)%nat.
Proof.
  intros fs F. unfold file_traces.
  destruct (MAX_INPUT <=? _); [cbn; lia|].
  destruct (_ <? HDR_MIN); [cbn; lia|].
  destruct (_ <? HDR_MIN + _); cbn; lia.
Qed.

Lemma spec_traces_length_le : forall argv fs, (length (spec_traces argv fs) <= 4)%nat.
Proof.
  intros argv fs. unfold spec_traces.
  destruct (negb _); [cbn; lia|].
  cbn [length]. destruct (open_may_succeed_b _ _); [|cbn; lia].
  destruct (is_dot _); [cbn; lia|].
  destruct (fs_lookup _ _) as [F|]; [|cbn; lia].
  pose proof (file_traces_length_le fs F). cbn [length] in *. lia.
Qed.

(* [comment removed for export] *)
Definition ends_in_exit (fs : Fs) (t : list event) : Prop :=
  exists evs c, t = evs ++ [ex fs c] /\ Forall (fun e => exists ch b, e = WriteEv ch b) evs.

Lemma wr_all_writes : forall ch s, Forall (fun e => exists ch' b, e = WriteEv ch' b) (wr ch s).
Proof.
  intros ch s. unfold wr. apply Forall_forall. intros e Hin.
  apply in_map_iff in Hin. destruct Hin as (b & <- & _). eauto.
Qed.

Lemma die_ends_in_exit : forall fs msg, ends_in_exit fs (die fs msg).
Proof. intros fs msg. exists (wr 2 msg), 2. split; [reflexivity|apply wr_all_writes]. Qed.

Lemma file_traces_end_in_exit : forall fs F t, In t (file_traces fs F) -> ends_in_exit fs t.
Proof.
  intros fs F t H. unfold file_traces in H.
  destruct (MAX_INPUT <=? _). { destruct H as [<-|[]]. apply die_ends_in_exit. }
  destruct (_ <? HDR_MIN). { destruct H as [<-|[]]. apply die_ends_in_exit. }
  destruct (_ <? HDR_MIN + _). { destruct H as [<-|[]]. apply die_ends_in_exit. }
  destruct H as [<-|[]]. exists (wr 1 (zeros (calls F))), 0.
  split; [reflexivity|apply wr_all_writes].
Qed.

Lemma Spec_ends_in_exit : forall inp t, Spec inp t -> ends_in_exit (in_fs inp) t.
Proof.
  intros inp t H. unfold Spec, spec_traces in H.
  set (fs := in_fs inp) in *. set (argv := in_argv inp) in *.
  destruct (negb _). { destruct H as [<-|[]]. apply die_ends_in_exit. }
  destruct H as [<-|H]; [apply die_ends_in_exit|].
  destruct (open_may_succeed_b _ _); [|destruct H].
  destruct (is_dot _). { destruct H as [<-|[]]. apply die_ends_in_exit. }
  destruct (fs_lookup _ _) as [F|]; [|destruct H].
  eapply file_traces_end_in_exit; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Intro.
Variable argv : list (list byte).
Variable fs : Fs.

Let p := nth 1 argv [].

Lemma spec_usage : length argv <> 2%nat ->
  In (die fs (msg_usage (hd [] argv))) (spec_traces argv fs).
Proof using .
  intros H. unfold spec_traces.
  destruct (Nat.eqb_spec (length argv) 2); [exfalso; lia|]. cbn. auto.
Qed.

Lemma spec_cannot_open : length argv = 2%nat ->
  In (die fs (msg_cannot_open p)) (spec_traces argv fs).
Proof using .
  intros H. unfold spec_traces. rewrite H. cbn -[die]. auto.
Qed.

(* [comment removed for export] *)

Lemma spec_read_error : length argv = 2%nat -> p = dot_path ->
  In (die fs (msg_read_error p)) (spec_traces argv fs).
Proof using .
  intros H Hd.
  assert (Hl : (length p < PATH_MAX)%nat) by (rewrite Hd, PATH_MAX_eq; cbn; lia).
  unfold spec_traces. rewrite H. cbn -[die open_may_succeed_b is_dot].
  right. fold p.
  assert (Ho : open_may_succeed p fs).
  { split; [exact Hl|]. split; [|left; exact Hd]. rewrite Hd. discriminate. }
  rewrite (proj2 (open_may_succeed_b_iff p fs) Ho).
  unfold is_dot. rewrite Hd, path_eqb_refl. cbn -[die]. auto.
Qed.

Lemma spec_file : forall F t, length argv = 2%nat -> (length p < PATH_MAX)%nat ->
  p <> [] -> p <> dot_path -> fs_lookup fs p = Some F ->
  In t (file_traces fs F) -> In t (spec_traces argv fs).
Proof using .
  intros F t H Hl Hn Hd HF Ht. unfold spec_traces. rewrite H.
  cbn -[die open_may_succeed_b is_dot file_traces]. right. fold p.
  assert (Ho : open_may_succeed p fs).
  { split; [exact Hl|]. split; [exact Hn|]. right. congruence. }
  rewrite (proj2 (open_may_succeed_b_iff p fs) Ho).
  unfold is_dot. destruct (path_eqb p dot_path) eqn:E.
  { apply path_eqb_eq in E. contradiction. }
  rewrite HF. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma file_traces_refused : forall F, MAX_INPUT <= Z.of_nat (length F) ->
  In (die fs msg_refused) (file_traces fs F).
Proof using .
  intros F H. unfold file_traces.
  destruct (Z.leb_spec MAX_INPUT (Z.of_nat (length F))); [|exfalso; lia].
  left; reflexivity.
Qed.

Lemma file_traces_short : forall F, Z.of_nat (length F) < HDR_MIN ->
  In (die fs msg_short) (file_traces fs F).
Proof using .
  intros F H. pose proof (config_len_range F).
  unfold file_traces, MAX_INPUT, HDR_MIN, CFG_COUNT_BIT in *.
  destruct (Z.leb_spec 67108864 (Z.of_nat (length F))); [exfalso; lia|].
  destruct (Z.ltb_spec (Z.of_nat (length F)) 6); [|exfalso; lia]. left; reflexivity.
Qed.

Lemma file_traces_overrun : forall F,
  HDR_MIN <= Z.of_nat (length F) < HDR_MIN + config_len F ->
  Z.of_nat (length F) < MAX_INPUT ->
  In (die fs msg_overrun) (file_traces fs F).
Proof using .
  intros F H Hm. pose proof (config_len_range F).
  unfold file_traces, MAX_INPUT, HDR_MIN, CFG_COUNT_BIT in *.
  destruct (Z.leb_spec 67108864 (Z.of_nat (length F))); [exfalso; lia|].
  destruct (Z.ltb_spec (Z.of_nat (length F)) 6); [exfalso; lia|].
  destruct (Z.ltb_spec (Z.of_nat (length F)) (6 + config_len F)); [|exfalso; lia].
  left; reflexivity.
Qed.

Lemma file_traces_normal : forall F,
  HDR_MIN + config_len F <= Z.of_nat (length F) < MAX_INPUT ->
  In (wr 1 (zeros (calls F)) ++ [ex fs 0]) (file_traces fs F).
Proof using .
  intros F H. pose proof (config_len_range F).
  unfold file_traces, MAX_INPUT, HDR_MIN, CFG_COUNT_BIT in *.
  destruct (Z.leb_spec 67108864 (Z.of_nat (length F))); [exfalso; lia|].
  destruct (Z.ltb_spec (Z.of_nat (length F)) 6); [exfalso; lia|].
  destruct (Z.ltb_spec (Z.of_nat (length F)) (6 + config_len F)); [exfalso; lia|].
  left. reflexivity.
Qed.

End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma file_traces_inv : forall fs F t, In t (file_traces fs F) ->
  let len := Z.of_nat (length F) in
  (MAX_INPUT <= len /\ t = die fs msg_refused)
  \/ (len < HDR_MIN /\ t = die fs msg_short)
  \/ (HDR_MIN <= len < HDR_MIN + config_len F /\ len < MAX_INPUT /\ t = die fs msg_overrun)
  \/ (HDR_MIN + config_len F <= len < MAX_INPUT /\ t = wr 1 (zeros (calls F)) ++ [ex fs 0]).
Proof.
  intros fs F t H. unfold file_traces in H. cbn zeta.
  destruct (Z.leb_spec MAX_INPUT (Z.of_nat (length F))).
  { destruct H as [<-|[]]. left. auto. }
  destruct (Z.ltb_spec (Z.of_nat (length F)) HDR_MIN).
  { destruct H as [<-|[]]. right; left. auto. }
  destruct (Z.ltb_spec (Z.of_nat (length F)) (HDR_MIN + config_len F)).
  { destruct H as [<-|[]]. right; right; left. repeat split; auto; lia. }
  destruct H as [<-|[]]. right; right; right. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma spec_traces_inv : forall argv fs t, In t (spec_traces argv fs) ->
  let p := nth 1 argv [] in
  (length argv <> 2%nat /\ t = die fs (msg_usage (hd [] argv)))
  \/ (length argv = 2%nat /\
      ( t = die fs (msg_cannot_open p)
        \/ (open_may_succeed p fs /\ p = dot_path /\ t = die fs (msg_read_error p))
        \/ (open_may_succeed p fs /\ p <> dot_path /\
            exists F, fs_lookup fs p = Some F /\ In t (file_traces fs F)))).
Proof.
  intros argv fs t H. unfold spec_traces in H. cbn zeta.
  destruct (Nat.eqb_spec (length argv) 2) as [E|E]; cbn [negb] in H.
  2:{ destruct H as [<-|[]]. left. auto. }
  right. split; [exact E|].
  destruct H as [<-|H]; [left; reflexivity|right].
  destruct (open_may_succeed_b (nth 1 argv []) fs) eqn:Ho; [|destruct H].
  apply open_may_succeed_b_iff in Ho.
  unfold is_dot in H. destruct (path_eqb (nth 1 argv []) dot_path) eqn:Hd.
  - apply path_eqb_eq in Hd. destruct H as [<-|[]]. left. auto.
  - right. assert (Hnd : nth 1 argv [] <> dot_path).
    { intros Heq. rewrite Heq, path_eqb_refl in Hd. discriminate. }
    destruct (fs_lookup fs (nth 1 argv [])) as [F|] eqn:HF; [|destruct H].
    split; [exact Ho|]. split; [exact Hnd|]. exists F. auto.
Qed.

(* [comment removed for export] *)
Lemma Spec_cases_iff : forall inp t,
  let argv := in_argv inp in let fs := in_fs inp in
  let p := nth 1 argv [] in
  Spec inp t <->
  ( (length argv <> 2%nat /\ t = die fs (msg_usage (hd [] argv)))
    \/ (length argv = 2%nat /\
        ( t = die fs (msg_cannot_open p)
          \/ (open_may_succeed p fs /\ p = dot_path /\ t = die fs (msg_read_error p))
          \/ (open_may_succeed p fs /\ p <> dot_path /\
              exists F, fs_lookup fs p = Some F /\ In t (file_traces fs F))))).
Proof.
  intros inp t. cbn zeta. unfold Spec. split; [apply spec_traces_inv|].
  intros [[Hn ->]|[Hl [->|[(Ho & Hd & ->)|(Ho & Hd & F & HF & Ht)]]]].
  - apply spec_usage, Hn.
  - apply spec_cannot_open, Hl.
  - apply spec_read_error; assumption.
  - destruct Ho as (Hlen & Hnil & _). eapply spec_file; eauto.
Qed.

(* [comment removed for export] *)
Lemma spec_traces_argv2 : forall a0 a1 fs,
  spec_traces [a0; a1] fs =
    die fs (msg_cannot_open a1)
    :: if open_may_succeed_b a1 fs then
         if is_dot a1 then [die fs (msg_read_error a1)]
         else match fs_lookup fs a1 with
              | Some F => file_traces fs F
              | None => []
              end
       else [].
Proof. reflexivity. Qed.

Lemma spec_traces_usage : forall argv fs, length argv <> 2%nat ->
  spec_traces argv fs = [die fs (msg_usage (hd [] argv))].
Proof.
  intros argv fs H. unfold spec_traces.
  destruct (Nat.eqb_spec (length argv) 2); [exfalso; lia|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Inductive drv_act :=
  | AMalloc (sz : Z)            (* [comment removed for export] *)
  | ARead (count got : Z)       (* [comment removed for export] *)
  | AGrowFree                   (* [comment removed for export] *)
  | ARefuse                     (* [comment removed for export] *)
  | AClose.                     (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint read_loop (L len cap : Z) (fuel : nat) : list drv_act :=
  match fuel with
  | O => []
  | S fuel' =>
      if len =? cap then
        if MAX_INPUT <=? cap then [ARefuse]
        else AMalloc (2 * cap) :: AGrowFree :: read_loop_rd L len (2 * cap) fuel'
      else read_loop_rd L len cap fuel'
  end
with read_loop_rd (L len cap : Z) (fuel : nat) : list drv_act :=
  match fuel with
  | O => []
  | S fuel' =>
      let count := Z.min (cap - len) READ_CHUNK in
      let got := Z.min count (L - len) in
      ARead count got ::
      if got =? 0 then [AClose] else read_loop L (len + got) cap fuel'
  end.

Definition read_all_plan (L : Z) : list drv_act :=
  AMalloc READ_CHUNK :: read_loop L 0 READ_CHUNK 2100%nat.

(* [comment removed for export] *)
Example plan_0 : read_all_plan 0 = [AMalloc 65536; ARead 65536 0; AClose].
Proof. vm_compute. reflexivity. Qed.
Example plan_5 : read_all_plan 5 = [AMalloc 65536; ARead 65536 5; ARead 65531 0; AClose].
Proof. vm_compute. reflexivity. Qed.
Example plan_65535 : read_all_plan 65535 =
  [AMalloc 65536; ARead 65536 65535; ARead 1 0; AClose].
Proof. vm_compute. reflexivity. Qed.
Example plan_65536 : read_all_plan 65536 =
  [AMalloc 65536; ARead 65536 65536; AMalloc 131072; AGrowFree; ARead 65536 0; AClose].
Proof. vm_compute. reflexivity. Qed.
Example plan_65537 : read_all_plan 65537 =
  [AMalloc 65536; ARead 65536 65536; AMalloc 131072; AGrowFree; ARead 65536 1;
   ARead 65535 0; AClose].
Proof. vm_compute. reflexivity. Qed.
Example plan_131073 : read_all_plan 131073 =
  [AMalloc 65536; ARead 65536 65536; AMalloc 131072; AGrowFree; ARead 65536 65536;
   AMalloc 262144; AGrowFree; ARead 65536 1; ARead 65536 0; AClose].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Example plan_64M_shape :
  let pl := read_all_plan MAX_INPUT in
  length pl = 1046%nat /\ last pl AClose = ARefuse /\
  nth 1044 pl AClose = ARead 65536 65536 /\
  length (List.filter (fun a => match a with AMalloc _ => true | _ => false end) pl) = 11%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Example plan_64Mm1_shape :
  let pl := read_all_plan (MAX_INPUT - 1) in
  length pl = 1047%nat /\ last pl ARefuse = AClose /\
  nth 1044 pl AClose = ARead 65536 65535 /\ nth 1045 pl AClose = ARead 1 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
