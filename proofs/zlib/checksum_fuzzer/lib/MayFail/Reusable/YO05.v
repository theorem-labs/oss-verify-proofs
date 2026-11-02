(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO05.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition strB (s : string) : list byte :=
map (fun a => Z_to_bv 8 (Z.of_N (N_of_ascii a))) (list_ascii_of_string s).
Definition nlB : list byte := [Z_to_bv 8 10].
Definition ch_stdout : word := Z_to_bv 64 1.
Definition ch_stderr : word := Z_to_bv 64 2.
Definition wr (ch : word) (bs : list byte) (T : TSet) : TSet := t_emit (map (WriteEv ch) bs) T.
Definition ex (code : Z) (fs : Fs) : TSet := t_exit (Z_to_bv 64 code) fs.
Definition diag (msg : list byte) (fs : Fs) : TSet := wr ch_stderr msg (ex 2 fs).
Definition msg_usage (argv0 : list byte) : list byte := strB "usage: " ++ argv0 ++ strB " INPUT" ++ nlB.
Definition msg_cannot_open (p : list byte) : list byte := strB "cli: cannot open " ++ p ++ nlB.
Definition msg_oom : list byte := strB "cli: out of memory" ++ nlB.
Definition msg_read_error (p : list byte) : list byte := strB "cli: read error on " ++ p ++ nlB.
Definition msg_refused : list byte := strB "cli: input >= 67108864 bytes, refused" ++ nlB.
Definition msg_short : list byte := strB "cli: input shorter than header" ++ nlB.
Definition msg_overrun : list byte := strB "cli: config_len overruns input" ++ nlB.
Definition line0 : list byte := strB "0" ++ nlB.
Definition MAX_INPUT : Z := 67108864.
Definition HDR_MIN : Z := 6.
Definition CAP0 : Z := 65536.
Section e.
Variable data : list byte.
Definition dlen : Z := Z.of_nat (length data).
Definition dbyte (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_word : Z := dbyte 0 + 256 * dbyte 1.
Definition count_mode : bool := 32768 <=? cfg_word.
Definition config_len : Z := cfg_word mod 32768.
Definition payload_len : Z := dlen - HDR_MIN - config_len.
Definition cfg_byte : Z := if config_len =? 0 then 0 else dbyte 2.
Definition calls : nat := Z.to_nat (1 + cfg_byte mod 4).
End e.
Inductive dleaf :=
| DL_oom
| DL_refused
| DL_short
| DL_overrun
| DL_payload_fail
| DL_run (buf : sptr) (cap : Z) (payload : option sptr).
Definition leaf_shape (data : list byte) (fs : Fs) (r : dleaf * astate) : TSet :=
match fst r with
| DL_oom => diag msg_oom fs
| DL_refused => diag msg_refused fs
| DL_short => diag msg_short fs
| DL_overrun => diag msg_overrun fs
| DL_payload_fail => ex (if count_mode data then 0 else 2) fs
| DL_run _ _ _ => wr ch_stdout (concat (repeat line0 (calls data))) (ex 0 fs)
end.
End d.
Local Open Scope mm_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Inductive rd_result := RdOOM | RdRefused | RdLoaded (buf : sptr) (cap : Z).
Fixpoint read_phase (fuel : nat) (L cap : Z) (buf : sptr) : M rd_result :=
match fuel with
| O => ret RdRefused
| S f =>
if L <? cap then ret (RdLoaded buf cap)
else if MAX_INPUT <=? cap then ret RdRefused
else p <- malloc (2 * cap) ;;
match p with
| None => ret RdOOM
| Some nb => free (Some buf) ;; read_phase f L (2 * cap) nb
end
end.
Definition READ_FUEL : nat := 11%nat.
Definition driver_m (data : list byte) : M dleaf :=
p0 <- malloc CAP0 ;;
match p0 with
| None => ret DL_oom
| Some b0 =>
r <- read_phase READ_FUEL (dlen data) CAP0 b0 ;;
match r with
| RdOOM => ret DL_oom
| RdRefused => ret DL_refused
| RdLoaded buf cap =>
if dlen data <? HDR_MIN then ret DL_short
else if dlen data <? HDR_MIN + config_len data then ret DL_overrun
else if payload_len data =? 0 then ret (DL_run buf cap None)
else p <- malloc (payload_len data) ;;
match p with
| None => ret DL_payload_fail
| Some q => ret (DL_run buf cap (Some q))
end
end
end.
Definition driver_tree (data : list byte) : itree astate (dleaf * astate) :=
driver_m data init_state.
Definition dir_m : M bool :=
p0 <- malloc CAP0 ;; ret (match p0 with None => false | Some _ => true end).
Definition SPEC_loaded (data : list byte) (fs : Fs) : TSet :=
tset (driver_tree data) (leaf_shape data fs).
Definition SPEC_dir (p : list byte) (fs : Fs) : TSet :=
tset (dir_m init_state)
(fun r => if fst r then diag (msg_read_error p) fs else diag msg_oom fs).
Inductive open_kind := OpenFails | OpenDir | OpenFile (data : list byte).
Definition classify_open (p : list byte) (fs : Fs) : open_kind :=
if (path_max <=? length p)%nat then OpenFails
else if path_eqb p [] then OpenFails
else if path_eqb p dot_path then OpenDir
else match fs_lookup fs p with
| None => OpenFails
| Some data => OpenFile data
end.
Definition SPEC_args (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_loaded data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition SPEC (inp : ProcInput) : TSet := SPEC_args (in_argv inp) (in_fs inp).
Definition leaf_rel (x y : dleaf * astate) : Prop :=
shape_eq (snd x) (snd y) /\
match fst x, fst y with
| DL_run _ c _, DL_run _ c' _ => c = c'
| a, b => a = b
end.
Record driver_obligations : Prop := {
do_jinv : forall data fs, jinv (leaf_shape data fs) (driver_tree data);
do_gtree : forall data, gtree mgrant (driver_tree data)
}.
Definition malloc_rel (x y : option sptr * astate) : Prop :=
shape_eq (snd x) (snd y) /\
match fst x, fst y with
| None, None => True
| Some p, Some p' =>
exists g am am' i fr fr',
In (g, am, i, fr) (frames (snd x)) /\ In (g, am', i, fr') (frames (snd y)) /\
p = frame_ptr am i fr /\ p' = frame_ptr am' i fr'
| _, _ => False
end.
Lemma malloc_self_tsim : forall s n, WF s -> 0 <= n -> tsim malloc_rel (malloc n s) (malloc n s).
Proof. intros s n HW Hn. apply (malloc_tsim s s n HW HW eq_refl Hn). Qed.
Lemma shape_eq_refl : forall s, shape_eq s s.
Proof. intros s. reflexivity. Qed.
Lemma dir_safe : safe (dir_m init_state).
Proof.
unfold dir_m, bind. apply safe_ibind.
- apply malloc_safe; [apply wf_init | unfold CAP0; lia].
- intros [p s]. exact I.
Qed.
Lemma dir_jinv : forall (p : list byte) (fs : Fs),
jinv (fun r : bool * astate => if fst r then diag (msg_read_error p) fs else diag msg_oom fs) (dir_m init_state).
Proof.
intros p fs. unfold dir_m.
match goal with |- jinv _ (bind ?m ?f ?s) =>
apply (tsim_jinv (fun x y : bool * astate => fst x = fst y) _ (bind m f s)) end.
- match goal with |- tsim ?R' (bind ?m ?f ?s) _ =>
apply (tsim_mbind malloc_rel R' m m f f s s) end.
+ apply malloc_self_tsim; [apply wf_init | unfold CAP0; lia].
+ intros a s1 b t1 [_ Hab]. cbn in Hab |- *. destruct a, b; try reflexivity; destruct Hab.
- intros [a sa] [b sb] E. cbn in E |- *. rewrite E. apply t_eq_refl.
Qed.
Lemma dir_gtree : gtree mgrant (dir_m init_state).
Proof.
vm_compute. repeat split; try discriminate; try reflexivity; try (intros _; repeat split; reflexivity); try lia.
Qed.
End h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma itok_intro {A} : forall (t : itree astate A) (Q : A -> Prop),
safe t -> reqs_ok t -> (forall tr a, yields t tr a -> Q a) -> itok t Q.
Proof.
induction t as [a | q s k IH | f]; intros Q Hs Hr Hy; cbn in *.
- apply (Hy []). reflexivity.
- split; [exact (proj1 Hr)|]. intros z Hz. apply IH; [apply Hs; exact Hz | apply (proj2 Hr); exact Hz |].
intros tr a H. apply (Hy ((q, z) :: tr)). auto.
- destruct Hs.
Qed.
Definition malloc_postP (s : astate) (n : Z) (r : option sptr * astate) : Prop :=
WF (snd r) /\
match fst r with
| None => user_blocks (snd r) = user_blocks s
| Some q => exists l1 l2, user_blocks (snd r) = l1 ++ (q, n) :: l2 /\ user_blocks s = l1 ++ l2
end.
Lemma malloc_itok : forall s n, WF s -> 0 <= n -> itok (malloc n s) (malloc_postP s n).
Proof.
intros s n HW Hn. apply itok_intro.
- apply malloc_safe; assumption.
- apply malloc_reqs_ok; assumption.
- intros tr [p s'] Hy. split.
+ eapply malloc_wf; eauto.
+ pose proof (malloc_blocks s n tr p s' HW Hn Hy) as H. cbn. destruct p; [| exact H].
destruct H as (l1 & l2 & E1 & E2 & _). exists l1, l2. auto.
Qed.
Definition free_postP (s : astate) (p : sptr) (n : Z) (r : unit * astate) : Prop :=
WF (snd r) /\ exists l1 l2, user_blocks s = l1 ++ (p, n) :: l2 /\ user_blocks (snd r) = l1 ++ l2.
Lemma free_itok : forall s p n, WF s -> In (p, n) (user_blocks s) -> itok (free (Some p) s) (free_postP s p n).
Proof.
intros s p n HW Hin. apply itok_intro.
- eapply free_safe; eassumption.
- eapply free_reqs_ok; eassumption.
- intros tr [[] s'] Hy. split; [eapply free_wf; eauto | eapply free_blocks; eauto].
Qed.
Lemma in_remove_other {X} : forall (l1 l2 : list X) (x y : X),
In y (l1 ++ x :: l2) -> y <> x -> In y (l1 ++ l2).
Proof.
intros l1 l2 x y H Hne. apply in_app_iff in H. apply in_app_iff.
destruct H as [H | [H | H]]; [left; exact H | subst; contradiction | right; exact H].
Qed.
Definition leaf_ok (data : list byte) (r : dleaf * astate) : Prop :=
WF (snd r) /\
match fst r with
| DL_run buf cap pay =>
In (buf, cap) (user_blocks (snd r)) /\
(forall q, pay = Some q -> In (q, payload_len data) (user_blocks (snd r)))
| _ => True
end.
Lemma read_phase_itok : forall fuel L cap buf s,
WF s -> 0 < cap -> In (buf, cap) (user_blocks s) ->
itok (read_phase fuel L cap buf s)
(fun r => WF (snd r) /\ match fst r with
| RdLoaded b c => In (b, c) (user_blocks (snd r)) /\ 0 < c
| _ => True end).
Proof.
induction fuel as [|fuel IH]; intros L cap buf s HW Hcap Hin; cbn [read_phase].
- apply itok_ret. unfold leaf_ok; cbn [fst snd]. auto.
- destruct (L <? cap); [apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto|].
destruct (MAX_INPUT <=? cap); [apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto|].
apply itok_bind. eapply itok_mono; [| apply malloc_itok; [exact HW | lia]].
intros [[nb|] s1] [HW1 Hb]; cbn [fst snd] in *.
+ destruct Hb as (l1 & l2 & E1 & E2).
assert (Hin1 : In (buf, cap) (user_blocks s1)).
{ rewrite E1. apply in_app_iff. rewrite E2 in Hin. apply in_app_iff in Hin. destruct Hin; [left | right; right]; assumption. }
assert (Hnb1 : In (nb, 2 * cap) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
apply itok_bind. eapply itok_mono; [| apply (free_itok s1 buf cap HW1 Hin1)].
intros [[] s2] [HW2 (m1 & m2 & F1 & F2)]; cbn [fst snd] in *.
apply IH; [exact HW2 | lia |].
rewrite F2. eapply in_remove_other; [rewrite <- F1; exact Hnb1 |]. intros E. injection E. lia.
+ apply itok_ret. unfold leaf_ok; cbn [fst snd]. auto.
Qed.
Theorem driver_itok : forall data, itok (driver_tree data) (leaf_ok data).
Proof.
intros data. unfold driver_tree, driver_m.
apply itok_bind. eapply itok_mono; [| apply malloc_itok; [apply wf_init | unfold CAP0; lia]].
intros [[b0|] s1] [HW1 Hb]; cbn [fst snd] in *; [| apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto].
destruct Hb as (l1 & l2 & E1 & _).
apply itok_bind. eapply itok_mono; [| apply read_phase_itok; [exact HW1 | unfold CAP0; lia | rewrite E1; apply in_app_iff; right; left; reflexivity]].
intros [[ | | buf cap] s2] [HW2 Hr]; cbn [fst snd] in *; try (apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto; fail).
destruct Hr as [Hbuf Hcap].
destruct (dlen data <? HDR_MIN); [apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto|].
destruct (dlen data <? HDR_MIN + config_len data) eqn:E6; [apply itok_ret; unfold leaf_ok; cbn [fst snd]; auto|].
destruct (payload_len data =? 0) eqn:Ep.
- apply itok_ret. unfold leaf_ok; cbn [fst snd]. split; [exact HW2 | split; [exact Hbuf | intros q H; discriminate]].
- apply itok_bind. eapply itok_mono; [| apply malloc_itok; [exact HW2 |]].
2:{ unfold payload_len, HDR_MIN in *. apply Z.ltb_ge in E6. lia. }
intros [[q|] s3] [HW3 Hq]; cbn [fst snd] in *.
+ destruct Hq as (m1 & m2 & F1 & F2). apply itok_ret. unfold leaf_ok; cbn [fst snd]. split; [exact HW3|]. split.
* rewrite F1. apply in_app_iff. rewrite F2 in Hbuf. apply in_app_iff in Hbuf. destruct Hbuf; [left | right; right]; assumption.
* intros q' E. injection E as <-. rewrite F1. apply in_app_iff. right. left. reflexivity.
+ apply itok_ret. unfold leaf_ok; cbn [fst snd]. auto.
Qed.
Corollary driver_safe : forall data, safe (driver_tree data).
Proof. intros data. eapply itok_safe. apply driver_itok. Qed.
Corollary driver_leaves : forall data, leaves (leaf_ok data) (driver_tree data).
Proof. intros data. apply itok_leaves. apply driver_itok. Qed.
Definition meta_slack (s : astate) : Z := st_avail_meta_count s + Z.of_nat (length (free_meta_keys s)).
Definition gtree_malloc_stmt : Prop :=
forall s n, WF s -> 0 <= n < 2 ^ 26 ->
65 <= meta_slack s -> st_brk s <> BrkNever ->
live_bytes s + 2 ^ 28 <= MG_LIVE -> nslots s + 8 <= MG_SLOTS ->
gtree mgrant (malloc n s) /\
itok (malloc n s) (fun r => meta_slack (snd r) >= meta_slack s - 65 /\
live_bytes (snd r) <= live_bytes s + page_round (n + 20) + 2 ^ 21 /\
nslots (snd r) <= nslots s + 5 /\ st_brk (snd r) <> BrkNever).
Example gtree_first_malloc : gtree mgrant (malloc CAP0 init_state).
Proof. vm_compute. repeat split; try discriminate; try reflexivity; try (intros _; repeat split; reflexivity); try lia. Qed.
Definition gtree_free_stmt : Prop :=
forall s p n, WF s -> In (p, n) (user_blocks s) ->
gtree mgrant (free (Some p) s) /\
itok (free (Some p) s) (fun r => meta_slack (snd r) >= meta_slack s /\
live_bytes (snd r) <= live_bytes s /\ nslots (snd r) <= nslots s /\
st_brk (snd r) = st_brk s).
Definition jinv_driver_stmt : Prop := forall data fs, jinv (leaf_shape data fs) (driver_tree data).
End j.
