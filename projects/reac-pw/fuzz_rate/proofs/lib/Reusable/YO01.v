(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO01.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YO01.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO05 YO09 YO06 YO0p YO0j YO0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition POSTX (data : list byte) (fs : Fs) : TSet :=
if dlen data <? HDR_MIN then diag msg_short fs
else if dlen data <? HDR_MIN + config_len data then diag msg_overrun fs
else run_shape (payload data) (calls data) fs.
Fixpoint RPX (data : list byte) (fs : Fs) (fuel : nat) (cap : Z) : TSet :=
match fuel with
| O => diag msg_refused fs
| S f => if dlen data <? cap then POSTX data fs
else if MAX_INPUT <=? cap then diag msg_refused fs
else RPX data fs f (2 * cap)
end.
Definition CLOSEDX_loaded (data : list byte) (fs : Fs) : TSet := RPX data fs READ_FUEL CAP0.
Definition CLOSEDX_dir (p : list byte) (fs : Fs) : TSet := diag (msg_read_error p) fs.
Definition CLOSEDX_args (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (CLOSEDX_dir p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (CLOSEDX_loaded data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition CLOSEDX (inp : ProcInput) : TSet := CLOSEDX_args (in_argv inp) (in_fs inp).
Lemma RPX_closed : forall data fs, 0 <= dlen data ->
t_eq (RPX data fs READ_FUEL CAP0) (if dlen data <? MAX_INPUT then POSTX data fs else diag msg_refused fs).
Proof.
intros data fs Hd. unfold READ_FUEL, CAP0, MAX_INPUT. cbn [RPX].
destruct (Z.ltb_spec (dlen data) 65536) as [L0|L0]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 65536) with false by reflexivity.
replace (2 * 65536) with 131072 by reflexivity.
destruct (Z.ltb_spec (dlen data) 131072) as [L1|L1]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 131072) with false by reflexivity.
replace (2 * 131072) with 262144 by reflexivity.
destruct (Z.ltb_spec (dlen data) 262144) as [L2|L2]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 262144) with false by reflexivity.
replace (2 * 262144) with 524288 by reflexivity.
destruct (Z.ltb_spec (dlen data) 524288) as [L3|L3]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 524288) with false by reflexivity.
replace (2 * 524288) with 1048576 by reflexivity.
destruct (Z.ltb_spec (dlen data) 1048576) as [L4|L4]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 1048576) with false by reflexivity.
replace (2 * 1048576) with 2097152 by reflexivity.
destruct (Z.ltb_spec (dlen data) 2097152) as [L5|L5]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 2097152) with false by reflexivity.
replace (2 * 2097152) with 4194304 by reflexivity.
destruct (Z.ltb_spec (dlen data) 4194304) as [L6|L6]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 4194304) with false by reflexivity.
replace (2 * 4194304) with 8388608 by reflexivity.
destruct (Z.ltb_spec (dlen data) 8388608) as [L7|L7]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 8388608) with false by reflexivity.
replace (2 * 8388608) with 16777216 by reflexivity.
destruct (Z.ltb_spec (dlen data) 16777216) as [L8|L8]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 16777216) with false by reflexivity.
replace (2 * 16777216) with 33554432 by reflexivity.
destruct (Z.ltb_spec (dlen data) 33554432) as [L9|L9]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 33554432) with false by reflexivity.
replace (2 * 33554432) with 67108864 by reflexivity.
destruct (Z.ltb_spec (dlen data) 67108864) as [L10|L10]; [replace (dlen data <? 67108864) with true by (symmetry; apply Z.ltb_lt; lia); apply t_eq_refl|].
replace (67108864 <=? 67108864) with true by reflexivity. replace (dlen data <? 67108864) with false by (symmetry; apply Z.ltb_ge; lia). apply t_eq_refl.
Qed.
Lemma wr_has_nil : forall ch bs T, wr ch bs T []. Proof. intros. unfold wr. apply t_emit_has_nil. Qed.
Lemma diag_has_nil : forall m fs, diag m fs []. Proof. intros. unfold diag. apply wr_has_nil. Qed.
Lemma ex_has_nil : forall c fs, ex c fs []. Proof. intros. unfold ex, t_exit. apply t_emit_has_nil. Qed.
Lemma t_alt2_has_nil_l : forall A B, A [] -> t_alt2 A B []. Proof. intros A B H. left. exact H. Qed.
Hypothesis LIBK_has_nil : forall pl fs K, (forall l, K l []) -> LIBK pl fs K [].
Lemma lib_iter_has_nil : forall pl j K fs, (forall fs, K fs []) -> lib_iter pl j K fs [].
Proof. intros pl j. induction j as [|j IH]; intros K fs HK; cbn; [apply HK | apply LIBK_has_nil; intros l; apply IH; exact HK]. Qed.
Lemma run_tail_has_nil : forall m fs, run_tail m fs [].
Proof. intros [|m] fs; cbn; [apply ex_has_nil | apply wr_has_nil]. Qed.
Lemma run_shape_has_nil : forall pl k fs, run_shape pl k fs [].
Proof. intros pl [|k] fs; cbn; [apply ex_has_nil | apply LIBK_has_nil; intros l; apply wr_has_nil]. Qed.
Lemma POSTX_has_nil : forall data fs, POSTX data fs [].
Proof. intros. unfold POSTX. destruct (dlen data <? HDR_MIN); [apply diag_has_nil|]. destruct (dlen data <? HDR_MIN + config_len data); [apply diag_has_nil | apply run_shape_has_nil]. Qed.
Lemma RPX_has_nil : forall data fs f cap, RPX data fs f cap [].
Proof. intros data fs f. induction f as [|f IH]; intros cap; cbn; [apply diag_has_nil|]. destruct (dlen data <? cap); [apply POSTX_has_nil|]. destruct (MAX_INPUT <=? cap); [apply diag_has_nil | apply IH]. Qed.
Lemma CLOSEDX_has_nil : forall inp, CLOSEDX inp [].
Proof.
intros inp. unfold CLOSEDX, CLOSEDX_args.
destruct (in_argv inp) as [|a0 [|p [|x r]]]; try apply diag_has_nil.
destruct (classify_open p (in_fs inp)); [apply diag_has_nil | |]; apply t_alt2_has_nil_l; apply diag_has_nil.
Qed.
Definition specx_closedx_eq_stmt : Prop := forall inp, t_eq (SPECX inp) (CLOSEDX inp).
Lemma tset_const04 {A} : forall (t : itree astate A) (K : A -> TSet) (T : TSet),
safe t -> (forall tr a, cpath04 t tr a -> t_eq (K a) T) -> t_eq (tset t K) T.
Proof.
induction t as [a | q s k IH | f]; intros K T Hs HK; cbn in *.
- apply (HK []). reflexivity.
- assert (STEP : forall z, canswer04 q z -> answer_ok q z -> t_eq (tset (k z) K) T).
{ intros z Hz Hok. apply IH; [apply Hs; exact Hok|]. intros tr a Hp. apply (HK ((q, z) :: tr)). cbn. split; [reflexivity|]. split; [exact Hz | exact Hp]. }
destruct (fallible q) eqn:Hf; [destruct (spurious q) eqn:Hsp|].
+ eapply t_eq_trans; [| apply t_alt2_idem]. apply t_alt2_congr; apply STEP;
try (apply answer_ok_kernel; exact Hf);
destruct q; cbn in Hf, Hsp |- *; try discriminate; unfold canswer04; cbn; auto.
+ apply STEP; [| apply answer_ok_kernel; exact Hf].
destruct q; cbn in Hf, Hsp |- *; try discriminate; unfold canswer04; cbn; auto.
+ apply STEP; [| apply canon_answer_ok].
destruct q; cbn in Hf |- *; try discriminate; unfold canswer04; cbn; try reflexivity.
apply Z.mod_pos_bound. lia.
- destruct Hs.
Qed.
Definition rd_leaf (data : list byte) (r : rd_result * astate) : Prop :=
match fst r with RdOOM => False | RdRefused => MAX_INPUT <= dlen data | RdLoaded _ _ => dlen data < MAX_INPUT end.
Ltac rd_step :=
cbn [read_phase];
lazymatch goal with
| |- S4 _ ((if dlen ?data <? ?c then _ else _) ?s) =>
let cv := eval vm_compute in c in change c with cv; destruct (Z.ltb_spec (dlen data) cv); cbv iota beta
| |- S4 _ (ret RdRefused _) => idtac
end;
first [ apply S4_ret; cbn [fst rd_leaf]; unfold MAX_INPUT; lia
| lazymatch goal with |- S4 _ ((if ?m <=? ?c then _ else _) _) =>
let mv := eval vm_compute in m in change m with mv;
first [ replace (mv <=? c) with false by reflexivity | replace (mv <=? c) with true by reflexivity ]; cbv iota beta end;
first [ apply S4_ret; cbn [fst rd_leaf]; unfold MAX_INPUT; lia
| eapply S4_bind; [ apply malloc_some04; reflexivity |]; intros [?nb|] ?s1 [?pp HSOME]; cbn [fst] in HSOME; [clear HSOME | discriminate HSOME]; eapply S4_bind_TT; intros _ ?s2 ] ].
Lemma read_phase_S4 : forall data buf s, S4 (rd_leaf data) (read_phase READ_FUEL (dlen data) CAP0 buf s).
Proof.
intros data buf s. unfold READ_FUEL, CAP0. do 11 rd_step.
Qed.
Lemma config_len_range data : 0 <= config_len data < 32768.
Proof. unfold config_len. apply Z.mod_pos_bound. lia. Qed.
Lemma driver_tree_S4 : forall data fs,
S4 (fun r => t_eq (leaf_shapeX data fs r) (if dlen data <? MAX_INPUT then POSTX data fs else diag msg_refused fs)) (driver_tree data).
Proof.
intros data fs. unfold driver_tree, driver_m.
eapply S4_bind; [apply malloc_some04; reflexivity|]. intros [b0|] s1 [p0 Hp0]; cbn [fst] in Hp0; [clear Hp0 | discriminate Hp0]. cbv beta iota.
eapply S4_bind; [apply read_phase_S4|]. intros [| |buf cap] s2 Hr; cbn [fst rd_leaf] in Hr; [destruct Hr | |]; cbv beta iota.
- apply S4_ret. cbn [fst leaf_shapeX leaf_shape]. replace (dlen data <? MAX_INPUT) with false by (symmetry; apply Z.ltb_ge; lia). apply t_eq_refl.
- replace (dlen data <? MAX_INPUT) with true by (symmetry; apply Z.ltb_lt; lia). unfold POSTX.
destruct (dlen data <? HDR_MIN) eqn:E1; [apply S4_ret; cbn [fst leaf_shapeX leaf_shape]; apply t_eq_refl|].
destruct (dlen data <? HDR_MIN + config_len data) eqn:E2; [apply S4_ret; cbn [fst leaf_shapeX leaf_shape]; apply t_eq_refl|].
destruct (payload_len data =? 0) eqn:E3; [apply S4_ret; cbn [fst leaf_shapeX]; apply t_eq_refl|].
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. pose proof (config_len_range data) as CR.
eapply S4_bind; [apply malloc_some04; unfold size_overflows, payload_len, MAX_INPUT, HDR_MIN in *; apply Z.leb_gt; lia|].
intros [q|] s3 [pq Hpq]; cbn [fst] in Hpq; [clear Hpq | discriminate Hpq]. cbv beta iota.
apply S4_ret. cbn [fst leaf_shapeX]. apply t_eq_refl.
Qed.
Lemma dir_S4 : S4 (fun r => fst r = true) (dir_m init_state).
Proof.
unfold dir_m. eapply S4_bind; [apply malloc_some04; reflexivity|]. intros [b0|] s1 [p0 Hp0]; cbn [fst] in Hp0; [clear Hp0 | discriminate Hp0].
cbv beta iota. apply S4_ret. reflexivity.
Qed.
Theorem specx_closedx_eq : specx_closedx_eq_stmt.
Proof.
intros inp. unfold SPECX, CLOSEDX, SPECX_args, CLOSEDX_args.
destruct (in_argv inp) as [|a0 [|p [|x r]]]; [apply t_eq_refl | apply t_eq_refl | | apply t_eq_refl].
destruct (classify_open p (in_fs inp)) as [| |data]; [apply t_eq_refl | |]; (apply t_alt2_congr; [apply t_eq_refl|]).
-   unfold SPEC_dir, CLOSEDX_dir. apply tset_const04; [apply dir_safe|].
intros tr [b s'] Hp. pose proof (dir_S4 tr (b, s') Hp) as Hb. cbn [fst] in Hb |- *. subst b. apply t_eq_refl.
-   unfold SPECX_loaded, CLOSEDX_loaded.
eapply t_eq_trans; [| apply t_eq_sym; apply RPX_closed; unfold dlen; lia].
apply tset_const04; [apply driver_safe | intros tr r Hp; exact (driver_tree_S4 data (in_fs inp) tr r Hp)].
Qed.
End d.
