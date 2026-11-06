(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AgentLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app : forall (a b : list event) (T : TSet),
  t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
  t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.






(* [comment removed for export] *)
Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
  store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
  exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_sub_lit : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_addi_lit : forall a i, (0 <= a < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_ltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma c_eq_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.





(* [comment removed for export] *)
Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.

(* [comment removed for export] *)
Lemma rdn_addr_eq : forall segs m (a b : word) n r,
  a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.

Ltac rdn_at b :=
  apply (rdn_addr_eq _ _ _ b);
  [ first [ f_equal; lia
          | lazymatch goal with |- ?g => Mh32.StepTac.check_closed_term g end;
            apply bv_eq; vm_compute; reflexivity ]
  | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
  match n with
  | O => true
  | S n' => if f z then zall n' f (z + 1)%Z else false
  end.

Lemma zall_spec : forall n f z,
  zall n f z = true -> forall x, (z <= x < z + Z.of_nat n)%Z -> f x = true.
Proof.
  induction n as [|n IH]; intros f z H x Hx; [lia|].
  cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
  destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
  apply (IH f (z + 1)%Z H). lia.
Qed.

(* [comment removed for export] *)
Lemma zallN_spec : forall (n : N) f,
  zall (N.to_nat n) f 0%Z = true -> forall x, (0 <= x < Z.of_N n)%Z -> f x = true.
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.

(* [comment removed for export] *)
Ltac rdn_at_hyp Hb :=
  lazymatch type of Hb with
  | rdn _ _ ?b _ = _ => rdn_at b; exact Hb
  end.
End AgentLib.
Module ShapeLaws.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.







End ShapeLaws.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PuUnorm.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pu_u_Z2bv : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z [H1 H2]. exact (u_Z2bv z H1 H2). Qed.

Ltac pu_u_norm := repeat rewrite pu_u_Z2bv by lia.
End PuUnorm.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg ShapeLaws AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition s2b (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

Definition exit_code (z : Z) : word := Z_to_bv 64 z.

Definition LF : byte := Z_to_bv 8 10.

(* [comment removed for export] *)
Definition t_die (msg : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (W 2 msg) (t_exit (exit_code 2) fs).

Definition msg_usage (argv0 : list byte) : list byte :=
  s2b "usage: " ++ argv0 ++ s2b " INPUT" ++ [LF].
Definition msg_cannot_open (path : list byte) : list byte :=
  s2b "cli: cannot open " ++ path ++ [LF].
Definition msg_read_error (path : list byte) : list byte :=
  s2b "cli: read error on " ++ path ++ [LF].

Definition msg_refused : list byte :=
  s2b "cli: input >= 67108864 bytes, refused" ++ [LF].
Definition msg_short : list byte :=
  s2b "cli: input shorter than header" ++ [LF].
Definition msg_overrun : list byte :=
  s2b "cli: config_len overruns input" ++ [LF].


(* [comment removed for export] *)
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: LF :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.

(* [comment removed for export] *)

Definition hdr_byte (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).

(* [comment removed for export] *)
Definition hdr_cfg (data : list byte) : Z := (hdr_byte data 0 + 256 * hdr_byte data 1)%Z.
(* [comment removed for export] *)
Definition hdr_cfglen (data : list byte) : Z := (hdr_cfg data mod 32768)%Z.
(* [comment removed for export] *)
Definition hdr_count_mode (data : list byte) : bool := (32768 <=? hdr_cfg data)%Z.
(* [comment removed for export] *)
Definition hdr_paylen (data : list byte) : Z := (Z.of_nat (length data) - 6 - hdr_cfglen data)%Z.
(* [comment removed for export] *)
Definition hdr_calls (data : list byte) : nat :=
  if (hdr_cfglen data =? 0)%Z then 1%nat else S (Z.to_nat (hdr_byte data 2 mod 4)%Z).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_success (calls : nat) (fs : Fs.Fs) : TSet :=
  t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs).

(* [comment removed for export] *)
Definition t_payload (count_mode : bool) (paylen : Z) (calls : nat) (fs : Fs.Fs) : TSet :=
  t_success calls fs.

(* [comment removed for export] *)
Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := Z.of_nat (length data) in
  if (MAX_INPUT <=? len)%Z then t_die msg_refused fs
  else if (len <? 6)%Z then t_die msg_short fs
  else if (len <? 6 + hdr_cfglen data)%Z then t_die msg_overrun fs
  else t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data) fs.

(* [comment removed for export] *)
Definition t_opened (data : list byte) (fs : Fs.Fs) : TSet := t_body data fs.

(* [comment removed for export] *)
Definition t_opened_dir (path : list byte) (fs : Fs.Fs) : TSet :=
  t_die (msg_read_error path) fs.

(* [comment removed for export] *)
Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0            (* [comment removed for export] *)
      else if path_eqb path [] then t_die (msg_cannot_open path) fs0                (* [comment removed for export] *)
      else if path_is_dirref path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)           (* [comment removed for export] *)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0                                 (* [comment removed for export] *)
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)  (* [comment removed for export] *)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

(* [comment removed for export] *)
Definition spec_of (inp : ProcInput) : TSet := spec (in_argv inp) (in_fs inp).

(* [comment removed for export] *)

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

Lemma t_die_has_nil : forall msg fs, t_die msg fs [].
Proof. intros. unfold t_die. apply t_emit_has_nil. Qed.

Lemma t_success_has_nil : forall calls fs, t_success calls fs [].
Proof. intros. unfold t_success. apply t_emit_has_nil. Qed.

Lemma t_payload_has_nil : forall cm pl calls fs, t_payload cm pl calls fs [].
Proof. intros. unfold t_payload. apply t_success_has_nil. Qed.

Lemma t_body_has_nil : forall data fs, t_body data fs [].
Proof.
  intros. unfold t_body. cbv zeta.
  repeat (match goal with |- (if ?b then _ else _) [] => destruct b end); first [apply t_die_has_nil | apply t_payload_has_nil].
Qed.

Lemma t_opened_has_nil : forall data fs, t_opened data fs [].
Proof. intros. unfold t_opened. apply t_body_has_nil. Qed.

Lemma t_opened_dir_has_nil : forall path fs, t_opened_dir path fs [].
Proof. intros. unfold t_opened_dir. apply t_die_has_nil. Qed.

Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|p [|x l]]]; try apply t_die_has_nil.
  repeat (match goal with |- (if ?b then _ else _) [] => destruct b end); try apply t_die_has_nil.
  - left. apply t_die_has_nil.
  - destruct (fs_lookup fs p); [left |]; apply t_die_has_nil.
Qed.

(* [comment removed for export] *)
Lemma zero_lines_S : forall k, zero_lines (S k) = zero_lines 1 ++ zero_lines k.
Proof. reflexivity. Qed.



Lemma W_app : forall ch a b, W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

Lemma t_success_S : forall k fs,
  t_eq (t_success (S k) fs) (t_emit (W 1 (zero_lines 1)) (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs))).
Proof.
  intros k fs. unfold t_success. rewrite zero_lines_S, W_app. apply t_emit_app.
Qed.





(* [comment removed for export] *)
Lemma t_opened_eq : forall data fs, t_opened data fs = t_body data fs.
Proof. reflexivity. Qed.

Lemma t_opened_dir_eq : forall path fs, t_opened_dir path fs = t_die (msg_read_error path) fs.
Proof. reflexivity. Qed.


Lemma t_payload_none : forall cm pl calls fs, (pl <= 0)%Z -> t_payload cm pl calls fs = t_success calls fs.
Proof. reflexivity. Qed.

Lemma t_payload_some : forall cm pl calls fs, (1 <= pl)%Z -> t_payload cm pl calls fs = t_success calls fs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hdr_byte_range : forall data i, (0 <= hdr_byte data i < 256)%Z.
Proof.
  intros data i. unfold hdr_byte.
  pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256%Z in H. lia.
Qed.


Lemma hdr_cfglen_range : forall data, (0 <= hdr_cfglen data < 32768)%Z.
Proof. intros data. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.



Lemma hdr_calls_range : forall data, (1 <= hdr_calls data <= 4)%nat.
Proof.
  intros data. unfold hdr_calls. destruct (hdr_cfglen data =? 0)%Z; [lia|].
  pose proof (Z.mod_pos_bound (hdr_byte data 2) 4 ltac:(lia)). lia.
Qed.
