(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1rk X1r8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition evw (fd : Z) (bs : list Z) : list event :=
map (fun b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)) bs.

Record ctrace : Type := mkCT { ct_segs : list (Z * list Z); ct_code : Z }.

Definition seg_events (sg : Z * list Z) : list event := evw (fst sg) (snd sg).

Definition ct_events (fs : Fs) (ct : ctrace) : list event :=
concat (map seg_events (ct_segs ct)) ++ [ExitEv (Z_to_bv 64 (ct_code ct)) fs].

Definition msg_usage (argv0 : list Z) : list Z := concat (pieces_usage argv0).
Definition msg_cannot_open (path : list Z) : list Z := concat (pieces_cannot_open path).
Definition msg_read_error (path : list Z) : list Z := concat (pieces_read_error path).
Definition msg_too_big : list Z := concat pieces_too_big.
Definition msg_short_hdr : list Z := concat pieces_short_hdr.
Definition msg_cfg_overrun : list Z := concat pieces_cfg_overrun.

Definition emit_bytes (rc : Z) : list Z := concat (pieces_emit rc).

Definition ct_diag (msg : list Z) : ctrace := mkCT [(2, msg)] 2.

Definition cfg_word (data : list Z) : Z := znth data 0 + znth data 1 * 256.

Definition cfg_len (data : list Z) : Z := Z.land (cfg_word data) 0x7fff.

Definition cfg_count (data : list Z) : bool := Z.testbit (cfg_word data) 15.

Definition cfg_calls (data : list Z) : nat :=
let cfg := if 0 <? cfg_len data then znth data 2 else 0 in
Z.to_nat (1 + Z.land cfg 3).
Definition cfg_payload (data : list Z) : list Z := skipn (Z.to_nat (6 + cfg_len data)) data.

Definition target_trace (count : bool) (n : nat) (payload : list Z) : ctrace :=
let '(rc, eb) := canon_fuzz payload in
mkCT ([(2, eb); (1, emit_bytes rc)]
++ repeat (2, eb) (n - 1)
++ [(1, concat (repeat (emit_bytes rc) (n - 1)))])
(if count then 0 else if rc =? 0 then 0 else 1).

Definition file_trace (data : list Z) : ctrace :=
let len := zlength data in
if 67108864 <=? len then ct_diag msg_too_big
else if len <? 6 then ct_diag msg_short_hdr
else if len <? 6 + cfg_len data then ct_diag msg_cfg_overrun
else target_trace (cfg_count data) (cfg_calls data) (cfg_payload data).

Inductive oclass : Type := OCFail | OCDir | OCFile (data : list byte).

Definition open_class (path : list Z) (fs : Fs) : oclass :=
let p := map (Z_to_bv 8) path in
if (path_max <=? length p)%nat then OCFail
else match p with
| [] => OCFail
| _ :: _ => if path_eqb p dot_path then OCDir
else match fs_lookup fs p with
| None => OCFail
| Some data => OCFile data
end
end.

Definition ctrace_of (argv : list (list Z)) (fs : Fs) (ok : bool) : ctrace :=
if negb (Z.of_nat (length argv) =? 2) then ct_diag (msg_usage (nth 0 argv []))
else
let path := nth 1 argv [] in
match (if ok then open_class path fs else OCFail) with
| OCFail => ct_diag (msg_cannot_open path)
| OCDir => ct_diag (msg_read_error path)
| OCFile data => file_trace (map bv_unsigned data)
end.

Definition canonT (argv : list (list Z)) (fs : Fs) : list event -> Prop :=
fun tr => exists ok : bool, is_prefix tr (ct_events fs (ctrace_of argv fs ok)).

Definition Tc (inp : ProcInput) : list event -> Prop :=
canonT (map (map bv_unsigned) (in_argv inp)) (in_fs inp).

Definition ct_flat (ct : ctrace) : list event := concat (map seg_events (ct_segs ct)).

Lemma ct_flat_diag : forall msg, ct_flat (ct_diag msg) = evw 2 msg.
Proof. intros msg. unfold ct_flat, ct_diag. cbn [ct_segs map concat seg_events fst snd]. apply app_nil_r. Qed.

Lemma ct_events_flat : forall fs ct, ct_events fs ct = ct_flat ct ++ [ExitEv (Z_to_bv 64 (ct_code ct)) fs].
Proof. reflexivity. Qed.

Definition zeros_out (j : nat) : list Z := concat (repeat [48; 10] j).

Lemma zeros_out_S : forall n, zeros_out (S n) = [48; 10] ++ zeros_out n.
Proof. reflexivity. Qed.
Lemma zeros_out_app : forall j, zeros_out j ++ [48; 10] = zeros_out (S j).
Proof. induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. rewrite <- app_assoc, IH. reflexivity. Qed.
Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof. induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlength_app, IH. unfold zlength. cbn [length]. lia. Qed.

Definition calls_events (eb : list Z) (j : nat) : list event :=
match j with O => [] | S j' => evw 2 eb ++ evw 1 [48; 10] ++ concat (repeat (evw 2 eb) j') end.

Lemma calls_events_1 : forall eb, calls_events eb 1 = evw 2 eb ++ evw 1 [48; 10].
Proof. intros eb. cbn [calls_events repeat concat]. rewrite app_nil_r. reflexivity. Qed.

Lemma calls_events_S : forall eb j, calls_events eb (S (S j)) = calls_events eb (S j) ++ evw 2 eb.
Proof.
intros eb j. cbn [calls_events]. rewrite <- !app_assoc. do 2 f_equal.
change (repeat (evw 2 eb) (S j)) with (evw 2 eb :: repeat (evw 2 eb) j).
replace (evw 2 eb :: repeat (evw 2 eb) j) with (repeat (evw 2 eb) j ++ [evw 2 eb]).
- rewrite concat_app. cbn [concat]. rewrite app_nil_r. reflexivity.
- clear. induction j as [|j IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity.
Qed.

Lemma cfg_calls_pos : forall data, (1 <= cfg_calls data <= 4)%nat.
Proof.
intros data. unfold cfg_calls. set (cfg := if 0 <? cfg_len data then znth data 2 else 0).
change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)) as H. change (2^2) with 4 in *. lia.
Qed.

Lemma target_trace_flat : forall count n payload eb, (1 <= n)%nat -> canon_fuzz payload = (0, eb) ->
ct_code (target_trace count n payload) = 0
/\ ct_flat (target_trace count n payload) = calls_events eb n ++ evw 1 (zeros_out (n - 1)).
Proof.
intros count n payload eb Hn Hcf. unfold target_trace. rewrite Hcf. cbn [ct_code].
split; [destruct count; reflexivity|].
destruct n as [|j]; [lia|]. replace (S j - 1)%nat with j by lia.
unfold ct_flat. cbn [ct_segs]. rewrite !map_app, !concat_app. cbn [map concat seg_events fst snd calls_events].
rewrite !app_nil_r, <- !app_assoc. do 2 f_equal.
change (emit_bytes 0) with [48; 10]. fold (zeros_out j). f_equal.
clear. induction j as [|j IH]; [reflexivity|]. cbn [repeat map concat seg_events fst snd]. rewrite IH. reflexivity.
Qed.

Lemma file_trace_wf : forall data eb, zlength data < 67108864 -> ~ zlength data < 6 -> ~ zlength data < 6 + cfg_len data ->
canon_fuzz (cfg_payload data) = (0, eb) ->
ct_code (file_trace data) = 0
/\ ct_flat (file_trace data) = calls_events eb (cfg_calls data) ++ evw 1 (zeros_out (cfg_calls data - 1)).
Proof.
intros data eb Hb H1 H2 Hcf. unfold file_trace.
destruct (Z.leb_spec 67108864 (zlength data)); [lia|]. destruct (Z.ltb_spec (zlength data) 6); [lia|].
destruct (Z.ltb_spec (zlength data) (6 + cfg_len data)); [lia|].
apply target_trace_flat; [exact (proj1 (cfg_calls_pos data))| exact Hcf].
Qed.

Lemma file_trace_too_big : forall data, 67108864 <= zlength data -> file_trace data = ct_diag msg_too_big.
Proof. intros data H. unfold file_trace. destruct (Z.leb_spec 67108864 (zlength data)); [reflexivity| lia]. Qed.
Lemma file_trace_short : forall data, zlength data < 67108864 -> zlength data < 6 -> file_trace data = ct_diag msg_short_hdr.
Proof.
intros data H1 H2. unfold file_trace. destruct (Z.leb_spec 67108864 (zlength data)); [lia|].
destruct (Z.ltb_spec (zlength data) 6); [reflexivity| lia].
Qed.
Lemma file_trace_overrun : forall data, zlength data < 67108864 -> ~ zlength data < 6 -> zlength data < 6 + cfg_len data ->
file_trace data = ct_diag msg_cfg_overrun.
Proof.
intros data H1 H2 H3. unfold file_trace. destruct (Z.leb_spec 67108864 (zlength data)); [lia|].
destruct (Z.ltb_spec (zlength data) 6); [lia|]. destruct (Z.ltb_spec (zlength data) (6 + cfg_len data)); [reflexivity| lia].
Qed.

Definition fuzz_defined (payload : list Z) : Prop := prun (p_fuzz_one payload) p0 <> None.

Definition run_defined (fs : Fs) (argv : list (list Z)) (b : bool) : Prop :=
Z.of_nat (length argv) = 2 ->
forall data, (if b then open_class (nth 1 argv []) fs else OCFail) = OCFile data ->
let content := map bv_unsigned data in
zlength content < 67108864 -> ~ zlength content < 6 -> ~ zlength content < 6 + cfg_len content ->
fuzz_defined (cfg_payload content).

Lemma fuzz_defined_some : forall payload, fuzz_defined payload ->
exists eb, prun (p_fuzz_one payload) p0 = Some (fst (canon_fuzz payload), mkP eb) /\ snd (canon_fuzz payload) = eb.
Proof.
intros payload H. unfold fuzz_defined in H. unfold canon_fuzz.
destruct (prun (p_fuzz_one payload) p0) as [[rc [eb]]|]; [|contradiction]. exists eb. split; reflexivity.
Qed.

Lemma p_fuzz_one_rc : forall payload q rc q', prun (p_fuzz_one payload) q = Some (rc, q') -> rc = 0.
Proof.
intros payload q rc q' H. unfold p_fuzz_one, X1od.LLVMFuzzerTestOneInput in H. cbv zeta in H.
destruct (X1od.MAX_FUZZ_SIZE <? zlength payload); [rewrite prun_ret in H; congruence|].
apply prun_bind_some in H. destruct H as ([bits|] & q1 & _ & H); [|rewrite prun_munr in H; discriminate].
apply prun_bind_some in H. destruct H as ([h|] & q2 & _ & H).
- apply prun_bind_some in H. destruct H as (u & q3 & _ & H). rewrite prun_ret in H. congruence.
- rewrite prun_ret in H. congruence.
Qed.

Lemma canon_fuzz_of_prun : forall payload rc q', prun (p_fuzz_one payload) p0 = Some (rc, q') -> canon_fuzz payload = (0, p_err q').
Proof. intros payload rc q' H. unfold canon_fuzz. rewrite H. rewrite (p_fuzz_one_rc _ _ _ _ H). reflexivity. Qed.

Lemma canonT_nil : forall argv fs, canonT argv fs [].
Proof. intros. exists false. apply is_prefix_nil. Qed.

Lemma canonT_pclosed : forall argv fs tr tr',
canonT argv fs tr -> is_prefix tr' tr -> canonT argv fs tr'.
Proof.
intros argv fs tr tr' (ok & Hp) Hp'. exists ok. eapply is_prefix_trans; eassumption.
Qed.

Lemma canonT_max : forall argv fs ok, canonT argv fs (ct_events fs (ctrace_of argv fs ok)).
Proof. intros argv fs ok. exists ok. apply is_prefix_refl. Qed.

Lemma ctrace_of_fail : forall argv fs ok,
Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs = OCFail ->
ctrace_of argv fs ok = ct_diag (msg_cannot_open (nth 1 argv [])).
Proof.
intros argv fs ok Hl Hc. unfold ctrace_of. rewrite Hl. cbn [Z.eqb negb].
destruct ok; [rewrite Hc|]; reflexivity.
Qed.

Lemma evw_app : forall fd l1 l2, evw fd (l1 ++ l2) = evw fd l1 ++ evw fd l2.
Proof. intros. unfold evw. apply map_app. Qed.

Lemma evw_nil : forall fd, evw fd [] = [].
Proof. reflexivity. Qed.

Lemma ct_code_cases : forall argv fs ok,
ct_code (ctrace_of argv fs ok) = 0 \/ ct_code (ctrace_of argv fs ok) = 1 \/ ct_code (ctrace_of argv fs ok) = 2.
Proof.
intros argv fs ok. unfold ctrace_of. destruct (negb _); [right; right; reflexivity|].
destruct (if ok then open_class _ fs else OCFail) as [| |data]; try (right; right; reflexivity).
unfold file_trace.
repeat match goal with |- context [if ?c then ct_diag _ else _] => destruct c; [right; right; reflexivity|] end.
unfold target_trace. destruct (canon_fuzz _) as [rc eb]. cbn [ct_code].
destruct (cfg_count _); [left; reflexivity|]. destruct (rc =? 0); [left| right; left]; reflexivity.
Qed.

Lemma in_prefix {A} : forall (l1 l2 : list A) x, is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
induction l1 as [|a l1 IH]; intros l2 x Hp Hin; [destruct Hin|].
destruct l2 as [|b l2]; cbn in Hp; [contradiction|]. destruct Hp as [-> Hp].
destruct Hin as [->|Hin]; [left; reflexivity| right; exact (IH l2 x Hp Hin)].
Qed.

Lemma ct_events_nokill : forall fs ct sig fs', ~ In (KillEv sig fs') (ct_events fs ct).
Proof.
intros fs ct sig fs' Hin. unfold ct_events in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- apply in_concat in Hin. destruct Hin as (l & Hl & Hin). apply in_map_iff in Hl. destruct Hl as (sg & <- & _).
unfold seg_events, evw in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb.
- destruct Hin as [Hin|[]]. discriminate Hin.
Qed.

Theorem canonT_nokill : forall argv fs tr sig fs', canonT argv fs tr -> ~ In (KillEv sig fs') tr.
Proof.
intros argv fs tr sig fs' (ok & Hp) Hin.
exact (ct_events_nokill fs _ sig fs' (in_prefix _ _ _ Hp Hin)).
Qed.

Example msg_too_big_len : zlength msg_too_big = 38.
Proof. vm_compute. reflexivity. Qed.
Example msg_short_hdr_len : zlength msg_short_hdr = 31.
Proof. vm_compute. reflexivity. Qed.
Example emit_bytes_0 : emit_bytes 0 = [48; 10].
Proof. vm_compute. reflexivity. Qed.
Example emit_bytes_m12 : emit_bytes (-12) = [45; 49; 50; 10].
Proof. vm_compute. reflexivity. Qed.
