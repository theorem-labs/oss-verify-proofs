(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Export YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI22.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Inductive frames_run (g : YO07.gcfg) : nat -> YO07.gif_st -> list Z -> YO07.gif_st -> Prop :=
| fr_fuel : forall st s, frames_run g O st s st
| fr_stop : forall fuel st s,
frames_run g (S fuel) st s st
| fr_step : forall fuel st s st1 st' attr gen delay tidx nlp lpal img s7,
parse_frame g s = (true, (attr, gen, delay, tidx, nlp, lpal, img), s7) ->
(st1 = YO07.add_frame g st attr gen delay tidx nlp lpal img \/ af_cut g st st1 attr gen delay tidx nlp lpal img) ->
frames_run g fuel st1 s7 st' ->
frames_run g (S fuel) st s st'.
Lemma frames_loop_run : forall g fuel st s, frames_run g fuel st s (YO07.frames_loop fuel g st s).
Proof.
intros g fuel. induction fuel as [|fuel IH]; intros st s; [apply fr_fuel|].
rewrite frames_loop_step. destruct (parse_frame g s) as [[ok [[[[[[attr gen] delay] tidx] nlp] lpal] img]] s7] eqn:HP.
destruct ok; [| apply fr_stop].
eapply fr_step; [exact HP | left; reflexivity | apply IH].
Qed.
Lemma frames_run_stop : forall g fuel st s, frames_run g fuel st s st.
Proof. intros g [|fuel] st s; [apply fr_fuel | apply fr_stop]. Qed.
Lemma frames_run_fuel : forall g fuel st s st', frames_run g fuel st s st' -> forall fuel', (fuel <= fuel')%nat -> frames_run g fuel' st s st'.
Proof.
intros g fuel st s st' H. induction H as [st s | fuel st s | fuel st s st1 st' attr gen delay tidx nlp lpal img s7 HP Hs _ IH]; intros fuel' Hle.
- apply frames_run_stop.
- apply frames_run_stop.
- destruct fuel' as [|f']; [lia|]. eapply fr_step; [exact HP | exact Hs | apply IH; lia].
Qed.
Definition ff_run (payload : list Z) (OUT : list (list Z)) : Prop :=
exists g loops rest st', ff_cfg payload = Some (g, loops, rest) /\ g_opens g = true /\ g_sgct_ok g = true /\
frames_run g 16 (gs0 g loops) rest st' /\ close_out g st' OUT.
Definition ff_made (payload : list Z) (key' : option (list byte)) : Prop :=
exists g loops rest, ff_cfg payload = Some (g, loops, rest) /\ g_opens g = true /\
(key' = Some (bytes []) \/
exists st' OUT, g_sgct_ok g = true /\ frames_run g 16 (gs0 g loops) rest st' /\ close_out g st' OUT /\
key' = Some (bytes (concat OUT ++ [59]))).
Definition ff_key (key0 : option (list byte)) (payload : list Z) (key' : option (list byte)) : Prop :=
key' = key0 \/ (ff_cfg payload <> None /\ key' = None) \/ ff_made payload key'.
Lemma ff_made_key : forall key0 payload key', ff_made payload key' -> ff_key key0 payload key'.
Proof. intros key0 payload key' H. right. right. exact H. Qed.
Lemma ff_run_made : forall payload OUT, ff_run payload OUT -> ff_made payload (Some (bytes (concat OUT ++ [59]))).
Proof.
intros payload OUT (g & loops & rest & st' & Hc & Ho & Hs & Hr & Hcl). exists g, loops, rest. split; [exact Hc|]. split; [exact Ho|].
right. exists st', OUT. auto.
Qed.
Lemma ff_chunks_run : forall payload cs, YO07.ff_chunks payload = Some cs -> cs = [] \/ ff_run payload cs.
Proof.
intros payload cs H. unfold YO07.ff_chunks in H. unfold ff_run, ff_cfg, hdr5, g_opens, g_sgct_ok, g_sgct, gs0.
destruct (YO07.rd payload 2) as [[e1 w] s1]. destruct (YO07.rd s1 2) as [[e2 h] s2]. destruct (YO07.rd s2 4) as [[e3 a] s3].
destruct (YO07.rd s3 4) as [[e4 ge] s4]. destruct (YO07.rd s4 2) as [[e5 n] s5].
destruct (if YO07.flag (YO07.le_bytes a) 4 then (false, [], s5) else YO07.rd s5 (YO07.le_bytes n * 3)) as [[e6 gpal] s6].
destruct (e1 || e2 || e3 || e4 || e5); [discriminate H|]. destruct e6; [discriminate H|]. cbn [orb] in H |- *.
destruct (100000000 <? YO07.le_bytes w * YO07.le_bytes h); [discriminate H|].
destruct ((YO07.le_bytes w =? 0) || (YO07.le_bytes h =? 0)) eqn:E0; [discriminate H|].
destruct (256 <? (if YO07.flag (YO07.le_bytes a) 4 then 0 else YO07.le_bytes n)) eqn:E.
- left. injection H as <-. reflexivity.
- right. injection H as <-.
eexists _, 0, s6, _. split; [reflexivity|]. cbn [YO07.g_w YO07.g_h YO07.g_attr YO07.g_ngp YO07.g_gpal negb].
split; [rewrite E0; reflexivity|]. split; [rewrite E; reflexivity|]. split; [| left; reflexivity].
unfold raw_attr_of. apply frames_loop_run.
Qed.
Lemma ff_output_key : forall key0 payload bs, YO07.ff_output payload = Some bs -> ff_key key0 payload (Some (bytes bs)).
Proof.
intros key0 payload bs H. unfold YO07.ff_output in H.
destruct (YO07.ff_chunks payload) as [cs|] eqn:E; [|discriminate H]. cbn [option_map] in H. injection H as <-.
assert (Hcfg : exists g loops rest, ff_cfg payload = Some (g, loops, rest) /\ g_opens g = true).
{ unfold YO07.ff_chunks in E. unfold ff_cfg, hdr5, g_opens.
destruct (YO07.rd payload 2) as [[e1 w] s1]. destruct (YO07.rd s1 2) as [[e2 h] s2]. destruct (YO07.rd s2 4) as [[e3 a] s3].
destruct (YO07.rd s3 4) as [[e4 ge] s4]. destruct (YO07.rd s4 2) as [[e5 n] s5].
destruct (if YO07.flag (YO07.le_bytes a) 4 then (false, [], s5) else YO07.rd s5 (YO07.le_bytes n * 3)) as [[e6 gpal] s6].
destruct (e1 || e2 || e3 || e4 || e5); [discriminate E|]. destruct e6; [discriminate E|]. cbn [orb] in E |- *.
destruct (100000000 <? YO07.le_bytes w * YO07.le_bytes h); [discriminate E|].
destruct ((YO07.le_bytes w =? 0) || (YO07.le_bytes h =? 0)) eqn:E0; [discriminate E|].
eexists _, 0, s6. split; [reflexivity|]. cbn [YO07.g_w YO07.g_h negb]. rewrite E0. reflexivity. }
destruct Hcfg as (g & loops & rest & Hc & Ho).
destruct (ff_chunks_run payload cs E) as [-> | Hrun].
- right. right. exists g, loops, rest. split; [exact Hc|]. split; [exact Ho|]. left. reflexivity.
- destruct cs as [|c cs']; [right; right; exists g, loops, rest; split; [exact Hc|]; split; [exact Ho|]; left; reflexivity|].
cbn [YO07.file_of_chunks]. apply ff_made_key. apply ff_run_made. exact Hrun.
Qed.
