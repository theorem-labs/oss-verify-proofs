(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of plugin-hostd/fuzz_command's sup_broadcast walk, in the form
   of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call): from the return of arg_line (0x8b048)
   the frame is restored and `j answer` (0x8b06c) runs answer at the entry stack pointer; answer's statement
   (a Section hypothesis) gives the post-condition.

   Pass-4/5 re-fit: TANSWER is taken at every FP state and used at the entry's fx (no
   earlier call changes the FP state); answer's rounding-mode-0 premise is the entry's (HFRM); answer is the last
   step, through PaFx.v's cl_callS_wideF, and PaFx.v's apost_baseF_intro closes sup_broadcast's apost_baseF.
   Statement pass 5 removed astack_pres, so no stack fact is built for answer's entry; the frame chain answer's
   afn_pre asks is sup_broadcast's own afn_pre chain (s0 at the tail jump is the entry s0), kept by achain_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_broadcast_s3.v, with its module paths and module names changed; 96 of its 124 lines of code are new or changed and 402 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command: the post-condition the two arms prove
   (sr_post: tsup_remove_spec's, lib/A/Prog/sup_remove_c.v:90-104) and its derivation from the tail piece's post
   (sr_tail_stmt, sup_remove_s1.v) and an arm's block facts (sr_blocks, sup_remove_b.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_remove_s1 sup_remove_r sup_remove_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the model term after a symbolic run, named once so it does not grow over a chain of runs (trap 1) *)
Ltac sr_fold_md :=
repeat match goal with |- context [with_vm_backing ?l ?m ?d] =>
  let v := fresh "mdv" in set (v := with_vm_backing l m d) in *; clearbody v end.

Lemma sr_nodup_pw : forall (l : list (Z * Z)),
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall x, In x l -> 0 <= snd x) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hn; [constructor|]. cbn [map pairwise] in Hp. destruct Hp as [Hf Hp].
constructor; [|apply IH; [exact Hp | intros y Hy; apply Hn; right; exact Hy]].
intros Hx. rewrite Forall_map in Hf. pose proof (proj1 (Forall_forall _ _) Hf x Hx) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd x) (Hn x (or_introl eq_refl))). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

(* the post-condition the statement asks (tsup_remove_spec, sup_remove_c.v:90-104) *)
Definition sr_post (ly : alayout) (S : astate) (O : list (Z * Z)) (R : rstate) (id : Z)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_m R id = (R', snd (sup_remove_m R id)) /\
 let n := Z.of_nat (length (snd (sup_remove_m R id))) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q (snd (sup_remove_m R id)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE id (snd (sup_remove_m R id)) /\
 mo_le MT S S' (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id))).

(* live blocks: distinct starts, no repetition *)
Lemma sr_fst_inj : forall ly S (W : world SEGS) mem md x y, AR SEGS B ly S W mem md ->
In x (ablocks B ly S) -> In y (ablocks B ly S) -> fst x = fst y -> x = y.
Proof.
intros ly S W mem md [a m] [b k] HAR Hx Hy Ef. cbn [fst] in Ef. subst b.
destruct (sr_b_pair_dec (a, m) (a, k)) as [E|Ne]; [exact E|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md a m a k HAR Hx Hy Ne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS ly S W mem md a m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks _ _ LAWS ly S W mem md a k HAR Hy) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos m ltac:(lia)). pose proof (req_size_pos k ltac:(lia)). lia.
Qed.
Lemma sr_nodup_blocks : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply sr_nodup_pw.
- destruct (ablocks B ly S) as [|[p n] l] eqn:El; [cbn; exact I|].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR ltac:(rewrite El; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite El in Hpw. exact Hpw.
- intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.

(* the post-condition from the tail piece's post and the arm's block facts: the arm freed F (the spill's arguments,
   [] on the table arm), arg_i made (p, k), answer freed the block at old and made (p1, n), (p2, n) *)
Lemma sr_post_of : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) (R : rstate) (id : Z) lyt St
  (Ot O1 F B1 : list (Z * Z)) (p k old : Z) ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md',
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (B1 ++ F) ->
(forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
Permutation (ablocks B lyt St) ((p, k) :: B1) -> ~ In (p, k) B1 ->
(forall pn, In pn Ot <-> In pn O1 \/ pn = (p, k)) ->
(forall pn, In pn Ot -> In pn (ablocks B lyt St)) ->
(forall pn, In pn (ablocks B lyt St) -> fst pn = old -> In pn O) ->
blocks_bytes St <= blocks_bytes S + LIVE_ARG_I id ->
AR SEGS B ly' S' W' mem' md' ->
(exists p1 p2 O', let n := Z.of_nat (length (snd (sup_remove_m R id))) + 1 in
   getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
   (forall pn, In pn (ablocks B lyt St) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
   (forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B lyt St) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
   rec_repA B ly' S' (rdW W' mem') (fst (sup_remove_m R id)) O' /\
   (forall pn, In pn O' <-> (In pn Ot /\ fst pn <> old) \/ pn = (p1, n)) /\
   astr_atR (rdW W' mem') p2 (snd (sup_remove_m R id)) /\
   blocks_bytes S' <= blocks_bytes St + LIVE_ANSWER (snd (sup_remove_m R id)) /\
   mo_le MT S S' (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id)))) ->
sr_post ly S O R id ly' S' W' regs' mem' md'.
Proof.
intros ly S W mem md O R id lyt St Ot O1 F B1 p k old ly' S' W' regs' mem' md'
  HAR H01 HF HO1 H12 Hpk HO2 HOB Hold HBB HAR'
  (p1 & p2 & O' & Hq & Hq4 & Hne & Hfr & H23 & HREP' & HO3 & Hstr & HBB' & HMLE).
set (n := Z.of_nat (length (snd (sup_remove_m R id))) + 1) in *.
assert (HO3B : forall pn, In pn O' -> In pn (ablocks B ly' S')).
{ destruct HREP' as (Q' & HQ' & HOQ'). intros pn Hpn. apply HOQ' in Hpn.
  exact (proj1 (proj2 (sr_lay_live _ _ _ _ _ _ HQ') pn Hpn)). }
destruct (sr_blocks (ablocks B ly S) B1 (ablocks B lyt St) (ablocks B ly' S') O O1 Ot O' F p k p1 p2 n old
  H01 (sr_nodup_blocks ly S W mem md HAR) HF HO1 H12 Hpk HO2 HOB H23 Hfr Hne HO3 Hold HO3B
  (fun x y Hx Hy E => sr_fst_inj ly' S' W' mem' md' x y HAR' Hx Hy E))
  as (C1 & C2 & C3 & C4 & C5 & C7).
unfold sr_post. exists (fst (sup_remove_m R id)), O', p2.
split; [destruct (sup_remove_m R id); reflexivity|]. fold n.
split; [exact Hq|]. split; [exact Hq4|]. split; [exact HREP'|]. split; [exact C1|]. split; [exact C2|].
split; [exact C3|]. split; [exact C4|].
split; [intros pn Hpn HnO E; subst pn; exact (HnO (C5 Hpn))|].
split; [exact C7|]. split; [exact Hstr|].
split; [unfold LIVE_SUP_REMOVE; lia | exact HMLE].
Qed.
End c.
End b.
End a.
