(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the code-level helpers of sup_lv2_worker_set's ASan+UBSan walk
   (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan, entry 0x8c0cc, 28 instructions): the call targets of
   record / arg_s / rec_shape_of / answer, the verb literal "lv2_worker_set" (.str.13, 0x21ee0, the listing's object
   A_OBJ 75) with the premise rec_shape_of's statement (lib/B/Prog/rec_shape_of_c.v:91-94) asks of it, and the model
   step. After the ASan walk's lib/A/Prog/sup_lv2_worker_set_s2.v (a working branch 5c647899d9f:
   slw_verb, slw_verb_lit, slw_abytes_prefix, slw_unowned_rng and its rec_shape_of verb premise at :1409-1431), on
   B's astr_argA (lib/B/Prog/CmdRep.v): the read-only arm's checks cmd_addr_b, cmd_hull_b (lib/B/Prog/CmdChk.v) and
   the literal's end in cmd_ro_ends (lib/B/Prog/CmdRo.v) are closed computations. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdChk CmdRep CmdObj CmdRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* --- the verb literal and the model step ------------------------------------------------------------------ *)
(* the verb sup_lv2_worker_set passes to rec_shape_of (0x8c108-0x8c110: a0 = .str.13, a1 = 14) *)
Definition slw_verb : list byte := bstr "lv2_worker_set".

Lemma slw_verb_lit : RO_lit_21ee0 = slw_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma slw_verb_len : Z.of_nat (length slw_verb) = 14.
Proof. vm_compute. reflexivity. Qed.

(* the verb has no NUL byte *)
Lemma slw_verb_nonul : ~ In (Z_to_bv 8 0) slw_verb.
Proof.
intros Hz. apply (in_map bv_unsigned) in Hz. vm_compute in Hz.
repeat (destruct Hz as [Hz|Hz]; [discriminate Hz|]). exact Hz.
Qed.

(* the model step (RecModel.v:66, :159-160): the call recorded in the slot record() returns, then answered with
   the shape rec_shape_of returns for the verb *)
Lemma slw_model : forall R uri worker,
sup_lv2_worker_set_m R uri worker =
rec_answer (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) (REC_LV2_WORKER_SET, [sarg uri; sarg worker])
  (shape_of slw_verb) true.
Proof. reflexivity. Qed.

Lemma slw_abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by lia. exact H.
Qed.

(* a byte range none of a concrete list of ranges holds *)
Lemma slw_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* the literal's record checks (lib/B/Prog/CmdChk.v) and its end (lib/B/Prog/CmdRo.v), by computation *)
Lemma slw_lit_addr : cmd_addr_b 0x21ee0 15 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma slw_lit_hull : cmd_hull_b 0x21ee0 15 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma slw_lit_end : In (0x21ee0 + 14) cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb (0x21ee0 + 14)) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (x & Hx & Hq). apply Z.eqb_eq in Hq. rewrite Hq. exact Hx.
Qed.
Lemma slw_lit_unowned : forall i, 0 <= i < 15 ->
~ Exists (in_zr (0x21ee0 + i)) Tfib_owned_static /\ ~ (TFIB_ERRNO <= 0x21ee0 + i < TFIB_ERRNO + 4).
Proof.
intros i Hi. split; [apply (slw_unowned_rng 0x21ee0 15); [vm_compute; reflexivity | exact Hi]|].
unfold TFIB_ERRNO. lia.
Qed.

(* the conjunct of a long conjunction that holds the literal address [a]: a syntactic search that drops the leading
   conjuncts of H in place, so no conjunct is unified with the goal and no nested proj2 term is retyped *)
Local Ltac slw_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

Local Ltac slw_in := repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Section e.
Variable B : asyms.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name (RECB-NAMED-HYPS.md) *)
Hypothesis HB : CmdBSyms B.
(* the statement's bridge from the listing's object atoms to the image's addresses (lib/B/Prog/CmdObj.v:39-40) *)
Hypothesis VOBJS : cmd_val_objs.
(* the call targets of the program functions (lib/B/Prog/CmdObj.v:44-45), under its canonical name *)
Hypothesis SIGP : cmd_sig_prog.

(* --- the call targets: arg_s (0x8c0f8, 0x8c104), rec_shape_of (0x8c114), answer (0x8c138); record's (0x8c0ec) is
   CmdRecAns.rca_sig_record ---------------------------------------------------------------------------------- *)
Lemma slw_sig : forall s, In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. intros s Hs. exact (SIGP s Hs). Qed.
Local Ltac slw_in_syms := cbv [cmd_prog_syms]; slw_in.
Lemma slw_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma slw_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma slw_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.

(* the auipc/addi pair at 0x8c108 (`PHi 10 176; PAddHi 10 10 176 (A_OBJ 75) 0`) leaves the literal's address in a0;
   nothing is loaded or stored through the A_HI 176 value (0x22108) *)
Lemma slw_lit_val : VAL (A_OBJ 75) = 0x21ee0.
Proof. rewrite (VOBJS 75%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* --- rec_shape_of's verb premise (rec_shape_of_c.v:91-94) at the literal ---------------------------------- *)
Lemma slw_verb_ok : forall ly S (rd : reader),
cmd_ro_ok rd -> cmd_ro_in (in_roP SEGS RLO RHI) ->
Z.of_nat (length slw_verb) <= 16 ->
abytes_atR rd 0x21ee0 slw_verb /\
(in_blockA (ablocks B ly S) 0x21ee0 (Z.of_nat (length slw_verb)) \/
 astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21ee0 (Some slw_verb)).
Proof.
intros ly S rd HROK HRI _.
assert (HLIT : abytes_atR rd 0x21ee0 RO_lit_21ee0).
{ destruct HROK as [HBY _]. unfold cmd_ro_bytes in HBY. slw_projz HBY 0x21ee0. }
assert (HLITro : forall i, 0 <= i < 15 -> in_roP SEGS RLO RHI (0x21ee0 + i)).
{ unfold cmd_ro_in in HRI. slw_projz HRI 0x21ee0. }
rewrite slw_verb_lit in HLIT. split; [exact (slw_abytes_prefix _ _ _ _ HLIT)|].
right. cbn [astr_argA]. rewrite slw_verb_len. split; [lia|]. split.
{ split; [exact HLIT | exact slw_verb_nonul]. }
split; [unfold LMAX; lia|]. right. split; [|split; [exact slw_lit_addr | split; [exact slw_lit_hull|]]].
- intros i Hi. split; [apply HLITro; lia|]. rewrite (ts_owned B HB), (ts_errno B HB).
  exact (slw_lit_unowned i Hi).
- exact slw_lit_end.
Qed.
End e.
End f.
End d.
