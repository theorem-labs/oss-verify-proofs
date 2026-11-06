(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-10: copied from an earlier version of lib/A/Prog/RecBTemplate.v (the template walk)
   for sup_instance_verb's walk; the zero-shadow range lemmas follow the regenerated Tfib_zero_shadow (lib/A/AF0m.v),
   where g_rec and record.spill lie in two ranges. *)

(* The recorder-call template, blocks P / S / TA of the recorder-call walk plan.

   Eighteen functions of recorder.c:379-569 are one shape: an inlined record(FN) (block P), argument blocks
   (block S), and a tail (TA: rec_shape_of then a tail jump into answer). This file carries what they share:
   the seed of a walk segment over the recorder's globals (`recb_seed_*`), the model steps of record() and of
   arg_s over `rec_repA` (`recb_slot_*`), and the tail composition (`recb_tail_answer`), each parametric in the
   member's frame size, registers and constants. lib/A/Prog/sup_worker_list.v and lib/A/Prog/sup_reset.v
   instantiate them; the other 16 members instantiate the same lemmas with their own FN, DEFAULTs and tail.

   Named Section hypotheses (this port's decision, 2026-10-28 22:10Z: carry the per-binary facts under the
   final names until lib/A/Prog/CmdRecFacts.v lands, then drop each hypothesis for the lemma of the same name):
   `LAWS`, `TL`, `cmd_addressable_in`, `cmd_prog_unowned`, `cmd_rec_cells`, and `awr_prog_in_fp`, which is
   the core's new `awr_byte` disjunct (YCbq.v:496-504) in the form this tree's
   `awr_byte` takes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
(* recb_PG, the program's writable statics as (start, length), and its two ranges recb_grec_in / recb_spill_in are
   the kit's; the walks that import this file name them through it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
Export RecBLemmas(recb_PG, recb_grec_in, recb_spill_in).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the atoms a recorder walk adds above the 32 registers: the shadow base, the call count, the slot, and the
   callee-saved registers the member's frame holds *)
Definition RB_SB : nat := 32.
Definition RB_N : nat := 33.
Definition RB_C : nat := 34.
Definition rbs_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition rbs_extra (regs : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) rbs_saved.
Definition Bxr : sv := SOff RB_SB 0.
Definition rbs_SH : list shent := [mkSHE RB_C 0 CALL_SIZE].
(* the object atoms of the listing: g_rec, record.spill *)
Definition RB_GREC : nat := A_OBJ 44.
Definition RB_SPILL : nat := A_OBJ 51.
Definition rbs_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (RB_SB, mkAF SB SB 0); (RB_N, mkAF 0 16 0);
         (RB_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (RB_GREC, mkAF A_G_REC A_G_REC 3); (RB_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
(* the frame of the member: [sp + d, sp) of its own stack, written by the prologue *)
Definition rbs_stack (d : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) d 0 d 0 cs.
(* g_rec.ncalls, the only word of g_rec the inlined record() reads and writes *)
Definition rbs_ncalls : YP09.region :=
YP09.mkRegion (Some RB_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff RB_N 0))].
(* the slot the call records: g_rec.calls[k] or record.spill *)
Definition rbs_slot (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some RB_C) 0 CALL_SIZE 0 CALL_SIZE cs.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
(* The two per-binary facts about the program's own writable statics that the kit does not yet carry. Each is a
   field lib/A/Prog/CmdRecFacts.v states (this port's decision, 2026-10-28): replace the hypothesis by the
   lemma of the same name when that file lands.
   `recb_PG` is `cmd_PG` written as `as_prog_static` lists it, a base and a LENGTH, which is what `in_zr` reads
   (YG0n.v:197), where `cmd_PG`'s pairs are a base and an end (a footprint). *)
(* CmdRecFacts.v's `cif_prog_img`: every byte of g_rec / record.spill / g_quitting is in the image. *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
(* CmdRecFacts.v's `cmd_prog_writable` (PROG_PRESENT): those bytes are present, which the core's `awr_byte_cases`
   asks of a footprint write to a program static (YCbq.v:2032-2033). *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* --- the recorder's globals, as the walk needs them ----------------------------------------------------- *)

Lemma rbs_grec_val : VAL RB_GREC = A_G_REC.
Proof. unfold RB_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rbs_spill_val : VAL RB_SPILL = A_REC_SPILL.
Proof. unfold RB_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rbs_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. reflexivity. Qed.
Lemma rbs_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. reflexivity. Qed.

(* --- the walk's environment -------------------------------------------------------------------------- *)

(* what every segment of a recorder walk asks of its environment: the stack pointer of the member's entry,
   the shadow base, the call count the slot came from, and the slot itself *)
Definition rbs_env_ok (E : env) (sp n c : Z) : Prop :=
img_env VAL A_LIM E /\ ew E 2%nat = Z_to_bv 64 sp /\
ew E RB_SB = Z_to_bv 64 SB /\ ew E RB_N = Z_to_bv 64 n /\ ew E RB_C = Z_to_bv 64 c.
(* the slot the inlined record() picked: an entry of g_rec's table, or record.spill *)
Definition rbs_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma rbs_slot_bounds : forall c, rbs_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

(* the record's zero-shadow ranges that hold the recorder's globals: g_rec ends the range from 0xada00, record.spill
   has its own (AF0m.v Tfib_zero_shadow, regenerated) *)
Definition RB_ZSH : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition RB_ZSH_SP : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).
Lemma rbs_in_pairs : forall x l, existsb (fun y => (fst y =? fst x) && (snd y =? snd x)) l = true -> In x l.
Proof.
intros x l H. apply existsb_exists in H as (y & Hy & E). apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. destruct x as [x1 x2], y as [y1 y2]. cbn in E1, E2. subst. exact Hy.
Qed.
Lemma rbs_zsh_in : In RB_ZSH Tfib_zero_shadow.
Proof. apply rbs_in_pairs. vm_compute. reflexivity. Qed.
Lemma rbs_zsh_sp_in : In RB_ZSH_SP Tfib_zero_shadow.
Proof. apply rbs_in_pairs. vm_compute. reflexivity. Qed.

Lemma rbs_addressable : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0xada00 <= a -> a + n <= 0x5e3b00 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md RB_ZSH a n HAR rbs_zsh_in
  ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

Lemma rbs_addressable_sp : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0x5e3be0 <= a -> a + n <= 0x5e3c18 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md RB_ZSH_SP a n HAR rbs_zsh_sp_in
  ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

Lemma rbs_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> rbs_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc.
destruct Hc as [(H1 & H2 & _) | ->].
- apply (rbs_addressable ly S W mem md); [exact HAR | |];
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia.
- apply (rbs_addressable_sp ly S W mem md); [exact HAR | |]; unfold A_REC_SPILL, CALL_SIZE; lia.
Qed.

Lemma rbs_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma rbs_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma rbs_facts_ok : forall E sp n c,
rbs_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> rbs_slot_ok c ->
facts_ok E rbs_facts.
Proof.
intros E sp n c (HEI & E2 & ESB & EN & EC) Hsp Hsp16 Hn Hc.
destruct (rbs_slot_bounds c Hc) as [Hcb Hc8].
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)), rbs_grec_val;
      reflexivity).
assert (ES : ew E RB_SPILL = Z_to_bv 64 A_REC_SPILL)
  by (rewrite (img_env_atomP E RB_SPILL HEI ltac:(unfold RB_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), rbs_spill_val;
      reflexivity).
unfold facts_ok, rbs_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
- apply (rbs_afact E 2%nat sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
- apply (rbs_afact E RB_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (rbs_afact E RB_N n); [exact EN | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (rbs_afact E RB_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
  | change (2 ^ 3) with 8; exact Hc8 | lia].
- apply (rbs_afact E RB_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia
  | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
- apply (rbs_afact E RB_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia
  | change (2 ^ 3) with 8; unfold A_REC_SPILL; reflexivity | lia].
Qed.

Lemma rbs_sh_ok : forall ly S W mem md E sp n c,
AR SEGS B ly S W mem md -> rbs_env_ok E sp n c -> rbs_slot_ok c ->
sh_ok SEGS Bxr rbs_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E sp n c HAR HE Hc.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (rbs_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, rbs_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bxr RB_C c CALL_SIZE c 0 CALL_SIZE).
- exact (rbs_slot_addressable ly S W mem md c HAR Hc).
- unfold Bxr. apply rbs_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply rbs_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

End e.
End f.
End d.
