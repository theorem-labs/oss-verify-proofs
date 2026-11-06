(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)

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
(* recb_PG, the program's writable statics as (start, length), its two ranges recb_grec_in / recb_spill_in, and
   recb_ts_prog_m (the record pins them: CmdBSyms' ts_prog) are the kit's; the walks that import this file name
   them through it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
Export RecBLemmas(recb_PG, recb_grec_in, recb_spill_in, recb_ts_prog_m).
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
Definition rbt_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition rbt_extra (regs : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) rbt_saved.
Definition Bxr : sv := SOff RB_SB 0.
Definition rbt_SH : list shent := [mkSHE RB_C 0 CALL_SIZE].
(* the object atoms of the listing: g_rec, record.spill *)
Definition RB_GREC : nat := A_OBJ 44.
Definition RB_SPILL : nat := A_OBJ 51.
(* The call count's atom carries the arm's bounds: [0, 15] on the arm that takes a slot of the table, [16, 16]
   on the arm that spills. With them the symbolic executor decides record()'s `bne ncalls, 16` itself (the
   spill arm hands it the literal 16 as the loaded value), so the walk has no branch to split. *)
Definition rbt_facts (lo hi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (RB_SB, mkAF SB SB 0); (RB_N, mkAF lo hi 0);
         (RB_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (RB_GREC, mkAF A_G_REC A_G_REC 3); (RB_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
(* the frame of the member: [sp + d, sp) of its own stack, written by the prologue *)
Definition rbt_stack (d : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) d 0 d 0 cs.
(* g_rec.ncalls, the only word of g_rec the inlined record() reads and writes *)
Definition rbt_ncalls (v : sv) : YP09.region :=
YP09.mkRegion (Some RB_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 v)].
(* the slot the call records: g_rec.calls[k] or record.spill *)
Definition rbt_slot (cs : list YP09.chunk) : YP09.region :=
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
(* The two per-binary facts about the program's own writable statics that the kit does not carry yet. Each is a
   field lib/A/Prog/CmdRecFacts.v states (this port's decision and the recorder walks' named hypotheses,
   2026-10-28): replace the hypothesis by the lemma of the same name when that file lands.
   `recb_PG` is `cmd_PG` written as `as_prog_static` lists it, a base and a LENGTH, which is what `in_zr` reads
   (YG0n.v:197), where `cmd_PG`'s pairs are a base and an end (a footprint). *)
(* CmdRecFacts.v's `cmd_prog_img`: every byte of g_rec / record.spill / g_quitting is in the image. *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
(* CmdRecFacts.v's `cmd_prog_writable` (PROG_PRESENT): those bytes are present, which the core's `awr_byte_cases`
   asks of a footprint write to a program static (YCbq.v:2032-2033). *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* --- the recorder's globals, as the walk needs them ----------------------------------------------------- *)

Lemma rbt_grec_val : VAL RB_GREC = A_G_REC.
Proof. unfold RB_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rbt_spill_val : VAL RB_SPILL = A_REC_SPILL.
Proof. unfold RB_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rbt_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. reflexivity. Qed.
Lemma rbt_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. reflexivity. Qed.

(* --- the walk's environment -------------------------------------------------------------------------- *)

(* what every segment of a recorder walk asks of its environment: the stack pointer of the member's entry,
   the shadow base, the call count the slot came from, and the slot itself *)
Definition rbt_env_ok (E : env) (sp n c : Z) : Prop :=
img_env VAL A_LIM E /\ ew E 2%nat = Z_to_bv 64 sp /\
ew E RB_SB = Z_to_bv 64 SB /\ ew E RB_N = Z_to_bv 64 n /\ ew E RB_C = Z_to_bv 64 c.
(* the slot the inlined record() picked: an entry of g_rec's table, or record.spill *)
Definition rbt_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma rbt_slot_bounds : forall c, rbt_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

(* the two zero-shadow ranges of the record that hold the recorder's globals (AF0m.v:4649, :4650): g_rec's
   table ends the first, record.spill is the second *)
Definition RB_ZSH_REC : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition RB_ZSH_SPILL : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).
Lemma rbt_zsh_rec_in : In RB_ZSH_REC Tfib_zero_shadow.
Proof. unfold RB_ZSH_REC, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.
Lemma rbt_zsh_spill_in : In RB_ZSH_SPILL Tfib_zero_shadow.
Proof. unfold RB_ZSH_SPILL, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma rbt_addressable_rec : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_G_REC <= a -> a + n <= A_G_REC + REC_SIZE ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi. unfold A_G_REC, REC_SIZE in Hlo, Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md RB_ZSH_REC a n HAR rbt_zsh_rec_in
  ltac:(reflexivity) ltac:(reflexivity)
  ltac:(unfold RB_ZSH_REC; cbn [fst snd]; lia) ltac:(unfold RB_ZSH_REC; cbn [fst snd]; lia)).
Qed.

Lemma rbt_addressable_spill : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_REC_SPILL <= a -> a + n <= A_REC_SPILL + SC_SIZE ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi. unfold A_REC_SPILL, SC_SIZE in Hlo, Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md RB_ZSH_SPILL a n HAR rbt_zsh_spill_in
  ltac:(reflexivity) ltac:(reflexivity)
  ltac:(unfold RB_ZSH_SPILL; cbn [fst snd]; lia) ltac:(unfold RB_ZSH_SPILL; cbn [fst snd]; lia)).
Qed.

Lemma rbt_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> rbt_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & _) | ->].
- apply (rbt_addressable_rec ly S W mem md); [exact HAR | unfold OFF_CALLS in H1; lia | exact H2].
- apply (rbt_addressable_spill ly S W mem md); [exact HAR | lia | unfold SC_SIZE, CALL_SIZE; lia].
Qed.

(* A register that holds an address the walk computed (the slot the inlined record() picked) is replaced by the
   atom that names it, so that the inline checks and the stores on it have an atom base. This is CmdPaLib's
   st_ok_pi_pin_reg' with a symbolic value in place of a literal. *)
Lemma rbt_pin_reg : forall E ss ms (r : bv 5) (v : sv),
st_ok_pi SEGS VAL E ss ms -> sv_denot E v = sv_denot E (sr_get (ss_regs ss) r) -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r v HS Hv Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r v) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. exact Hv.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Lemma rbt_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma rbt_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma rbt_facts_ok : forall E sp n c lo hi,
rbt_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> lo <= n <= hi -> 0 <= n <= 16 ->
rbt_slot_ok c ->
facts_ok E (rbt_facts lo hi).
Proof.
intros E sp n c lo hi (HEI & E2 & ESB & EN & EC) Hsp Hsp16 Hn Hn0 Hc.
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)), rbt_grec_val;
      reflexivity).
assert (ES : ew E RB_SPILL = Z_to_bv 64 A_REC_SPILL)
  by (rewrite (img_env_atomP E RB_SPILL HEI ltac:(unfold RB_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), rbt_spill_val;
      reflexivity).
unfold facts_ok, rbt_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
- apply (rbt_afact E 2%nat sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
- apply (rbt_afact E RB_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (rbt_afact E RB_N n); [exact EN | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (rbt_afact E RB_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
  | change (2 ^ 3) with 8; exact Hc8 | lia].
- apply (rbt_afact E RB_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia
  | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
- apply (rbt_afact E RB_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia
  | change (2 ^ 3) with 8; unfold A_REC_SPILL; reflexivity | lia].
Qed.

Lemma rbt_sh_ok : forall ly S W mem md E sp n c,
AR SEGS B ly S W mem md -> rbt_env_ok E sp n c -> rbt_slot_ok c ->
sh_ok SEGS Bxr rbt_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E sp n c HAR HE Hc.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, rbt_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bxr RB_C c CALL_SIZE c 0 CALL_SIZE).
- exact (rbt_slot_addressable ly S W mem md c HAR Hc).
- unfold Bxr. apply rbt_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply rbt_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

End e.
End f.
End d.
