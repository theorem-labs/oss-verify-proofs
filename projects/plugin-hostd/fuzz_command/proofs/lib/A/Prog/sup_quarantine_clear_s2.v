(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states and seeds of sup_quarantine_clear's ASan walk
   (plugin-hostd/fuzz_command), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed, the region and fact tables
   of cgif_close's walk) and lib/A/Prog/RecBTemplate.v (the recorder template: the atoms, regions and
   facts of a recorder walk) over fuzz_command's listing. *)

(* sup_quarantine_clear (recorder.c:411-417, entry BASE + AF_sup_quarantine_clear = 0x8b844, 91 instructions):
   the symbolic states its walk starts from. Atoms above the 32 registers: 32 the shadow base, 33 the call count
   g_rec.ncalls had at the entry, 34 the slot record() fills (g_rec.calls[n], or record.spill when n = 16), 35..40
   the entry values of ra, s0, s1, s2, s3, s4, which the 48-byte frame holds. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
(* recb_PG, the program's writable statics as as_prog_static lists them (base, length) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk's points in the listing *)
Definition SQ_E : Z := AF_sup_quarantine_clear.
Definition SQ_RETR : Z := AF_sup_quarantine_clear + 0x54.  (* after the call of rec_calls_free (0x8b898) *)
Definition SQ_JOIN : Z := AF_sup_quarantine_clear + 0x74.  (* the two arms of record() meet (0x8b8b8) *)
Definition SQ_RETX : Z := AF_sup_quarantine_clear + 0xb8.  (* after the call of xstrdup (0x8b8fc) *)
Definition SQ_RETS : Z := AF_sup_quarantine_clear + 0xfc.  (* after the call of rec_shape_of (0x8b940) *)
Definition SQ_FRAME : Z := 48.
(* the function the call records (REC_QUARANTINE_CLEAR, the `li a0,11` before the store to c->fn) *)
Definition SQ_FN : Z := 11.

(* atoms *)
Definition SQ_SB : nat := 32.
Definition SQ_N : nat := 33.
Definition SQ_C : nat := 34.
Definition sqc_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition sqc_extra (regs0 : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs0 (Z_to_bv 5 r)) sqc_saved.
Definition sqc_Bx : sv := SOff SQ_SB 0.
Definition sqc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sqc_SH : list shent := [mkSHE SQ_C 0 CALL_SIZE].
(* the listing's object atoms: g_rec, record.spill *)
Definition SQ_GREC : nat := A_OBJ 44.
Definition SQ_SPILL : nat := A_OBJ 51.
Definition sqc_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SQ_SB, mkAF SB SB 0); (SQ_N, mkAF 0 16 0);
         (SQ_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (SQ_GREC, mkAF A_G_REC A_G_REC 3); (SQ_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].

(* regions: the frame at the entry (written by the prologue), g_rec.ncalls, the frame after the prologue (it holds
   the entry's ra, s0..s4), and the slot *)
Definition sqc_stack0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SQ_FRAME) 0 (- SQ_FRAME) 0 [].
Definition sqc_ncalls : YP09.region :=
YP09.mkRegion (Some SQ_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff SQ_N 0))].
Definition sqc_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 SQ_FRAME 0 0
  (map (fun j => YP09.mkChunk (40 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 6)).
(* the slot: its 56 bytes, of which the walk writes fn, nargs and args[0] (the first 16) *)
Definition sqc_slotR (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some SQ_C) 0 CALL_SIZE 0 16 cs.

Definition sqc_ssA : sstate :=
mkSS SQ_E sr_atoms [sqc_stack0; got_regionP; bcell_regionP SQ_SB; sqc_ncalls] None sqc_facts.
(* at the join: s0 the slot, s3 the shadow base *)
Definition sqc_regsC : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 8 (SOff SQ_C 0)) 19 (SOff SQ_SB 0).
Definition sqc_ssC (pc : Z) : sstate := mkSS pc sqc_regsC [sqc_frame; sqc_slotR []] None sqc_facts.

(* the slot record() picked: an entry of g_rec's table, or record.spill *)
Definition sqc_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.
(* the zero-shadow ranges of the record that hold g_rec and record.spill (AF0m.v:4649, :4650) *)
Definition SQ_ZSH_REC : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition SQ_ZSH_SPILL : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).

Lemma sqc_slot_bounds : forall c, sqc_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL).
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
[split; [lia | split; [exact H3 | left; lia]] | split; [lia | split; [reflexivity | right; reflexivity]]].
Qed.

Lemma sqc_in_PG_slot : forall c a, sqc_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. destruct (sqc_slot_bounds c Hc) as (Hb & _ & [Hh | ->]).
- apply recb_grec_in. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- apply recb_spill_in. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the 48-byte frame holds the entry's ra, s0, s1, s2, s3, s4 at sp1 + 40, 32, 24, 16, 8, 0 *)
Definition sqc_frame_at (m : word -> option byte) (sp1 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error sqc_saved j = Some r ->
val_mem SEGS m (sp1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* every atom of the walk's environment: the registers of the current state, then the extra atoms *)
Definition sqc_E (regs1 regs0 : bvmap 5 word) (n c : Z) : env := Eimg (Ereg regs1 (sqc_extra regs0 n c)).

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma sqc_grec_val : VAL SQ_GREC = A_G_REC.
Proof. unfold SQ_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma sqc_spill_val : VAL SQ_SPILL = A_REC_SPILL.
Proof. unfold SQ_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma sqc_zsh_rec_in : In SQ_ZSH_REC Tfib_zero_shadow.
Proof. unfold SQ_ZSH_REC, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma sqc_zsh_spill_in : In SQ_ZSH_SPILL Tfib_zero_shadow.
Proof. unfold SQ_ZSH_SPILL, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma sqc_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sqc_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & _) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SQ_ZSH_REC c CALL_SIZE HAR sqc_zsh_rec_in);
  unfold SQ_ZSH_REC; cbn [fst snd]; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; first [reflexivity | lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SQ_ZSH_SPILL A_REC_SPILL CALL_SIZE HAR sqc_zsh_spill_in);
  unfold SQ_ZSH_SPILL; cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; first [reflexivity | lia].
Qed.

Lemma sqc_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma sqc_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma sqc_E_reg : forall regs1 regs0 n c k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (sqc_E regs1 regs0 n c) k = getr regs1 r.
Proof.
intros regs1 regs0 n c k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold sqc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma sqc_E_extra : forall regs1 regs0 n c j, (j < 9)%nat ->
ew (sqc_E regs1 regs0 n c) (32 + j) = nth j (sqc_extra regs0 n c) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 n c j Hj. unfold sqc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma sqc_E_extra_at : forall regs1 regs0 n c k, (32 <= k < 41)%nat ->
ew (sqc_E regs1 regs0 n c) k = nth (k - 32) (sqc_extra regs0 n c) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 n c k Hk. replace k with (32 + (k - 32))%nat at 1 by lia. apply sqc_E_extra. lia.
Qed.

Lemma sqc_E_img : forall regs1 regs0 n c, img_env VAL A_LIM (sqc_E regs1 regs0 n c).
Proof. intros. unfold sqc_E. apply Eimg_env. Qed.

Lemma sqc_E_grec : forall regs1 regs0 n c, ew (sqc_E regs1 regs0 n c) SQ_GREC = Z_to_bv 64 A_G_REC.
Proof.
intros. rewrite (img_env_atomP (sqc_E regs1 regs0 n c) SQ_GREC (sqc_E_img regs1 regs0 n c)
  ltac:(unfold SQ_GREC, A_OBJ, A_TEXT, A_LIM; lia)), sqc_grec_val. reflexivity.
Qed.

Lemma sqc_E_spill : forall regs1 regs0 n c, ew (sqc_E regs1 regs0 n c) SQ_SPILL = Z_to_bv 64 A_REC_SPILL.
Proof.
intros. rewrite (img_env_atomP (sqc_E regs1 regs0 n c) SQ_SPILL (sqc_E_img regs1 regs0 n c)
  ltac:(unfold SQ_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), sqc_spill_val. reflexivity.
Qed.

Lemma sqc_facts_ok : forall regs1 regs0 n c,
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 -> bv_unsigned (getr regs1 2) mod 16 = 0 -> 0 <= n <= 16 -> sqc_slot_ok c ->
facts_ok (sqc_E regs1 regs0 n c) sqc_facts.
Proof.
intros regs1 regs0 n c Hsp Hsp16 Hn Hc.
destruct (sqc_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (E := sqc_E regs1 regs0 n c).
assert (E2 : ew E 2 = Z_to_bv 64 (bv_unsigned (getr regs1 2))) by (subst E; rewrite (sqc_E_reg _ _ _ _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (ESB : ew E SQ_SB = Z_to_bv 64 SB) by (subst E; exact (sqc_E_extra regs1 regs0 n c 0 ltac:(lia))).
assert (EN : ew E SQ_N = Z_to_bv 64 n) by (subst E; exact (sqc_E_extra regs1 regs0 n c 1 ltac:(lia))).
assert (EC : ew E SQ_C = Z_to_bv 64 c) by (subst E; exact (sqc_E_extra regs1 regs0 n c 2 ltac:(lia))).
pose proof (sqc_E_grec regs1 regs0 n c) as EG. pose proof (sqc_E_spill regs1 regs0 n c) as ES. fold E in EG, ES.
unfold facts_ok, sqc_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
- apply (sqc_afact E 2%nat (bv_unsigned (getr regs1 2))); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
- apply (sqc_afact E SQ_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (sqc_afact E SQ_N n); [exact EN | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (sqc_afact E SQ_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
  | change (2 ^ 3) with 8; exact Hc8 | lia].
- apply (sqc_afact E SQ_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia
  | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
- apply (sqc_afact E SQ_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia
  | change (2 ^ 3) with 8; unfold A_REC_SPILL; reflexivity | lia].
Qed.

Lemma sqc_sh_ok : forall ly S W mem md regs1 regs0 n c,
AR SEGS B ly S W mem md -> sqc_slot_ok c ->
sh_ok SEGS sqc_Bx sqc_SH (sqc_E regs1 regs0 n c) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 regs0 n c HAR Hc.
destruct (sqc_slot_bounds c Hc) as (Hcb & Hc8 & _).
assert (ESB : ew (sqc_E regs1 regs0 n c) SQ_SB = Z_to_bv 64 SB) by exact (sqc_E_extra regs1 regs0 n c 0 ltac:(lia)).
assert (EC : ew (sqc_E regs1 regs0 n c) SQ_C = Z_to_bv 64 c) by exact (sqc_E_extra regs1 regs0 n c 2 ltac:(lia)).
unfold sh_ok, sqc_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem (sqc_E regs1 regs0 n c) sqc_Bx SQ_C c CALL_SIZE c 0 CALL_SIZE).
- exact (sqc_slot_addressable ly S W mem md c HAR Hc).
- unfold sqc_Bx. apply sqc_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply sqc_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the seed of a walk segment after the prologue: the frame (its saved registers) and the slot *)
Lemma sqc_seed : forall pc sregs cs W1 (regs1 regs0 : bvmap 5 word) mem1 ly1 S1 md1 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 - SQ_FRAME -> bv_unsigned (getr regs1 2) mod 16 = 0 ->
0 <= n <= 16 -> sqc_slot_ok c ->
regs_ok (sqc_E regs1 regs0 n c) sregs regs1 ->
sqc_frame_at (mrestrict (w_H W1) mem1) (bv_unsigned (getr regs1 2)) regs0 ->
regions_wf [sqc_frame; sqc_slotR cs] = true ->
Forall (YP09.chunk_ok SEGS (sqc_E regs1 regs0 n c) (mrestrict (w_H W1) mem1) c) cs ->
st_ok_pi SEGS VAL (sqc_E regs1 regs0 n c) (mkSS pc sregs [sqc_frame; sqc_slotR cs] None sqc_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS sqc_Bx sqc_SH (sqc_E regs1 regs0 n c) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs cs W1 regs1 regs0 mem1 ly1 S1 md1 n c HAR Hsp Hsp16 Hn Hc HREG HFR Hwf HCS.
destruct (sqc_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (sp1 := bv_unsigned (getr regs1 2)) in *.
set (E := sqc_E regs1 regs0 n c) in *.
assert (E2 : bv_unsigned (ew E 2) = sp1) by (subst E sp1; rewrite (sqc_E_reg _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (EC : ew E SQ_C = Z_to_bv 64 c) by (subst E; exact (sqc_E_extra regs1 regs0 n c 2 ltac:(lia))).
assert (UC : bv_unsigned (ew E SQ_C) = c) by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [| exact (sqc_sh_ok ly1 S1 W1 mem1 md1 regs1 regs0 n c HAR Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- exact Hwf.
- unfold sqc_frame, sqc_slotR. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. unfold SQ_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
    let j := eval compute in (k - 35)%nat in let r := eval compute in (nth j sqc_saved 0) in
    apply (chunk_ok_val SEGS E _ sp1 off 8 (SOff k 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r; subst E;
      rewrite (sqc_E_extra_at regs1 regs0 n c k ltac:(lia)); cbn [Nat.sub nth sqc_extra sqc_saved map app];
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; cbn; lia
    | cbn; lia
    | replace (sp1 + off) with (sp1 + 40 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
  + rewrite UC. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, CALL_SIZE in *; lia|].
    split; [| exact HCS].
    intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1 _ HAR). apply (sqc_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents. unfold sqc_frame, sqc_slotR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SQ_FRAME, CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- apply (sqc_facts_ok regs1 regs0 n c); [unfold SQ_FRAME in Hsp; fold sp1; lia | exact Hsp16 | exact Hn | exact Hc].
Qed.

(* the seed at the entry: the frame the prologue writes, the two words of the shadow base, and g_rec.ncalls *)
Lemma sqc_seed_entry : forall W (regs : bvmap 5 word) mem ly S md n c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - SQ_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 -> sqc_slot_ok c ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (sqc_E regs regs n c) sqc_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SQ_E)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md n c HAR Hsp Hsp16 Hpres Hn Hc HNC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := sqc_E regs regs n c).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (sqc_E_reg _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (ESB : ew E SQ_SB = Z_to_bv 64 SB) by (subst E; exact (sqc_E_extra regs regs n c 0 ltac:(lia))).
assert (EN : ew E SQ_N = Z_to_bv 64 n) by (subst E; exact (sqc_E_extra regs regs n c 1 ltac:(lia))).
assert (EG : ew E SQ_GREC = Z_to_bv 64 A_G_REC) by (subst E; apply sqc_E_grec).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold sqc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold sqc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold sqc_ssA. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. unfold sqc_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sqc_stack0, got_regionP, bcell_regionP, sqc_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. unfold SQ_FRAME in *. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 sqc_Bx SB);
    [cbn [sv_denot sqc_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB SQ_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply recb_grec_in.
      unfold OFF_NCALLS, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff SQ_N 0) n);
    [cbn [sv_denot]; rewrite EN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | zside | zside | exact HNC].
- apply pairwise_disjoint_of_extents.
  unfold sqc_stack0, got_regionP, bcell_regionP, sqc_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB SQ_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SQ_FRAME, A_G_REC, OFF_NCALLS in *.
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
  let v0 := eval vm_compute in (nth 0 cmd_objs 0) in change (nth 0 cmd_objs 0) with v0.
  let v12 := eval vm_compute in (nth 12 cmd_objs 0) in change (nth 12 cmd_objs 0) with v12.
  repeat split; lia.
- exact (sqc_facts_ok regs regs n c ltac:(unfold spZ in Hsp; lia) Hsp16 Hn Hc).
Qed.

End e.
End f.
End d.
