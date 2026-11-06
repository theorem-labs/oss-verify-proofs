(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of sup_worker_env's ASan walk (plugin-hostd/fuzz_command, 0x8c060,
   149 instructions), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed of a walk segment, the region and
   fact tables) over fuzz_command's listing, and the recorder-call template
   (lib/A/Prog/RecBTemplate.v: the atoms, facts and regions of a recorder walk, restated
   here over the zero-shadow table of CmdB): the symbolic states of the segments and their seeds. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_worker_env_c sup_worker_env_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of the walk's segments in the listing (entry 0x8c060 = BASE + 0x5b7c) *)
Definition SWE_FRAME : Z := 64.
Definition SWE_ENTRY : Z := AF_sup_worker_env.
Definition SWE_J : Z := AF_sup_worker_env + 0x84.    (* 0x8c0e4: the two arms of record() meet *)
Definition SWE_X1 : Z := AF_sup_worker_env + 0xc0.   (* 0x8c120: a0 := format (or "(null)"), jal xstrdup *)
Definition SWE_R1 : Z := AF_sup_worker_env + 0xc8.   (* 0x8c128: back from xstrdup(format) *)
Definition SWE_X2 : Z := AF_sup_worker_env + 0x110.  (* 0x8c170 *)
Definition SWE_R2 : Z := AF_sup_worker_env + 0x118.  (* 0x8c178 *)
Definition SWE_X3 : Z := AF_sup_worker_env + 0x15c.  (* 0x8c1bc *)
Definition SWE_R3 : Z := AF_sup_worker_env + 0x164.  (* 0x8c1c4 *)
Definition SWE_R4 : Z := AF_sup_worker_env + 0x1a4.  (* 0x8c204: back from rec_shape_of *)

(* the program's own writable statics as as_prog_static lists them: the kit's recb_PG (RecBLemmas.v) is CmdB's
   TFIB_PROG_STATIC *)
Lemma swe_PG_tfib : recb_PG = TFIB_PROG_STATIC.
Proof. reflexivity. Qed.

(* the atoms above the 32 registers: the shadow base, the call count, the slot, then the saved registers *)
Definition SW_SB : nat := 32.
Definition SW_N : nat := 33.
Definition SW_C : nat := 34.
(* the callee-saved registers the 64-byte frame holds, at sp0 - 8 - 8 j *)
Definition swe_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22].
Definition swe_extra (regs : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) swe_saved.
Definition swe_Bx : sv := SOff SW_SB 0.
Definition swe_SH : list shent := [mkSHE SW_C 0 CALL_SIZE].
Definition swe_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the object atoms of the listing: g_rec, record.spill, the literals "(null)" (.str.47) and "worker_env" (.str.14) *)
Definition SW_GREC : nat := A_OBJ 44.
Definition SW_SPILL : nat := A_OBJ 51.
Definition SW_NULL : nat := A_OBJ 52.
Definition SW_VERB : nat := A_OBJ 70.
Definition swe_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SW_SB, mkAF SB SB 0); (SW_N, mkAF 0 16 0);
         (SW_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (SW_GREC, mkAF A_G_REC A_G_REC 3); (SW_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
(* the frame: [sp + d, sp) of the member's own stack *)
Definition swe_stack (d : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) d 0 d 0 cs.
(* g_rec.ncalls, the only word of g_rec the inlined record() reads and writes *)
Definition swe_ncalls : YP09.region :=
YP09.mkRegion (Some SW_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff SW_N 0))].
(* the slot the call records: g_rec.calls[k] or record.spill *)
Definition swe_slot (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some SW_C) 0 CALL_SIZE 0 CALL_SIZE cs.
Definition swe_rs0 : YP09.smem :=
[swe_stack (- SWE_FRAME) []; got_regionP; bcell_regionP SW_SB; swe_ncalls].

Lemma In_of_existsb_pair : forall (x : Z * Z) l,
existsb (fun r => (fst r =? fst x) && (snd r =? snd x)) l = true -> In x l.
Proof.
intros [a b] l H. apply existsb_exists in H as ([c d] & Hin & E). apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. cbn in E1, E2. subst. exact Hin.
Qed.

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
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma swe_grec_val : VAL SW_GREC = A_G_REC.
Proof. unfold SW_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma swe_spill_val : VAL SW_SPILL = A_REC_SPILL.
Proof. unfold SW_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma swe_null_val : VAL SW_NULL = 0x22480.
Proof. unfold SW_NULL. rewrite (VOBJS 52%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma swe_verb_val : VAL SW_VERB = 0x21ec0.
Proof. unfold SW_VERB. rewrite (VOBJS 70%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma swe_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. reflexivity. Qed.
Lemma swe_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. reflexivity. Qed.

(* what every segment of the walk asks of its environment: the frame's base, the shadow base, the call count the
   slot came from, and the slot itself *)
Definition swe_env_ok (E : env) (sp n c : Z) : Prop :=
img_env VAL A_LIM E /\ ew E 2%nat = Z_to_bv 64 sp /\
ew E SW_SB = Z_to_bv 64 SB /\ ew E SW_N = Z_to_bv 64 n /\ ew E SW_C = Z_to_bv 64 c.
Definition swe_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma swe_slot_of_ok : forall n, 0 <= n <= 16 -> swe_slot_ok (swe_slot_of n).
Proof.
intros n Hn. unfold swe_slot_of, swe_slot_ok. destruct (Z.ltb_spec n 16) as [Hl|Hl]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
rewrite Z.add_mod, Z.mul_mod by lia. change (56 mod 8) with 0. rewrite Z.mul_0_l. reflexivity.
Qed.

Lemma swe_slot_bounds : forall c, swe_slot_ok c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

(* the record's zero-shadow ranges that hold g_rec and record.spill (CmdB's Tfib_zero_shadow) *)
Lemma swe_zsh_grec : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow.
Proof. apply In_of_existsb_pair. vm_compute. reflexivity. Qed.
Lemma swe_zsh_spill : In (0x5e3be0, 0x5e3c18 - 0x5e3be0) Tfib_zero_shadow.
Proof. apply In_of_existsb_pair. vm_compute. reflexivity. Qed.

Lemma swe_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> swe_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(H1 & H2 & H3) | ->].
- exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ c CALL_SIZE HAR swe_zsh_grec
    ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold A_G_REC, OFF_CALLS in *; cbn [fst]; lia)
    ltac:(unfold A_G_REC, REC_SIZE in *; cbn [fst snd]; lia)).
- exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ A_REC_SPILL CALL_SIZE HAR swe_zsh_spill
    ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold A_REC_SPILL; cbn [fst]; lia)
    ltac:(unfold A_REC_SPILL, CALL_SIZE; cbn [fst snd]; lia)).
Qed.

Lemma swe_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma swe_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma swe_facts_ok : forall E sp n c,
swe_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> swe_slot_ok c ->
facts_ok E swe_facts.
Proof.
intros E sp n c (HEI & E2 & ESB & EN & EC) Hsp Hsp16 Hn Hc.
destruct (swe_slot_bounds c Hc) as [Hcb Hc8].
assert (EG : ew E SW_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E SW_GREC HEI ltac:(unfold SW_GREC, A_OBJ, A_TEXT, A_LIM; lia)), swe_grec_val;
      reflexivity).
assert (ES : ew E SW_SPILL = Z_to_bv 64 A_REC_SPILL)
  by (rewrite (img_env_atomP E SW_SPILL HEI ltac:(unfold SW_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), swe_spill_val;
      reflexivity).
unfold facts_ok, swe_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
- apply (swe_afact E 2%nat sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
- apply (swe_afact E SW_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (swe_afact E SW_N n); [exact EN | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (swe_afact E SW_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
  | change (2 ^ 3) with 8; exact Hc8 | lia].
- apply (swe_afact E SW_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia
  | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
- apply (swe_afact E SW_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia
  | change (2 ^ 3) with 8; unfold A_REC_SPILL; reflexivity | lia].
Qed.

Lemma swe_sh_ok : forall ly S W mem md E sp n c,
AR SEGS B ly S W mem md -> swe_env_ok E sp n c -> swe_slot_ok c ->
sh_ok SEGS swe_Bx swe_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E sp n c HAR HE Hc.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (swe_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, swe_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E swe_Bx SW_C c CALL_SIZE c 0 CALL_SIZE).
- exact (swe_slot_addressable ly S W mem md c HAR Hc).
- unfold swe_Bx. apply swe_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply swe_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

Lemma swe_entry_seed : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
swe_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> swe_slot_ok c ->
(forall a, sp - SWE_FRAME <= a < sp -> apresent (w_H W1) mem1 a) ->
aval_mem (rdW W1 mem1) (A_G_REC + OFF_NCALLS) 4 n ->
regs_ok E sr_atoms regs1 ->
st_ok_pi SEGS VAL E (mkSS SWE_ENTRY sr_atoms swe_rs0 None swe_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SWE_ENTRY)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS swe_Bx swe_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n c HAR HE Hsp Hsp16 Hn Hc Hpres HNC HREG.
pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
assert (EG : ew E SW_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E SW_GREC HEI ltac:(unfold SW_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      swe_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0)
  by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8)
  by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| exact (swe_sh_ok ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- unfold swe_rs0, swe_stack, got_regionP, bcell_regionP, swe_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat sp E2) by lia. split; [unfold SWE_FRAME; lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite swe_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 swe_Bx SHADOW_OFF);
    [cbn [sv_denot swe_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite swe_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB SW_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff SW_N 0) n);
    [cbn [sv_denot]; rewrite EN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite swe_pow4; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W1) mem1 (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold swe_rs0, swe_stack, got_regionP, bcell_regionP, swe_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB SW_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat sp E2) by lia.
  rewrite EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SWE_FRAME, A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- exact (swe_facts_ok E sp n c HE Hsp Hsp16 Hn Hc).
Qed.


End e.
End f.
End d.
