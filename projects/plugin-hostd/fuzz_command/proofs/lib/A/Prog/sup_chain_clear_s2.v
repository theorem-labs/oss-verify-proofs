(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second half of the walk of sup_chain_clear on plugin-hostd/fuzz_command.asan
   (from the join of record()'s two arms to the tail jump into answer), in the walk style of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a run, a call through cl_callS, the return through
   jafter_call_keep_pi); the seed tables after lib/A/Prog/RecBTemplate.v,
   itself after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v. *)

(* sup_chain_clear (recorder.c:481-487, entry BASE + AF_sup_chain_clear = 0x8c558, 64 instructions):
   record(REC_CHAIN_CLEAR) inlined, arg_i(c, id), rec_shape_of("chain_clear", 11), tail jump answer(c, shape, 1).
   This file walks 0x8c5c4 .. 0x8c630: the two inline checks on the slot c (the shadow byte at
   (c >> 3) + 0x7fff8000 and at ((c + 4) >> 3) + 0x7fff8000; c lies in g_rec or record.spill, which the allocator
   record marks usable, so the error path is not reached), the stores c->fn := 18 and c->nargs := 0, the calls of
   arg_i and rec_shape_of, the epilogue and the tail jump. lib/A/Prog/sup_chain_clear.v walks the entry and
   record()'s two arms to 0x8c5c4 and applies `scc_join`.

   Statement passes 4, 4b and 5: the post is apost_baseF and the callees' contracts are
   taken at every FP state. arg_i reaches the snprintf wrapper, so it is called through PaFx.v's cl_callS_wideF and
   returns at some fx1 with fxrel fx fx1; the walk after it runs at fx1 (PaFx.v's `st_ok_restrict_xfx` takes the
   call site's symbolic state to fx1, the runs use paj_run at fx1), calls rec_shape_of and answer at fx1, and closes
   with apost_baseF_intro at the fx2 answer returns. The program's statics are RecBLemmas.v's recb_PG.

   Named Section hypotheses beyond the statement's callee contracts (the recorder walks' shared names and forms;
   each becomes a lemma of lib/A/Prog/CmdRecFacts.v or of the core's kit): cmd_prog_img, cmd_prog_writable,
   SIGP (CmdObj.v's cmd_sig_prog), cmd_ro_ok_of_aro, RRO, RELRO_IMG, cmd_ro_prog_apart, CMD_RO_IN. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_i_c rec_shape_of_c answer_c sup_chain_clear_c xstrdup_c hand_back_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain sup_chain_clear_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offsets of the walk: the join of record()'s two arms (0x8c5c4) and the two return points *)
Definition SCC_JOIN : Z := AF_sup_chain_clear + 0x6c.
Definition SCC_RA_ARGI : Z := AF_sup_chain_clear + 0xa8.
Definition SCC_RA_RSO : Z := AF_sup_chain_clear + 0xb8.
(* the footprint of the contract (sup_chain_clear_c.v:86) *)
Definition scc_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the symbolic state at the join: register atoms; s2 (atom 18) holds the shadow base, s0 (atom 8) the slot; the
   atoms 32 .. 35 are the entry values of ra, s0, s1, s2 that the frame holds *)
Definition scc_Bx : sv := SOff 18 0.
Definition scc_SH : list shent := [mkSHE 8 0 CALL_SIZE].
Definition scc_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (18%nat, mkAF SB SB 0)] [] [].
Definition scc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition scc_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
 [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
  YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition scc_slot : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
Definition ss_join : sstate := mkSS SCC_JOIN sr_atoms [scc_frame; scc_slot] None scc_facts.
Definition scc_saved (regs : bvmap 5 word) : list word := [getr regs 1; getr regs 8; getr regs 9; getr regs 18].
(* the verb the call records, "chain_clear": the literal .str.18 at 0x21f40 without its terminator *)
Definition scc_verb : list byte := bstr "chain_clear"%string.
Lemma scc_verb_ro : scc_verb ++ [Z_to_bv 8 0] = RO_lit_21f40.
Proof. vm_compute. reflexivity. Qed.
Lemma scc_verb_len : length scc_verb = 11%nat.
Proof. reflexivity. Qed.
Lemma scc_shape_eq : daemon_shape "chain_clear"%string = shape_of scc_verb.
Proof. reflexivity. Qed.
Lemma scc_fits : fits (shape_of scc_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma scc_abytes_prefix : forall rd a (l1 l2 : list byte), abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
Qed.
(* a member of a filtered list is a member of the list (the filter answer_c.v's footprint uses) *)
Lemma scc_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
repeat match type of H with context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
repeat match type of H with context [if ?b then _ else _] => destruct b end;
first [ destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H) ].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition EJ (regsc regs : bvmap 5 word) : env := Eimg (Ereg regsc (scc_saved regs)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses, with cgif's names (cgif's names) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
(* the program's statics (the recorder walks' shared names, RecBTemplate.v forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the callees' statement addresses (CmdObj.v's cmd_sig_prog, the walk hypothesis SIGP) *)
Hypothesis SIGP : cmd_sig_prog.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma scc_sig : SIG CS_rec_calls_free = BASE + AF_rec_calls_free /\ SIG CS_arg_i = BASE + AF_arg_i /\
  SIG CS_rec_shape_of = BASE + AF_rec_shape_of /\ SIG CS_answer = BASE + AF_answer.
Proof.
rewrite !SIGP by (vm_compute; tauto). vm_compute. repeat split; reflexivity.
Qed.

Lemma scc_in_PG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
Exists (in_zr a) recb_PG.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* a write of the walk to g_rec or record.spill is one the footprint names: the core's program-static disjunct of
   awr_byte (YCbq.v:497), with the statics from HB's ts_prog *)
Lemma scc_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (scc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) recb_PG) by exact (scc_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma scc_val_mem : forall (W : world SEGS) mem a v,
rdword (rdW W mem) a = Some v -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v.
Proof. intros W mem a v H. exact (val_mem_of_rdword SEGS _ _ _ _ H). Qed.

(* the slot's bytes lie in g_rec's call table or in record.spill *)
Definition scc_slot_ok (c : Z) : Prop :=
A_G_REC + OFF_CALLS <= c /\ c mod 8 = 0 /\ (c + CALL_SIZE <= A_G_REC + REC_SIZE \/ c = A_REC_SPILL).

Lemma scc_slot_in : forall c a, scc_slot_ok c -> c <= a < c + CALL_SIZE ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros c a (H1 & _ & [H3 | ->]) Ha; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

(* a range of the record's zero-shadow list, found by computation *)
Lemma scc_in_zsh : forall r, existsb (fun r' => (fst r' =? fst r) && (snd r' =? snd r)) Tfib_zero_shadow = true ->
In r Tfib_zero_shadow.
Proof.
intros [a n] H. apply existsb_exists in H as ([a' n'] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. exact Hin.
Qed.

(* the slot's 56 bytes are marked usable: g_rec's and record.spill's ranges of the record's zero-shadow list *)
Lemma scc_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> scc_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR (Hc1 & _ & [Hc3 | ->]).
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) c CALL_SIZE HAR);
  [apply scc_in_zsh; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst]; unfold A_G_REC, OFF_CALLS in *; lia | cbn [fst snd]; unfold A_G_REC, REC_SIZE, CALL_SIZE in *; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL CALL_SIZE HAR);
  [apply scc_in_zsh; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst]; unfold A_REC_SPILL; lia | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia].
Qed.

Lemma scc_join_seed : forall ly S (W : world SEGS) mem md (regsc regs : bvmap 5 word) c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regsc <= 2 ^ 47 - 32 -> spZ regsc mod 16 = 0 ->
getr regsc 8 = w64 c -> scc_slot_ok c ->
getr regsc 18 = w64 SB ->
rdword (rdW W mem) (spZ regsc) = Some (bv_unsigned (getr regs 18)) ->
rdword (rdW W mem) (spZ regsc + 8) = Some (bv_unsigned (getr regs 9)) ->
rdword (rdW W mem) (spZ regsc + 16) = Some (bv_unsigned (getr regs 8)) ->
rdword (rdW W mem) (spZ regsc + 24) = Some (bv_unsigned (getr regs 1)) ->
st_ok_pi SEGS VAL (EJ regsc regs) ss_join
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + SCC_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scc_Bx scc_SH (EJ regsc regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regsc regs c HAR Hsp Hsp16 H8 Hc H18 F0 F8 F16 F24.
pose proof Hc as (Hc1 & Hc8 & Hc3).
assert (Hcb : A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE).
{ destruct Hc3 as [H | ->]; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia. }
set (E := EJ regsc regs).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (scc_saved regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 8) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 9) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 18) by exact (EX 3%nat ltac:(lia)).
assert (E2 : bv_unsigned (ew E 2) = spZ regsc) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EL 18%nat 18%bv eq_refl); exact H18).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (Hcz : 0 <= c < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, EJ. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold scc_frame, scc_slot. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (spZ regsc) 0 8 (SOff 35 0) (bv_unsigned (getr regs 18)));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
           change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | rewrite Z.add_0_r; exact (scc_val_mem W mem _ _ F0)].
      -- apply (chunk_ok_val SEGS E _ (spZ regsc) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
           change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact (scc_val_mem W mem _ _ F8)].
      -- apply (chunk_ok_val SEGS E _ (spZ regsc) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
           change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact (scc_val_mem W mem _ _ F16)].
      -- apply (chunk_ok_val SEGS E _ (spZ regsc) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
           change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact (scc_val_mem W mem _ _ F24)].
    * rewrite (VB 8%nat c E8 Hcz).
      assert (Hc64 : c + 8 <= 2 ^ 64) by (unfold A_REC_SPILL in Hcb; lia).
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR). apply scc_in_PG.
      apply (scc_slot_in c); [exact Hc | unfold CALL_SIZE; lia].
  + apply pairwise_disjoint_of_extents.
    unfold scc_frame, scc_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 8%nat c E8 Hcz). cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *. repeat split; lia.
  + unfold scc_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E18. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, scc_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E scc_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
  + exact (scc_slot_addressable ly S W mem md c HAR Hc).
  + unfold scc_Bx, U. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia).
    reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* --- the callees, and the per-binary facts the walk carries (the recorder walks' shared names and forms) --------- *)

Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
(* cmd_ro_ok names only bytes no runtime entry owns, so arodata_okP gives it back at any AR state (the statements'
   pending lemma); arodata_okP travels with arodata_ok_journalP, whose two facts are RRO and RELRO_IMG, and whose
   footprint premise uses cmd_ro_prog_apart *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the image's literals are read-only (a premise the statements carried until a read-only string argument came to
   carry the record's checks, CmdRo.v:434): the verb "chain_clear" handed to rec_shape_of through astr_argA's read-only arm *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).

(* arg_i's footprint for the slot c with nargs = 0 (arg_i_c.v:89-91) *)
Definition scc_FPa (c : Z) : list (Z * Z) :=
if 0 <? REC_ARGS_MAX
then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]
else [].
(* what the walk keeps of arg_i's post (arg_i_c.v:94-103, m = 0) *)
Definition scc_Karg (lyc : alayout) (Sc : astate) (c id : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 mo_le MT Sc S' (XM_ARG_I MT id) /\ exists p,
 4096 <= p < 2 ^ 64 /\ Permutation (ablocks B ly' S') ((p, Z.of_nat (length (dec id)) + 1) :: ablocks B lyc Sc) /\
 Forall (fun qk => iv_apart p (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
 aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 1 /\ aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * 0) 8 p /\
 astr_atR (rdW W' mem') p (dec id).

(* what the walk keeps of rec_shape_of's post (rec_shape_of_c.v:100-105, v = "chain_clear") *)
Definition scc_Krso (lyc : alayout) (Sc : astate) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 (exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
  forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of scc_verb))) /\
 Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc.

(* the contract's post (sup_chain_clear_c.v:91-110) *)
Definition scc_Q (ly : alayout) (S : astate) (id : Z) (R : rstate) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_chain_clear_m R id = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN_CLEAR R id /\
 mo_le MT S S' (XM_SUP_CHAIN_CLEAR MT R id).

(* --- the recorder's statics across a callee's journal ---------------------------------------------------------- *)

(* g_rec's and record.spill's bytes are none of the runtime's statics (HB's ts_owned) and not the errno cell *)
Lemma scc_rec_unowned : forall a, in_recA a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold in_recA in Ha.
split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb1 : forallb (fun r => (0x5e3b00 <=? fst r) || (fst r + snd r <=? 0x5e3740)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  assert (Hb2 : forallb (fun r => (0x5e3c18 <=? fst r) || (fst r + snd r <=? 0x5e3be0)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb1 _ Hin) as Hq1. pose proof (proj1 (forallb_forall _ _) Hb2 _ Hin) as Hq2.
  cbn beta in Hq1, Hq2. cbn [fst snd] in Hq1, Hq2.
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha.
  apply Bool.orb_true_iff in Hq1 as [Hq1 | Hq1]; apply Z.leb_le in Hq1;
  apply Bool.orb_true_iff in Hq2 as [Hq2 | Hq2]; apply Z.leb_le in Hq2; lia.
- unfold TFIB_ERRNO, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
Qed.

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was (the journal's image clause) *)
Lemma scc_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 -> in_recA a -> ~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (scc_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply cmd_prog_img. apply scc_in_PG. exact Ha.
Qed.

(* a live block is apart from g_rec and record.spill (no block byte is an image byte) *)
Lemma scc_blk_apart : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & _ & _ & _ & _ & Hnr).
assert (Hn0 : 0 <= n) by lia.
pose proof (req_size_pos n Hn0) as [R1 R2].
assert (HI : forall a, p <= a < p + req_size n -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin); lia).
unfold iv_apart. split.
- destruct (Z.le_gt_cases (p + n) A_G_REC) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_G_REC)); [lia|]. apply cmd_prog_img. apply scc_in_PG. left. unfold REC_SIZE in *. lia.
- destruct (Z.le_gt_cases (p + n) A_REC_SPILL) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_REC_SPILL + SC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_REC_SPILL)); [lia|]. apply cmd_prog_img. apply scc_in_PG. right. unfold SC_SIZE in *. lia.
Qed.

(* a block live across a callee whose footprint lies in g_rec / record.spill keeps its bytes *)
Lemma scc_blk_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k p n i,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
AR SEGS B lyc Sc Wc memc mdc ->
(forall a, inFP FP1 a -> in_recA a) ->
In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
rdW W' mem' (p + i) = rdW Wc memc (p + i).
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k p n i HJ HAR HFP Hin Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2].
apply (F2 p n i); [exact Hin | exact Hin' | lia |].
intros Hf. apply HFP in Hf.
apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + i) HAR Hin); [lia|].
apply cmd_prog_img. apply scc_in_PG. exact Hf.
Qed.

Lemma scc_FPa_in : forall c a, inFP (scc_FPa c) a -> c + 4 <= a < c + 16.
Proof.
intros c a (r & Hr & Ha). unfold scc_FPa in Hr. change (0 <? REC_ARGS_MAX) with true in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha; lia.
Qed.

(* no read-only byte is in the contract's footprint (arodata_ok_journalP's premise) *)
Lemma scc_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (scc_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro (r & Hr & Ha).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply scc_in_PG. left. exact Ha.
- apply Hnp. apply scc_in_PG. right. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HOS _ Hin) Ha Himg).
Qed.

(* the verb "chain_clear" (0x21f40) as rec_shape_of's string argument: astr_argA's read-only arm, with the
   record's checks decided on the concrete lists *)
Lemma scc_verb_argA : forall ly S rd O, abytes_atR rd 0x21f40 RO_lit_21f40 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O 0x21f40 (Some scc_verb).
Proof.
intros ly S rd O HL. unfold astr_argA. cbv zeta. rewrite scc_verb_len. change (Z.of_nat 11) with 11.
split; [lia|]. split.
{ split; [rewrite scc_verb_ro; exact HL|].
  assert (E : scc_verb = map (Z_to_bv 8) [99; 104; 97; 105; 110; 95; 99; 108; 101; 97; 114]) by (vm_compute; reflexivity).
  rewrite E. cbn [map In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. }
split; [unfold LMAX; lia|]. right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
- intros i Hi. split; [|split].
  + clear - CMD_RO_IN Hi. unfold cmd_ro_in in CMD_RO_IN.
    repeat match type of CMD_RO_IN with
    | (forall i, 0 <= i < 12 -> _ (0x21f40 + i)) /\ _ => exact (proj1 CMD_RO_IN i Hi)
    | _ /\ _ => apply proj2 in CMD_RO_IN
    end.
  + rewrite (ts_owned B HB). intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz.
    cbn [fst snd] in Hz.
    assert (Hb : forallb (fun r => (0x21f4c <=? fst r) || (fst r + snd r <=? 0x21f40)) Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Hq. cbn beta in Hq. cbn [fst snd] in Hq.
    apply Bool.orb_true_iff in Hq as [Hq | Hq]; apply Z.leb_le in Hq; lia.
  + rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
- assert (Hb : existsb (Z.eqb (0x21f40 + 11)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (e & He & Heq). apply Z.eqb_eq in Heq. rewrite Heq. exact He.
Qed.

(* astr_argA reads its reader only through the string's bytes *)
Lemma scc_argA_rd : forall ly S rd rd' O p x, astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S rd rd' O p x H Hk. unfold astr_argA in *. cbv zeta in *.
destruct H as (H0 & [Hb Hnz] & Hl & Harm). split; [exact H0|]. split; [|split; [exact Hl | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

(* the bytes of such a string lie below the stack (a heap block or the image) *)
Lemma scc_argA_bound : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md -> 0 <= p ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md rd O p x HAR Hp H i Hi. unfold astr_argA in H. cbv zeta in H.
pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [((pb & kb & Hin & Hlo & Hhi) & _) | (Hro & _)]).
- destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Rk]. lia.
- destruct (Hro i Hi) as (Hr & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
  pose proof (pa_img_range _ Himg). lia.
Qed.

(* two live blocks with the same start are the same block (the allocator record keeps them disjoint) *)
Lemma scc_same_start : forall ly S (W : world SEGS) mem md a b, AR SEGS B ly S W mem md ->
In a (ablocks B ly S) -> In b (ablocks B ly S) -> fst a = fst b -> a = b.
Proof.
intros ly S W mem md [pa na] [pb nb] HAR Ha Hb E. cbn [fst] in E. subst pb.
destruct (decide ((pa, na) = (pa, nb))) as [Heq | Hne]; [exact Heq|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md pa na pa nb HAR Ha Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa na HAR Ha) as (_ & _ & _ & _ & _ & _ & Hna).
destruct (al_blocks _ _ LAWS ly S W mem md pa nb HAR Hb) as (_ & _ & _ & _ & _ & _ & Hnb).
pose proof (req_size_pos na ltac:(lia)) as [Ra _]. pose proof (req_size_pos nb ltac:(lia)) as [Rb _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the block bookkeeping of the post, over the block lists of the entry (bl0), the join (blc), answer's entry (bl4)
   and the end (bl5) *)
Lemma scc_post_lists : forall (bl0 blc bl4 bl5 O O1 O' : list (Z * Z)) pnew p1 p2 old,
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn blc -> In pn bl0) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn blc -> In pn O1) ->
(forall pn, In pn O1 -> In pn blc) ->
~ In pnew blc ->
(forall pn, In pn bl4 <-> pn = pnew \/ In pn blc) ->
(forall pn, In pn bl4 -> fst pn <> old -> pn <> p1 /\ pn <> p2) -> p1 <> p2 ->
(forall pn, In pn bl5 <-> (In pn bl4 /\ fst pn <> old) \/ pn = p1 \/ pn = p2) ->
(forall pn, In pn O' <-> (In pn (O1 ++ [pnew]) /\ fst pn <> old) \/ pn = p1) ->
(forall pn, In pn bl4 -> fst pn = old -> In pn (O1 ++ [pnew])) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In p2 bl5 /\
(In p2 bl0 -> In p2 O) /\
~ In p2 O' /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl5 /\ In pn bl4) /\
(forall pn, In pn bl5 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = p2).
Proof.
intros bl0 blc bl4 bl5 O O1 O' pnew p1 p2 old HB2 HB1 HO1 HO2 HO1c Hnew H4 Hfr H12 H5 HO' Hold.
assert (Hdec : forall pn (l : list (Z * Z)), In pn l \/ ~ In pn l)
  by (intros pn l; destruct (in_dec (fun x y : Z * Z => decide (x = y)) pn l); tauto).
assert (Hnew0 : In pnew bl0 -> In pnew O).
{ intros H0. destruct (Hdec pnew O) as [H|H]; [exact H | exfalso; exact (Hnew (HB2 _ H0 H))]. }
(* a fresh copy that was a block of the entry was one of the recorder's (freed on the spill arm or as the old answer) *)
assert (Cp : forall pp, pp = p1 \/ pp = p2 -> In pp bl0 -> In pp O).
{ intros pp Hpp H0. destruct (Hdec pp O) as [H|H]; [exact H|]. exfalso.
  assert (Hc : In pp blc) by exact (HB2 _ H0 H).
  assert (H4' : In pp bl4) by (apply H4; right; exact Hc).
  destruct (Z.eq_dec (fst pp) old) as [Eo | Ne].
  - pose proof (Hold _ H4' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
    + exact (H (HO1 _ Hin)).
    + subst pp. exact (Hnew Hc).
  - destruct (Hfr _ H4' Ne) as [N1 N2]. destruct Hpp as [-> | ->]; [exact (N1 eq_refl) | exact (N2 eq_refl)]. }
split; [|split; [|split; [|split; [|split]]]].
- intros pn Hpn. apply HO' in Hpn as [(Hin & _) | ->].
  + apply in_app_or in Hin as [Hin | [<- | []]]; [left; exact (HO1 _ Hin)|].
    destruct (Hdec pnew bl0) as [H|H]; [left; exact (Hnew0 H) | right; exact H].
  + destruct (Hdec p1 bl0) as [H|H]; [left; exact (Cp p1 (or_introl eq_refl) H) | right; exact H].
- apply H5. right; right. reflexivity.
- intros H0. exact (Cp p2 (or_intror eq_refl) H0).
- intros Hin. apply HO' in Hin as [(Hin & Hne) | E]; [|exact (H12 (eq_sym E))].
  assert (H4' : In p2 bl4).
  { apply in_app_or in Hin as [Hin | [E | []]]; apply H4; [right; exact (HO1c _ Hin) | left; symmetry; exact E]. }
  exact (proj2 (Hfr _ H4' Hne) eq_refl).
- intros pn H0 HnO. assert (Hc : In pn blc) by exact (HB2 _ H0 HnO).
  assert (H4' : In pn bl4) by (apply H4; right; exact Hc).
  split; [|exact H4']. apply H5. left. split; [exact H4'|]. intros Eo.
  pose proof (Hold _ H4' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
  + exact (HnO (HO1 _ Hin)).
  + subst pn. exact (Hnew Hc).
- intros pn Hpn. apply H5 in Hpn as [(Hin4 & Hne) | [-> | ->]].
  + apply H4 in Hin4 as [-> | Hc].
    * right; left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hne].
    * destruct (Hdec pn O) as [HinO' | HnO].
      -- right; left. apply HO'. left. split; [apply in_or_app; left; exact (HO2 _ HinO' Hc) | exact Hne].
      -- left. split; [exact (HB1 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

(* --- the walk from the join to the tail jump ------------------------------------------------------------------ *)
Theorem scc_join : forall ly S W regs mem md ch id R O lyc Sc Wc regsc memc mdc kc O1 c,
afn_pre SEGS B SUP_CHAIN_CLEAR_STK ly S W regs mem md ch ->
(* rounding mode 0 at the entry (the statement's pre): arg_i's and answer's pre *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_CHAIN_CLEAR R <= EV_MAX -> blocks_bytes S + LIVE_SUP_CHAIN_CLEAR R id <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CHAIN_CLEAR MT R id) ->
(length (r_calls R) <= 16)%nat ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(* the state at the join *)
ajournal SEGS B SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md [] lyc Sc Wc memc mdc kc ->
kc <= rec_spill_frees R ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
c = rec_slotA R ->
(forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW Wc memc a) -> aval_mem rd' c 4 REC_CHAIN_CLEAR ->
   aval_mem rd' (c + 4) 4 0 -> rec_repA B lyc Sc rd' (rec_record R REC_CHAIN_CLEAR []) O1) ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
((length (r_calls R) < 16)%nat -> forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
spZ regsc = spZ regs - 32 -> getr regsc 8 = w64 c -> getr regsc 9 = w64 id -> getr regsc 18 = w64 SB ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall r, acallee_saved r -> 19 <= r -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
rdword (rdW Wc memc) (spZ regs - 32) = Some (bv_unsigned (getr regs 18)) ->
rdword (rdW Wc memc) (spZ regs - 24) = Some (bv_unsigned (getr regs 9)) ->
rdword (rdW Wc memc) (spZ regs - 16) = Some (bv_unsigned (getr regs 8)) ->
rdword (rdW Wc memc) (spZ regs - 8) = Some (bv_unsigned (getr regs 1)) ->
SRr SEGS Wc (cfg_at SEGS (BASE + SCC_JOIN) regsc memc mdc)
  (apost_baseF SEGS B SUP_CHAIN_CLEAR_STK (scc_FP O) regs ly S W mem md (EV_SUP_CHAIN_CLEAR R) (scc_Q ly S id R O)).
Proof.
intros ly S W regs mem md ch id R O lyc Sc Wc regsc memc mdc kc O1 c
  HPRE HFRM HROD HROOK H10 Hid HFR HEV HLIVE HMOK Hlen HOS HJ Hkc HMLE Hbb Ec HPEND HB1 HB2 HB3 HO1 HO2
  Hspc H8 H9 H18 H3 H4 Hcs F0 F8 F16 F24.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_CHAIN_CLEAR_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 + 32 <= sp0 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. rewrite WS in Hslo. lia. }
pose proof (rec_slotA_home R Hlen) as (Hhome & Hc1 & Hc2 & Hc8 & Hc3). rewrite <- Ec in Hhome, Hc1, Hc2, Hc8, Hc3.
assert (Hc : scc_slot_ok c) by (split; [exact Hc1 | split; [exact Hc8 | exact Hc3]]).
assert (Hcz : 0 <= c < 2 ^ 64) by (clear - Hc1 Hc2; unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
pose proof (proj1 HJ) as HARc.
destruct (scc_join_seed lyc Sc Wc memc mdc regsc regs c HARc ltac:(rewrite Hspc; lia)
  ltac:(rewrite Hspc; clear - Hsp16; unfold sp0 in *; apply Z.mod_divide in Hsp16 as [q Hq]; [|lia]; rewrite Hq;
        replace (q * 16 - 32) with ((q - 2) * 16) by lia; apply Z_mod_mult)
  H8 Hc H18 ltac:(rewrite Hspc; exact F0) ltac:(rewrite Hspc; replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact F8)
  ltac:(rewrite Hspc; replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact F16)
  ltac:(rewrite Hspc; replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact F24)) as [HS SHOK].
set (E := EJ regsc regs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EJ; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. unfold E, EJ. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5;
    change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (scc_saved regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 8) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 9) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 18) by exact (EX 3%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hspc).
assert (E8 : ew E 8 = w64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = w64 id) by (rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (EL 3%nat 3%bv eq_refl); exact H3).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (EL 4%nat 4%bv eq_refl); exact H4).
clearbody E. clear EX.
unfold cfg_at, w64.
(* 0x8c5c4 .. 0x8c5fc: the two checks on the slot, c->fn := 18, c->nargs := 0, then the call of arg_i(c, id) *)
paj_run_tok RUN HS HJ SHOK scc_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen (segs := SEGS) B) with (n := 8%nat);
    [reflexivity | rewrite E8; unfold w64; exact (unsigned_lit_small c Hcz) | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply scc_awr_rec. apply (scc_slot_in c); [exact Hc | unfold CALL_SIZE; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* the two stores: c->fn = 18, c->nargs = 0, and nothing else changed *)
lazymatch type of HS with
| st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) scc_slot) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict mkst] in HRg
end.
assert (Uc : bv_unsigned (ew E 8) = c) by (rewrite E8; unfold w64; exact (unsigned_lit_small c Hcz)).
pose proof (field_of_region (segs := SEGS) E _ 8 c _ _ _ _ _ 0 4 (SLit 18) 18 HRg Uc ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfn.
pose proof (field_of_region (segs := SEGS) E _ 8 c _ _ _ _ _ 4 4 (SLit 0) 0 HRg Uc ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vna.
clear HRg.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ ?mA) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc mA (fun a => c <= a < c + 8) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Uc in Hrr; lia|]);
          destruct Hin)) as UN1
end.
rewrite Z.add_0_r in Vfn.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgA := rg) in *; set (mA := mm) in *; set (mdA := mdq) in *
end.
pose proof (proj1 HJ) as HARa.
pose proof HJ as (_ & _ & _ & _ & _ & HfrA & HnevA & _).
assert (Hcs2 : c + CALL_SIZE <= 0x5e3c18) by (clear - Hc2; unfold A_REC_SPILL, SC_SIZE in Hc2; lia).
assert (HREP1 : rec_repA B lyc Sc (rdW Wc mA) (rec_record R REC_CHAIN_CLEAR []) O1).
{ apply HPEND.
  - intros a Ha Hn. apply UN1; [exact Ha | exact Hn].
  - apply (aval_mem_view SEGS (w_H Wc) mA). exact Vfn.
  - apply (aval_mem_view SEGS (w_H Wc) mA). exact Vna. }
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
  (scc_ro_off ly S W mem md O HAR HOS) HROD) as HRODa.
pose proof (cmd_ro_ok_of_aro lyc Sc Wc mA mdA HARa HRODa) as HROa.
assert (HXa : 0 <= XM_ARG_I MT id /\ 0 <= XM_ANSWER MT (snd (sup_chain_clear_m R id))).
{ unfold XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_clear_m R id))) + 1) ltac:(lia)). lia. }
assert (HEVa : st_nev Sc + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_CHAIN_CLEAR, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (HLIVEa : blocks_bytes Sc + LIVE_ARG_I id <= LIVE_MAX).
{ unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in HLIVE. lia. }
assert (HMOKa : mo_ok MT Sc (XM_ARG_I MT id)).
{ apply (mok_station MT S Sc (XM_SUP_CHAIN_CLEAR MT R id) (rec_spill_frees R * mo_free MT) (XM_ARG_I MT id) MTL HMOK HMLE);
  [lia | unfold XM_SUP_CHAIN_CLEAR; lia]. }
assert (P10' : getr rgA 10 = w64 c) by (rewrite P10; exact E8).
assert (P11' : getr rgA 11 = w64 id) by (rewrite P11; exact E9).
assert (Nargs0 : aval_mem (rdW Wc mA) (c + CALL_OFF_NARGS) 4 0) by (apply (aval_mem_view SEGS (w_H Wc) mA); exact Vna).
assert (HFRa : Z.of_nat (length (frames Sc)) <= 8) by (rewrite HfrA; exact HFR).
(* the call of arg_i: its contract through cl_callS_wideF (arg_i writes c->nargs and c->args[0] of g_rec /
   record.spill, and returns at some FP state fx1 with fxrel fx fx1: it reaches the snprintf wrapper) *)
rewrite (proj1 (proj2 scc_sig)).
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS Wc rgA mA _ SUP_CHAIN_CLEAR_STK sp0 (scc_FP O) ly S W mem md [] lyc Sc mdA kc
    ARG_I_STK (scc_FPa c) EV_ARG_I (-32) (getr rgA 1) [] (scc_Karg lyc Sc c id) HJ).
  - unfold spZ. rewrite P2, Usp. lia.
  - reflexivity.
  - lia.
  - unfold ARG_I_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite WS. unfold ARG_I_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite P3, E3. exact Hgp.
  - rewrite P4, E4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, E8. unfold w64. rewrite unsigned_lit_small by lia.
    unfold CALL_SIZE in Hcs2. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (TARG_I fx lyc Sc Wc rgA mA mdA [] c id 0 HPRE1 HFRM HFRa HRODa HROa P10' P11' Hid Hhome Nargs0
        ltac:(unfold REC_ARGS_MAX; lia) HEVa HLIVEa HMOKa).
    + cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & _ & HMLE2 & HCASE).
      exists fx2, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
      split; [exact HJ2|]. split; [exact HP2|].
      unfold scc_Karg. split; [exact HMLE2|].
      destruct HCASE as [(Hm6 & _) | (_ & p & Hp & Hperm & Hfresh & Hna & Hap & Hstr)];
        [unfold REC_ARGS_MAX in Hm6; lia|].
      exists p. split; [exact Hp|]. split; [exact Hperm|]. split; [exact Hfresh|].
      split; [exact Hna|]. split; [exact Hap | exact Hstr].
  - intros a Ha. apply scc_awr_rec. apply (scc_slot_in c); [exact Hc|].
    pose proof (scc_FPa_in c a Ha). unfold CALL_SIZE. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (scc_FPa_in c a Ha).
    rewrite WS in Hw. unfold CALL_SIZE in Hcs2. lia. }
cbv beta. intros W3 c3 Hwle3 (fx1 & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HK3). rewrite P1.
(* arg_i returned at fx1: the rest of the walk runs at fx1 (the call site's symbolic state taken to fx1, the runs at
   fx1, rounding mode 0 at fx1 for answer's pre) *)
pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
pose proof (fxrel_frm0 fx fx1 HFRM Hfx) as HFRM1.
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia |].
  intros a Ha Hf. pose proof (scc_FPa_in c a Hf). unfold CALL_SIZE in Hcs2. lia. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS3. rename HS3 into HS.
remember (havoc E 40 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 40)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
(* the recorder after arg_i: the call c holds (18, [dec id]) and the recorder owns the copy of dec id *)
destruct HK3 as (HMLE3 & p & Hp4096 & Hperm3 & Hfresh3 & Hna3 & Hap3 & Hstr3).
set (nd := Z.of_nat (length (dec id)) + 1) in *.
pose proof (proj1 HJc3) as HAR3.
assert (Hdec : (1 <= length (dec id) <= 11)%nat) by exact (dec_length id Hid).
assert (Hpin3 : In (p, nd) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
assert (HinSc3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm3)); right; exact Hpn).
assert (HO1Sc : forall pn, In pn O1 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (proj1 (rec_repA_blocks B lyc Sc (rdW Wc mA) _ O1 HREP1 pn Hpn))).
assert (HskA : ~ YI16.sink_open_fp (scc_FPa c)).
{ apply sink_closed_pos. unfold scc_FPa. change (0 <? REC_ARGS_MAX) with true. cbn.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS. repeat constructor; cbn [fst]; lia. }
assert (HFPa_rec : forall a, inFP (scc_FPa c) a -> in_recA a).
{ intros a Ha. pose proof (scc_FPa_in c a Ha). unfold in_recA. apply (scc_slot_in c); [exact Hc | unfold CALL_SIZE; lia]. }
assert (HpO1 : ~ In p (map fst O1)).
{ intros Hq. apply in_map_iff in Hq as ([q k] & Hqe & Hq). cbn [fst] in Hqe. subst q.
  pose proof (HO1Sc _ Hq) as HqSc.
  pose proof (proj1 (Forall_forall _ _) Hfresh3 _ HqSc) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap.
  assert (Hk0 : k <= 0) by lia.
  assert (Hne : (p, k) <> (p, nd)) by (intros Hx; injection Hx as Hx; lia).
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 p k p nd HAR3 (HinSc3 _ HqSc) Hpin3 Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p k HAR3 (HinSc3 _ HqSc)) as (_ & _ & _ & _ & _ & _ & Hkr).
  pose proof (req_size_pos k ltac:(lia)) as [Rk _]. pose proof (req_size_pos nd ltac:(lia)) as [Rn _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HREP2 : rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_CHAIN_CLEAR ([] ++ [dec id])) (O1 ++ [(p, nd)])).
{ apply (rec_repA_arg B lyc Sc (rdW Wc mA) ly3 S3 (rdW W3 mem3) R REC_CHAIN_CLEAR [] O1 (dec id) p nd HREP1).
  - cbn. lia.
  - rewrite <- Ec. exact Hna3.
  - rewrite <- Ec. exact Hap3.
  - intros a Ha Hn1 Hn2. rewrite <- Ec in Hn1, Hn2.
    apply (scc_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3 HskA Ha).
    intros (r & Hr & Hrr). unfold scc_FPa in Hr. change (0 <? REC_ARGS_MAX) with true in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrr; [apply Hn1 | apply Hn2]; cbn; lia.
  - intros pn Hpn. split; [exact (HinSc3 _ (HO1Sc _ Hpn))|]. intros i Hi.
    destruct pn as [q k]. cbn [fst snd] in Hi |- *.
    exact (scc_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q k i HJc3 HARa HFPa_rec (HO1Sc _ Hpn) (HinSc3 _ (HO1Sc _ Hpn)) Hi).
  - exact HpO1.
  - lia.
  - exact Hpin3.
  - unfold LMAX. lia.
  - unfold LMAX, nd. lia.
  - exact Hstr3.
  - exact (proj1 (scc_blk_apart ly3 S3 W3 mem3 md3 p nd HAR3 Hpin3)).
  - exact (proj2 (scc_blk_apart ly3 S3 W3 mem3 md3 p nd HAR3 Hpin3)). }
cbn [app] in HREP2.
(* 0x8c600 .. 0x8c60c: a0 := "chain_clear" (0x21f40), a1 := 11, the call of rec_shape_of *)
assert (SHOKa : sh_ok SEGS scc_Bx [] Ea (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN1 HS HJ3 SHOKa scc_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgB := rg) in *; set (mB := mm) in *; set (mdB := mdq) in *
end.
lazymatch goal with Hfr : frame_of Ea _ (mrestrict _ mem3) (mrestrict _ mB) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) Ea _ (w_H W3) mem3 mB (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN2
end.
pose proof (proj1 HJ3) as HAR3b.
pose proof HJ3 as (_ & _ & _ & _ & _ & Hfr3 & Hnev3 & _).
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3
  (scc_ro_off ly S W mem md O HAR HOS) HROD) as HROD3.
pose proof (cmd_ro_ok_of_aro ly3 S3 W3 mB mdB HAR3b HROD3) as HRO3.
assert (HLIT : abytes_atR (rdW W3 mB) 0x21f40 RO_lit_21f40).
{ clear - HRO3. destruct HRO3 as [HRO3 _]. unfold cmd_ro_bytes in HRO3.
  repeat match type of HRO3 with
  | abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 HRO3)
  | _ /\ _ => apply proj2 in HRO3
  end. }
assert (HVERB : Z.of_nat (length scc_verb) <= 16 ->
  abytes_atR (rdW W3 mB) 0x21f40 scc_verb /\
  (in_blockA (ablocks B ly3 S3) 0x21f40 (Z.of_nat (length scc_verb)) \/
   astr_argA B ly3 S3 (rdW W3 mB) (in_roP SEGS RLO RHI) [] 0x21f40 (Some scc_verb))).
{ intros _. split.
  - apply (scc_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite scc_verb_ro. exact HLIT.
  - right. exact (scc_verb_argA ly3 S3 (rdW W3 mB) [] HLIT). }
assert (HEV3 : st_nev S3 + EV_REC_SHAPE_OF <= EV_MAX).
{ unfold EV_SUP_CHAIN_CLEAR, EV_REC_SHAPE_OF, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (Q10' : getr rgB 10 = w64 0x21f40).
{ rewrite Q10. change 314%nat with (A_OBJ 73). rewrite (img_env_atomP Ea (A_OBJ 73) HEIa ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 73%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Q11' : getr rgB 11 = w64 (Z.of_nat (length scc_verb))) by (rewrite Q11, scc_verb_len; reflexivity).
(* the call of rec_shape_of("chain_clear", 11): no footprint, no allocator event, the frame form (afn_pre_na) *)
rewrite (proj1 (proj2 (proj2 scc_sig))).
eapply SRr_bind.
{ eapply (cl_callS_na (fx := fx1) B LAWS W3 rgB mB _ SUP_CHAIN_CLEAR_STK sp0 (scc_FP O) ly S W mem md [] ly3 S3 mdB (kc + EV_ARG_I)
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr rgB 1) (scc_Krso ly3 S3) HJ3).
  - unfold spZ. rewrite Q2, OLDa by lia. rewrite Usp. lia.
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite WS. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite Q3, OLDa, E3 by lia. exact Hgp.
  - rewrite Q4, OLDa, E4 by lia. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - intros HPRE2. eapply SRr_mono.
    + exact (TREC_SHAPE_OF fx1 ly3 S3 W3 rgB mB mdB 0x21f40 scc_verb HPRE2 HROD3 Q10' ltac:(lia) Q11'
        ltac:(rewrite scc_verb_len; lia) HRO3 VOBJS HVERB HEV3).
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
      exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4). rewrite Q1.
jafter_call_keep_pi HS 60%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | rewrite OLDa by lia; exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia |].
  intros a Ha Hf. exact (inFP_nil a Hf). }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS4. rename HS4 into HS.
remember (havoc Ea 60 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 60)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (Eb60 : forall j, (j < length CLOB)%nat -> ew Eb (60 + j) = nth j (map (getr regs4) CLOB) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HEb. unfold havoc. cbn [ew].
  replace (60 + j <? 60)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (60 + j - 60)%nat with j by lia. apply nth_indep. rewrite length_map. exact Hj. }
clear HEb.
(* the recorder after rec_shape_of: nothing it owns changed *)
destruct HK4 as ((q & Hq10 & Hq64 & HqA) & Hperm4 & Ely4 & ES4).
pose proof (proj1 HJc4) as HAR4.
assert (HinS34 : forall pn, In pn (ablocks B ly3 S3) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym Hperm4) Hpn)).
assert (Hblk3 : forall q' k' i, In (q', k') (ablocks B ly3 S3) -> 0 <= i < k' -> 0 <= q' + i < 2 ^ 64).
{ intros q' k' i Hin Hi. destruct (al_blocks _ _ LAWS ly3 S3 W3 mB mdB q' k' HAR3b Hin) as (_ & Hq4 & Hqc & _ & _ & _ & _).
  pose proof (req_size_pos k' ltac:(lia)) as [_ Rk]. lia. }
(* 0x8c610 .. 0x8c630: a2 := 1, a1 := the shape, a0 := c, the frame restored, the tail jump into answer *)
assert (SHOKb : sh_ok SEGS scc_Bx [] Eb (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN1 HS HJ4 SHOKb scc_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18.
prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22.
prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
prreg HS (27%bv : bv 5) T27.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdT := mdq) in *
end.
clearbody mdT.
(* the registers at the tail jump: the entry's ra, sp, s0, s1, s2 and the callee-saved ones, c, the shape, 1 *)
assert (OLDab : forall n, (n < 40)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite OLDb, OLDa by lia; reflexivity).
assert (R1 : getr rgT 1 = getr regs 1) by (rewrite T1, OLDab by lia; exact E32).
assert (Rsp : spZ rgT = sp0).
{ unfold spZ. rewrite T2, OLDab by lia. rewrite Usp. rewrite unsigned_lit_small by lia. lia. }
assert (R3 : getr rgT 3 = getr regs 3) by (rewrite T3, OLDab, E3 by lia; reflexivity).
assert (R4 : getr rgT 4 = getr regs 4) by (rewrite T4, OLDab, E4 by lia; reflexivity).
assert (R8 : getr rgT 8 = getr regs 8) by (rewrite T8, OLDab by lia; exact E33).
assert (R9 : getr rgT 9 = getr regs 9) by (rewrite T9, OLDab by lia; exact E34).
assert (R18 : getr rgT 18 = getr regs 18) by (rewrite T18, OLDab by lia; exact E35).
assert (R10 : getr rgT 10 = w64 c) by (rewrite T10, OLDab by lia; exact E8).
assert (R11 : getr rgT 11 = w64 q)
  by (rewrite T11; change 64%nat with (60 + 4)%nat; rewrite (Eb60 4%nat ltac:(cbv; lia)); exact Hq10).
assert (Rhi : forall r, acallee_saved r -> 19 <= r -> getr rgT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr H19. unfold acallee_saved in Hr. assert (Hc19 : 19 <= r <= 27) by lia.
  rewrite <- (Hcs r Hr H19).
  assert (Hcases : r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T19, OLDab by lia. exact (EL 19%nat 19%bv eq_refl).
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T20, OLDab by lia. exact (EL 20%nat 20%bv eq_refl).
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T21, OLDab by lia. exact (EL 21%nat 21%bv eq_refl).
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T22, OLDab by lia. exact (EL 22%nat 22%bv eq_refl).
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T23, OLDab by lia. exact (EL 23%nat 23%bv eq_refl).
  - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T24, OLDab by lia. exact (EL 24%nat 24%bv eq_refl).
  - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T25, OLDab by lia. exact (EL 25%nat 25%bv eq_refl).
  - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T26, OLDab by lia. exact (EL 26%nat 26%bv eq_refl).
  - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T27, OLDab by lia. exact (EL 27%nat 27%bv eq_refl). }
assert (HPT : aregs_preserved regs rgT).
{ intros r Hr. destruct (Z.lt_ge_cases r 19) as [Hlt | Hge]; [|exact (Rhi r Hr Hge)].
  unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    apply bv_eq. fold (spZ rgT). rewrite Rsp. reflexivity.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact R8.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact R9.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact R18. }
(* the memory the tail jump hands to answer: the epilogue wrote nothing *)
lazymatch goal with Hfr : frame_of Eb _ (mrestrict _ mem4) (mrestrict _ mT) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) Eb _ (w_H W4) mem4 mT (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN3
end.
pose proof (proj1 HJ4) as HART.
pose proof HJ4 as (_ & HlyT & _ & _ & _ & HfrT & HnevT & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4
  (scc_ro_off ly S W mem md O HAR HOS) HROD) as HRODT.
pose proof (cmd_ro_ok_of_aro ly4 S4 W4 mT mdT HART HRODT) as HROT.
assert (HFRT : Z.of_nat (length (frames S4)) <= 8) by (rewrite HfrT; exact HFR).
set (R2 := rec_record R REC_CHAIN_CLEAR [dec id]) in *.
set (O2 := O1 ++ [(p, nd)]) in *.
set (x := shape_of scc_verb) in *.
set (e := (REC_CHAIN_CLEAR, [dec id])).
set (t := snd (rec_answer R2 e x true)).
assert (Ht : snd (sup_chain_clear_m R id) = t) by reflexivity.
assert (HREPT : rec_repA B ly4 S4 (rdW W4 mT) R2 O2).
{ apply (rec_repA_keep B ly3 S3 (rdW W3 mem3) ly4 S4 (rdW W4 mT) R2 O2 HREP2).
  - intros a Ha. assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (UN3 a Ha64 (fun z => z)).
    rewrite (scc_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc4 (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
    exact (UN2 a Ha64 (fun z => z)).
  - intros pn Hpn. pose proof (proj1 (rec_repA_blocks B ly3 S3 _ _ _ HREP2 pn Hpn)) as Hpn3.
    split; [exact (HinS34 _ Hpn3)|]. intros i Hi. destruct pn as [q' k']. cbn [fst snd] in Hi |- *.
    pose proof (Hblk3 q' k' i Hpn3 Hi) as Hb.
    rewrite (UN3 _ Hb (fun z => z)).
    rewrite (scc_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q' k' i HJc4 HAR3b (fun a Ha => False_ind _ (inFP_nil a Ha))
      Hpn3 (HinS34 _ Hpn3) Hi).
    exact (UN2 _ Hb (fun z => z)). }
destruct (rec_repA_answer B ly4 S4 _ _ _ HREPT) as (old & Hold & Holdc).
assert (Hold64 : 0 <= old < 2 ^ 64).
{ pose proof asan_consts as (Ca & _). destruct Holdc as [-> | (pn' & Hpn' & Eo')]; [lia|].
  destruct pn' as [a k]. cbn [fst] in Eo'. subst a.
  pose proof (proj1 (rec_repA_blocks B ly4 S4 _ _ _ HREPT _ Hpn')) as Hin4.
  destruct (al_blocks _ _ LAWS ly4 S4 W4 mT mdT old k HART Hin4) as (_ & H4096 & Hoc & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Rk]. lia. }
assert (Hqb : forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= q + i < 2 ^ 64)
  by exact (scc_argA_bound ly4 S4 W4 mem4 md4 _ [] q x HAR4 (proj1 Hq64) (HqA [])).
assert (HSH : r_refuse R2 = 0 ->
  astr_argA B ly4 S4 (rdW W4 mT) (in_roP SEGS RLO RHI) O2 q (Some x) /\ fits x).
{ intros _. split; [|exact scc_fits].
  apply (scc_argA_rd ly4 S4 (rdW W4 mem4) (rdW W4 mT) O2 q x (HqA O2)).
  intros i Hi. exact (UN3 (q + i) (Hqb i Hi) (fun z => z)). }
assert (HSLOT : r_refuse R2 = 0 -> true = true ->
  (exists k, nth_error (r_calls R2) k = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (c = A_REC_SPILL /\ e = r_spill R2)).
{ intros _ _. rewrite Ec. exact (rec_slotA_entry R REC_CHAIN_CLEAR [dec id] Hlen). }
assert (Hchg : true = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite T12; reflexivity).
assert (HEVT : st_nev S4 + EV_ANSWER <= EV_MAX).
{ unfold EV_SUP_CHAIN_CLEAR, EV_REC_SHAPE_OF, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (Hbb4 : blocks_bytes S4 = nd + blocks_bytes Sc).
{ rewrite (blocks_bytes_bsum B ly4 S4), (blocks_bytes_bsum B lyc Sc).
  rewrite (bsum_perm _ _ Hperm4), (bsum_perm _ _ Hperm3), bsum_cons. reflexivity. }
assert (HLIVET : blocks_bytes S4 + LIVE_ANSWER t <= LIVE_MAX).
{ rewrite Hbb4. unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ARG_I, LIVE_XSTRDUP in HLIVE. rewrite Ht in HLIVE. unfold nd. lia. }
assert (HXt : 0 <= XM_ANSWER MT t) by (rewrite <- Ht; exact (proj2 HXa)).
assert (HMOKc : mo_ok MT Sc (XM_ARG_I MT id + XM_ANSWER MT t)).
{ apply (mo_ok_step MT MTL S Sc (rec_spill_frees R * mo_free MT)); [|exact HMLE].
  unfold XM_SUP_CHAIN_CLEAR in HMOK. rewrite Ht, <- Z.add_assoc in HMOK. exact HMOK. }
assert (Hm34 : mo_le MT S3 S4 0) by (rewrite ES4; exact (mo_le_refl MT MTL S3)).
pose proof (mle_station MT Sc S3 S4 _ _ MTL HMLE3 Hm34) as HmSc4.
assert (HMOKT : mo_ok MT S4 (XM_ANSWER MT t)).
{ apply (mok_station MT Sc S4 (XM_ARG_I MT id + XM_ANSWER MT t) (XM_ARG_I MT id + 0) (XM_ANSWER MT t) MTL HMOKc HmSc4);
  lia. }
(* the tail jump: answer runs at this function's entry sp, at the FP state fx1 arg_i returned, and returns to its
   caller at some fx2 with fxrel fx1 fx2 *)
rewrite (proj2 (proj2 (proj2 scc_sig))).
eapply SRr_mono.
{ eapply (cl_callS_wideF (fx := fx1) B LAWS W4 rgT mT _ SUP_CHAIN_CLEAR_STK sp0 (scc_FP O) ly S W mem md [] ly4 S4 mdT
    (kc + EV_ARG_I + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ4).
  - rewrite Rsp. lia.
  - reflexivity.
  - lia.
  - unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite WS. unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - reflexivity.
  - rewrite R1. exact Hra.
  - rewrite R1. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite R8. fold (s0Z regs).
    apply (achain_ly_top ly ly4 _ _ _ _ EtopT).
    apply (achain_kept ly (rdW W mem) (rdW W4 mT) sp0 (s0Z regs) ch sp0 Hch); [lia | lia |].
    intros a Ha. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply F1; [lia | lia |].
    intros (r & Hr & Hra'). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra'.
    + unfold A_G_REC, REC_SIZE in Hra'. lia.
    + unfold A_REC_SPILL, SC_SIZE in Hra'. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Hra'.
      destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR (HOS _ Hin)) as (_ & _ & Hbc & _). lia.
  - intros HPRE3. eapply SRr_mono.
    + exact (TANSWER fx1 ly4 S4 W4 rgT mT mdT ch c q old e x true R2 O2
        HPRE3 HFRM1 HFRT HRODT HROT R10 Hcz R11 Hq64 Hchg HREPT Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
    + cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HK2).
      exists fx2, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
      split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply scc_awr_rec. left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply scc_awr_rec. left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Ha.
      apply scc_filter_in in Hin.
      assert (HinT : In (pb, nb) (ablocks B ly4 S4)) by exact (proj1 (rec_repA_blocks B ly4 S4 _ _ _ HREPT _ Hin)).
      assert (HinFP : In (pb, nb) O -> inFP (scc_FP O) a).
      { intros HO. exists (pb, pb + req_size nb). split; [right; right; apply in_map_iff; exists (pb, nb); split; [reflexivity | exact HO]|].
        cbn [fst snd]. exact Ha. }
      destruct (in_dec (fun u v : Z * Z => decide (u = v)) (pb, nb) O) as [HO | HnO].
      * right; left. split; [exact (HinFP HO)|]. exists pb, nb. split; [exact HinT | exact Ha].
      * right; right; left. exists pb, nb. split; [exact HinT|]. split; [|exact Ha].
        intros H0. pose proof (HB2 _ H0 HnO) as HSc.
        unfold O2 in Hin. apply in_app_or in Hin as [Hin | [E' | []]].
        -- exact (HnO (HO1 _ Hin)).
        -- rewrite <- E' in HSc. pose proof (proj1 (Forall_forall _ _) Hfresh3 _ HSc) as Hap. cbn [fst snd] in Hap.
           unfold iv_apart in Hap. unfold nd in Hap. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. exfalso.
    rewrite WS in Hw. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + unfold A_G_REC, OFF_STATE in Ha. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Ha.
      apply scc_filter_in in Hin.
      pose proof (proj1 (rec_repA_blocks B ly4 S4 _ _ _ HREPT _ Hin)) as HinT.
      destruct (al_blocks _ _ LAWS ly4 S4 W4 mT mdT pb nb HART HinT) as (_ & _ & Hbc & _).
      rewrite WS in Hslo. lia. }
cbv beta. intros W5 c5 _ (fx2 & ly5 & S5 & regs5 & mem5 & md5 & Hfx2 & -> & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (p1 & p2 & O' & HK5). cbv zeta in HK5.
change (snd (rec_answer R2 e x true)) with t in HK5.
destruct HK5 as (Hp2r & Hp24096 & H12 & Hfr12 & Hbl5 & HREP5 & HO'iff & Hstr5 & Hbb5 & HMLE5).
set (n := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ5) as HAR5.
(* answer returned at fx2, fxrel fx fx2 by way of fx1: this function's apost_baseF *)
rewrite R1.
apply (apost_baseF_intro (fx := fx) SEGS fx2 _ _ _ _ _ _ _ _ _ _ _ _ ly5 S5);
  [exact (fxrel_trans fx fx1 fx2 Hfx Hfx2)
  | eapply (ajournal_mono_k SEGS B); [exact HJ5|];
    unfold EV_SUP_CHAIN_CLEAR, EV_REC_SHAPE_OF, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia
  | exact (aregs_preserved_trans _ _ _ HPT HP5) |].
(* the block bookkeeping *)
assert (H4iff : forall pn, In pn (ablocks B ly4 S4) <-> pn = (p, nd) \/ In pn (ablocks B lyc Sc)).
{ intros pn. split; intros Hpn.
  - apply (Permutation_in _ Hperm4) in Hpn. apply (Permutation_in _ Hperm3) in Hpn.
    destruct Hpn as [<- | Hpn]; [left; reflexivity | right; exact Hpn].
  - apply (Permutation_in _ (Permutation_sym Hperm4)). apply (Permutation_in _ (Permutation_sym Hperm3)).
    destruct Hpn as [-> | Hpn]; [left; reflexivity | right; exact Hpn]. }
assert (HnewSc : ~ In (p, nd) (ablocks B lyc Sc)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hfresh3 _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, nd in Hap. lia. }
assert (Hold4 : forall pn, In pn (ablocks B ly4 S4) -> fst pn = old -> In pn O2).
{ intros pn Hpn Eo. destruct Holdc as [Eold | (pn' & Hpn' & Eo')].
  - destruct pn as [a k]. destruct (al_blocks _ _ LAWS ly4 S4 W4 mT mdT a k HART Hpn) as (_ & H4096 & _).
    cbn [fst] in Eo. lia.
  - assert (Hpn'4 : In pn' (ablocks B ly4 S4)) by exact (proj1 (rec_repA_blocks B ly4 S4 _ _ _ HREPT _ Hpn')).
    rewrite (scc_same_start ly4 S4 W4 mT mdT pn pn' HART Hpn Hpn'4 ltac:(congruence)). exact Hpn'. }
assert (Hfr4 : forall pn, In pn (ablocks B ly4 S4) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n))
  by exact Hfr12.
destruct (scc_post_lists (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly4 S4) (ablocks B ly5 S5) O O1 O'
  (p, nd) (p1, n) (p2, n) old HB2 HB1 HO1 HO2 HO1Sc HnewSc H4iff Hfr4
  ltac:(intros E'; injection E' as E'; exact (H12 E')) Hbl5 HO'iff Hold4) as (L1 & L2 & L3 & L4 & L5 & L6).
unfold scc_Q. exists (fst (rec_answer R2 e x true)), t, p2, O'.
split; [exact (surjective_pairing (rec_answer R2 e x true))|].
split; [exact Hp2r|]. split; [exact Hp24096|]. split; [exact HREP5|].
split; [exact L1|]. split; [exact L2|].
split; [intros pn H0 HnO E'; subst pn; exact (HnO (L3 H0))|].
split.
{ intros Hq. apply in_map_iff in Hq as (pn & Ep & Hpn).
  assert (Hpn5 : In pn (ablocks B ly5 S5)) by exact (proj1 (rec_repA_blocks B ly5 S5 _ _ _ HREP5 _ Hpn)).
  apply L4. rewrite <- (scc_same_start ly5 S5 W5 mem5 md5 pn (p2, n) HAR5 Hpn5 L2 Ep). exact Hpn. }
split; [exact Hstr5|].
split.
{ intros pn H0 HnO. destruct (L5 pn H0 HnO) as [H5' H4']. split; [exact H5'|].
  assert (Hne : pn <> (p2, n)) by (intros ->; exact (HnO (L3 H0))).
  destruct pn as [a k].
  pose proof (sep_blocks SEGS B LAWS ly5 S5 W5 mem5 md5 a k p2 n HAR5 H5' L2 Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 a k HAR5 H5') as (_ & _ & _ & _ & _ & _ & Hk).
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 p2 n HAR5 L2) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos k ltac:(lia)) as [_ Rk]. pose proof (req_size_pos n ltac:(lia)) as [_ Rn].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
split; [exact L6|].
split.
{ rewrite Hbb4 in Hbb5. unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ARG_I, LIVE_XSTRDUP. rewrite Ht. unfold nd in Hbb5. lia. }
pose proof (mle_station MT S Sc S4 _ _ MTL HMLE HmSc4) as HmS4.
pose proof (mle_station MT S S4 S5 _ _ MTL HmS4 HMLE5) as HmS5.
apply (mle_weaken MT S S5 _ _ MTL HmS5). unfold XM_SUP_CHAIN_CLEAR. rewrite Ht. lia.
Qed.

End e.
End f.
End d.
