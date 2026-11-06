(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic entry states of sup_connect's ASan walk
   (plugin-hostd/fuzz_command, 0x8ad20), in the form of cgif_file_fuzzer's A/AChc.v (the seed of a walk) and
   A/AChd.v, and the per-binary facts about the program's own statics that the walk uses at every step.

   The walk is cut in two at 0x8adac, the join of record()'s two arms, because the call slot's address is
   g_rec + 16 + 56 * ncalls on one arm and record.spill on the other: before the cut the slot is only computed
   (the executor keeps it as an offset of the object atom A_OBJ 44), after the cut it is the base of a region
   and of the shadow entry that removes the nine inline checks, so it must be an atom. `scn_ss_e` is the state
   at the entry and `scn_ss_m` the state at the join.

   Atoms. At the entry: 0..31 the registers, 32 the shadow base 0x7fff8000; the regions are the 80-byte frame,
   the GOT word A_OBJ 0 = 0xa63f0 and the cell A_OBJ 12 = 0xb10b8 (read-only), and g_rec's ncalls field
   [A_OBJ 44 + 8, A_OBJ 44 + 12). At the join: 0..31 the registers there (s0 = the slot, s6 = the shadow base),
   32..40 the entry values of ra, s0..s7 that the frame holds; the regions are that frame (read-only) and the
   slot [s0, s0 + 56); the one shadow entry is [s0, s0 + 56). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_line_c answer_c sup_connect_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the two readers of a 4- or 8-byte field are the same statement (two copies of one definition) *)
Lemma scn_le_byte_same : forall v n k, YG0f.le_byte v n k = YO0f.le_byte v n k.
Proof. reflexivity. Qed.
Lemma scn_le_byte_range : forall v n k, 0 <= YO0f.le_byte v n k < 256.
Proof. intros v n k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

(* the offsets of sup_connect the walk cuts at, as offsets of the listing's base *)
Definition SCN_JOIN : Z := 0x48c8.    (* 0x8adac, the join of record()'s two arms *)
Definition SCN_TAIL : Z := 0x4a28.    (* 0x8af0c, the jump into answer *)
(* the program functions sup_connect calls are CmdObj's cmd_prog_syms, with CmdObj's cmd_af; a walk ties
   `pa_sigma CS_<fn>` to `BASE + cmd_af CS_<fn>` with CmdObj's cmd_sig_prog *)
(* the registers the frame holds, in the order of their slots below the entry sp *)
Definition scn_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma scn_val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite <- Hb. symmetry.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma scn_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by apply scn_le_byte_range. reflexivity.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition SCN_SB : Z := 0x7fff8000.
(* the entry state *)
Definition scn_Bx_e : sv := SOff 32 0.
Definition scn_Bspan : Z * Z := (SCN_SB, SCN_SB + 2 ^ 44 - 1).
Definition scn_ncalls_region (n : Z) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
[YP09.mkChunk OFF_NCALLS (CVal 4 (SLit n))].
Definition scn_regs_e (n : Z) : smem := [stack_region 80; got_regionP; bcell_regionP 32; scn_ncalls_region n].
Definition scn_facts_e : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SCN_SB SCN_SB 0)] [] [].
Definition scn_ss_e (n : Z) : sstate := mkSS AF_sup_connect sr_atoms (scn_regs_e n) None scn_facts_e.
Definition scn_SH_e : list shent := [].
Definition scn_extra_e : list word := map (Z_to_bv 64) [SCN_SB].
(* the state at the join: the slot is atom 8 (s0), the shadow base atom 22 (s6), and atoms 32..40 are the
   entry values of ra, s0..s7 that the frame holds *)
Definition scn_Bx_m : sv := SOff 22 0.
Definition scn_slot_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 CALL_SIZE 0 CALL_SIZE [].
(* atom 2 is the JOIN's sp, 80 below the entry's, so the frame is [sp, sp + 80): ra at +72, s0 at +64, ...,
   s7 at +8 *)
Definition scn_stack_m : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 80 0 0
(map (fun j => YP09.mkChunk (72 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 9)).
Definition scn_regs_m : smem := [scn_stack_m; scn_slot_region].
Definition scn_facts_m : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
(22%nat, mkAF SCN_SB SCN_SB 0)] [] [].
Definition scn_ss_m : sstate := mkSS SCN_JOIN sr_atoms scn_regs_m None scn_facts_m.
Definition scn_SH_m : list shent := [mkSHE 8 0 CALL_SIZE].
Definition scn_extra_m (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) scn_saved.
(* the frame of the walk: the nine saved registers at their slots below the entry sp (cgif's cl_frame) *)
Definition scn_frame (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error scn_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* the call slot: a slot of g_rec's table or record.spill (arg_line_c.v:64) *)
Definition scn_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma scn_slot_facts : forall c, scn_slot c ->
c mod 8 = 0 /\ A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ (forall a, c <= a < c + CALL_SIZE -> inFP cmd_PG a).
Proof.
unfold scn_slot, cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX.
intros c [(i & Hi & ->) | ->].
- split; [|split; [lia|]].
  + replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia. apply Z_mod_mult.
  + intros a Ha. exists (6174528, 6174528 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- split; [reflexivity|]. split; [lia|].
  intros a Ha. exists (6175712, 6175712 + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Section e.
Variable B : asyms.
(* the per-binary facts (the walk hypotheses, with cgif's names) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* CmdRecFacts.v is not in the tree yet; these two are its group (a) facts under their final names: the
   cif_prog_img field of cmd_img_facts, and PROG_WRITABLE (from prog_rw and CmdBSyms' ts_prog) *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the program's own writable statics, from the record (CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
destruct Ha as (r & Hr & Hb). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hb.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* none of them is owned by the runtime or the errno cell, so a journal keeps the ones its footprint misses *)
Lemma scn_pg_unowned : forall a, inFP cmd_PG a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB).
destruct Ha as (r & Hr & Hb).
(* the three ranges are the objects' bodies; the ASan redzones around them are owned, the bodies are not *)
assert (HOW : forallb (fun q : Z * Z => forallb (fun p : Z * Z =>
((fst q + snd q <=? fst p) || (snd p <=? fst q))%bool) cmd_PG) Tfib_owned_static = true)
by (vm_compute; reflexivity).
assert (HER : forallb (fun p : Z * Z => ((snd p <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst p))%bool) cmd_PG = true)
by (vm_compute; reflexivity).
split.
- intros HE. rewrite Exists_exists in HE. destruct HE as (q & Hq & Hz). unfold in_zr in Hz.
  rewrite forallb_forall in HOW. specialize (HOW q Hq). rewrite forallb_forall in HOW. specialize (HOW r Hr).
  apply Bool.orb_prop in HOW as [H1 | H1]; apply Z.leb_le in H1; lia.
- rewrite forallb_forall in HER. specialize (HER r Hr).
  apply Bool.orb_prop in HER as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.
Lemma scn_pg_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> inFP cmd_PG a -> writable_at SEGS (mrestrict (w_H W) mem) a.
Proof.
intros ly S W mem md a _ Ha. exact (PROG_WRITABLE _ a Ha).
Qed.
(* the journal keeps every byte of the program's statics its footprint does not name *)
Lemma scn_pg_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP -> inFP cmd_PG a -> ~ inFP FP a ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a HJ Hcl Ha Hnf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (scn_pg_unowned a Ha) as [Hno He].
exact (F3 a (cif_prog_img a Ha) Hno He (fp_spares_closed FP a Hcl Hnf)).
Qed.
(* every byte range inside the call slot is addressable: the record's zero-shadow ranges
   [0xada00, 0x5e3b00) (which ends at the end of g_rec's body, where its ASan redzone starts) and
   [0x5e3be0, 0x5e3c18) (record.spill's body) cover the two cases (CmdZsh's cmd_addressable_in) *)
Lemma scn_slot_addressable : forall ly S (W : world SEGS) mem md c a n,
AR SEGS B ly S W mem md -> scn_slot c -> c <= a -> a + n <= c + CALL_SIZE ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md c a n HAR Hsl Ha Hn.
destruct Hsl as [(i & Hi & ->) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) a n HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right])
  | reflexivity | reflexivity
  | cbn [fst snd]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia
  | cbn [fst snd]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x38) a n HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right])
  | reflexivity | reflexivity
  | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE in *; lia
  | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE in *; lia].
Qed.

Lemma scn_obj0 : VAL (A_OBJ 0) = 0xa63f0.
Proof. exact (VOBJS 0%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.
Lemma scn_obj12 : VAL (A_OBJ 12) = 0xb10b8.
Proof. exact (VOBJS 12%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.
Lemma scn_obj42 : VAL (A_OBJ 42) = 0x21ce0.
Proof. exact (VOBJS 42%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.
Lemma scn_obj44 : VAL (A_OBJ 44) = A_G_REC.
Proof. exact (VOBJS 44%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.
Lemma scn_obj51 : VAL (A_OBJ 51) = A_REC_SPILL.
Proof. exact (VOBJS 51%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.
Lemma scn_obj52 : VAL (A_OBJ 52) = 0x22480.
Proof. exact (VOBJS 52%nat ltac:(apply Nat.ltb_lt; reflexivity)). Qed.

(* the seed of the walk at the entry 0x8ad20 *)
Lemma scn_entry : forall (W : world SEGS) ly S (regs : bvmap 5 word) mem md ch n,
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs scn_extra_e)) (scn_ss_e n)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_connect)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scn_Bx_e scn_SH_e (Eimg (Ereg regs scn_extra_e)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hncalls.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_CONNECT_STK = 16592) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs scn_extra_e)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SCN_SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof scn_obj0 as V0. pose proof scn_obj12 as V12. pose proof scn_obj44 as V44.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (HW : forall o, OFF_NCALLS <= o < OFF_NCALLS + 4 ->
writable_at SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 44) + o)).
{ intros o Ho. apply (scn_pg_writable ly S W mem md); [exact HAR|].
  rewrite V44. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
  cbn [fst snd]. unfold OFF_NCALLS in Ho. lia. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (VAL (A_OBJ 44))
(YP09.mkChunk OFF_NCALLS (CVal 4 (SLit n)))).
{ apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 44)) OFF_NCALLS 4 (SLit n) n);
  [reflexivity | cbn; lia | lia |].
  rewrite V44. exact (scn_val_mem_of_aval SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4 n Hncalls). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 scn_Bx_e SCN_SB);
    [cbn [sv_denot scn_Bx_e]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SCN_SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 80)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RN : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (scn_ncalls_region n)).
{ unfold region_ok, scn_ncalls_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E285) by (rewrite V44; unfold A_G_REC; lia).
  split; [rewrite V44; unfold A_G_REC, OFF_NCALLS; lia|].
  split; [rewrite V44; unfold A_G_REC, OFF_NCALLS; lia|].
  split; [exact HW|]. constructor; [exact CK | constructor]. }
assert (HG : facts_ok E scn_facts_e).
{ split; [|split; [exact I | exact I]].
  cbn [scn_facts_e f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold SCN_SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 FFS Hstk0. clear. unfold SCN_SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
split.
- unfold scn_ss_e. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold scn_regs_e. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
    constructor; [apply RG; right; left; reflexivity|]. constructor; [exact RN | constructor].
  + apply pairwise_disjoint_of_extents.
    unfold scn_regs_e, stack_region, got_regionP, bcell_regionP, scn_ncalls_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia).
    rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E285) by (rewrite V44; unfold A_G_REC; lia).
    cbn [base_val]. rewrite Usp, V0, V12, V44.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, A_G_REC, OFF_NCALLS. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. intros.
    repeat split; lia.
  + exact HG.
- unfold sh_ok, scn_SH_e. apply Forall_nil.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The two halves of the walk and what they hand over at the join 0x8adac.                            *)

Section s.
Variable MT : ameter_ops.
(* the statement pass fixes the read-only range (CmdGlob.v): the walk reads it only through these two *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the footprint of the statement (sup_connect_c.v:123-126) *)
Definition scn_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* a caller string in a live block, in the form the statement pass gives the line and the two ports
   (sup_connect_c.v:106-117: verbs_receive passes its strndup line and two words of its strdup copy, so the
   block form and not astr_argA) *)
Definition scn_blkarg ly S (rd : reader) (O : list (Z * Z)) (p : Z) (x : list byte) : Prop :=
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O /\
astr_atR rd p x /\ Z.of_nat (length x) + 1 <= LMAX + 1.
(* the same for an argument the walk also sees as NULL: the binary's null check at 0x8ae50 / 0x8ae9c has two
   arms, and the statement takes the Some arm of each port *)
Definition scn_sarg ly S (rd : reader) (O : list (Z * Z)) (p : Z) (v : option (list byte)) : Prop :=
match v with None => p = 0 | Some x => scn_blkarg ly S rd O p x end.
(* a string in a live block is a str_arg of the recorder's form, which is what xstrdup asks *)
Lemma scn_argA_of_blkarg : forall ly S (W : world SEGS) mem md rd O p x,
AR SEGS B ly S W mem md -> scn_blkarg ly S rd O p x ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S W mem md rd O p x HAR (Hbl & Hap & Hst & Hlen). cbn [astr_argA].
split; [|split; [exact Hst | split; [exact Hlen | left; split; [exact Hbl | exact Hap]]]].
destruct Hbl as (q & m & Hin & Hq & Hm).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & _). lia.
Qed.

(* the entry of the statement, premise for premise (sup_connect_c.v:84-121, statement passes 4 and 5: the
   rounding-mode-0 premise in astack_pres's old place), with the two ports left as the walk sees them: the
   statement hands Some, the binary checks for NULL *)
Definition scn_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch
(pv pl pa pb : Z) (verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte))
(R : rstate) (O : list (Z * Z)) (t : list byte) : Prop :=
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
Z.of_nat (length (frames S)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pv /\ 0 <= pv < 2 ^ 64 /\ getr regs 11 = w64 pl /\ 0 <= pl < 2 ^ 64 /\
getr regs 12 = w64 pa /\ 0 <= pa < 2 ^ 64 /\ getr regs 13 = w64 pb /\ 0 <= pb < 2 ^ 64 /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verb /\
(forall x, verb = Some x -> atail_vis SEGS W mem (pv + Z.of_nat (length x))) /\
scn_blkarg ly S (rdW W mem) O pl line /\
scn_sarg ly S (rdW W mem) O pa port_a /\
scn_sarg ly S (rdW W mem) O pb port_b /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_CONNECT R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_CONNECT verb line port_a port_b t <= LIVE_MAX /\
mo_ok MT S (XM_SUP_CONNECT MT R verb line port_a port_b t).

(* the post of the statement (sup_connect_c.v:122-143), conjunct for conjunct: apost_baseF, the FP-existential
   post (answer, the tail call, reaches the snprintf wrapper) *)
Definition scn_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md
(verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte))
(R : rstate) (O : list (Z * Z)) (t : list byte) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_CONNECT_STK (scn_FP O) regs ly S W mem md (EV_SUP_CONNECT R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_connect_m R verb line port_a port_b = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CONNECT verb line port_a port_b t /\
 mo_le MT S S' (XM_SUP_CONNECT MT R verb line port_a port_b t)).

(* the registers at the join: sp is 80 below the entry's, s0 is the call slot, s6 the shadow base, and
   s1, s3, s4, s5 the four arguments; gp, tp and s8..s11 are the entry's *)
Definition scn_regs_join (regs0 regsc : bvmap 5 word) (c : Z) : Prop :=
spZ regsc = spZ regs0 - 80 /\
getr regsc 8 = w64 c /\ getr regsc 22 = w64 SCN_SB /\
getr regsc 21 = getr regs0 10 /\ getr regsc 20 = getr regs0 11 /\
getr regsc 19 = getr regs0 12 /\ getr regsc 9 = getr regs0 13 /\
getr regsc 3 = getr regs0 3 /\ getr regsc 4 = getr regs0 4 /\
(forall r : Z, 24 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).

(* what the first half proves and the second half takes: record() has picked the slot c and, on the spill
   arm, freed the spill's old arguments. The slot's own 56 bytes are not yet written, so the recorder's
   state is handed over as the fact that ANY reader which differs from this one only inside the slot and
   holds `c->fn = REC_CONNECT` and `c->nargs = 0` is a recorder state for `rec_record R REC_CONNECT []`. *)
Definition scn_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc (k : Z) (c : Z) (O1 : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R /\
scn_slot c /\
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
 (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL) /\
scn_regs_join regs regsc c /\
scn_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
(forall rd', (forall a, ~ (c <= a < c + CALL_SIZE) -> rd' a = rdW Wc memc a) ->
 aval_mem rd' (c + CALL_OFF_FN) 4 REC_CONNECT -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
 rec_repA B lyc Sc rd' (rec_record R REC_CONNECT []) O1) /\
(forall pn, In pn O1 -> In pn O) /\
(forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) /\
(* a recorder block record() did not free is still the recorder's *)
(forall pn, In pn (ablocks B lyc Sc) -> In pn O -> In pn O1) /\
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
frames Sc = frames S /\ blocks_bytes Sc <= blocks_bytes S /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT).

(* the second half of the walk: from the join to the tail jump into answer, and on through answer's
   contract to sup_connect's post *)
Definition SCN_B_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O
lyc Sc Wc regsc memc mdc k c O1,
let t := snd (sup_connect_m R verb line port_a port_b) in
scn_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scn_mid ly S W regs mem md R O lyc Sc Wc regsc memc mdc k c O1 ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + SCN_JOIN)) memc (seg_rom SEGS)) mdc)
(scn_post ly S W regs mem md verb line port_a port_b R O t).

(* the four arguments the call records (sup_connect_m, RecModel.v:124-126) *)
Definition scn_args (verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte)) :
list (list byte) := [sarg verb; canon line; sarg port_a; sarg port_b].
(* the meter the four arguments spend, and their events *)
Definition XM_SCN_ARGS (R : rstate) (verb : option (list byte)) (line : list byte)
(port_a port_b : option (list byte)) : Z :=
rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line + XM_XSTRDUP MT (sarg port_a) +
XM_XSTRDUP MT (sarg port_b).
Definition EV_SCN_ARGS (R : rstate) : Z := rec_spill_frees R + EV_XSTRDUP + EV_ARG_LINE + EV_XSTRDUP + EV_XSTRDUP.
(* the live bytes they add *)
Definition LIVE_SCN_ARGS (verb : option (list byte)) (line : list byte)
(port_a port_b : option (list byte)) : Z :=
LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b).

(* the state at answer's entry, after the epilogue and `j answer` (0x8af0c): the frame is popped, so sp, ra,
   gp, tp and every callee-saved register are the entry's; a0 = the slot, a1 = the shape "resp 0", a2 = 1;
   the call (REC_CONNECT, scn_args ...) is recorded in the slot, with the four new blocks among the
   recorder's blocks Ot *)
Definition scn_tail ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z))
(verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte)) (t : list byte)
lyt St (Wt : world SEGS) (regst : bvmap 5 word) memt mdt (kt : Z) (c : Z) (Ot : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] lyt St Wt memt mdt kt /\
0 <= kt <= EV_SCN_ARGS R /\
spZ regst = spZ regs /\ getr regst 1 = getr regs 1 /\ aregs_preserved regs regst /\
getr regst 3 = w64 (as_gp B) /\ getr regst 4 = w64 (as_tp B) /\
getr regst 10 = w64 c /\ getr regst 11 = w64 0x21ce0 /\ getr regst 12 = w64 1 /\
achain lyt (rdW Wt memt) (spZ regst) (s0Z regst) ch /\
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
 (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL) /\
rec_repA B lyt St (rdW Wt memt) (rec_record R REC_CONNECT (scn_args verb line port_a port_b)) Ot /\
(forall pn, In pn Ot -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyt St) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Ot) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyt St)) /\
frames St = frames S /\
blocks_bytes St <= blocks_bytes S + LIVE_SCN_ARGS verb line port_a port_b /\
mo_le MT S St (XM_SCN_ARGS R verb line port_a port_b) /\
(* the guard cell answer's snprintf reads is not here: its GOT word 0xa7098 is runtime-owned, so no journal
   carries it; the tail gets it at its own state from the record (cmd_rec_cells) *)
arodata_okP SEGS RLO RHI B (rdW Wt memt) /\ cmd_ro_ok (rdW Wt memt).

(* the tail: answer's contract at that state gives sup_connect's post *)
Definition SCN_T_stmt : Prop :=
forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyt St Wt regst memt mdt kt c Ot,
let t := snd (sup_connect_m R verb line port_a port_b) in
scn_pre ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scn_tail ly S W regs mem md ch R O verb line port_a port_b t lyt St Wt regst memt mdt kt c Ot ->
SRr SEGS Wt (mkCfg (mkst regst (Z_to_bv 64 (BASE + AF_answer)) memt (seg_rom SEGS)) mdt)
(scn_post ly S W regs mem md verb line port_a port_b R O t).
End s.

End e.
End f.
End w.
