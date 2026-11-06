(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of sup_chain's ASan walk (plugin-hostd/fuzz_command, 0x8c2b4), in
   the form of lib/A/Prog/sup_reply_code_s1.v (the symbolic entry state and its seed) over
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cgif_close's seed, region and fact tables) at c8557374ad2e. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_chain_c RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the atoms the walk adds above the 32 registers: the shadow base, the call count g_rec.ncalls reads, and the
   slot the inlined record() picks *)
Definition SC_SB : nat := 32.
Definition SC_N : nat := 33.
Definition SC_C : nat := 34.
Definition SC_Bx : sv := SOff SC_SB 0.
Definition SC_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the object atoms of the listing this walk names: g_rec, record.spill, " %d", "%d", "chain" *)
Definition SC_GREC : nat := A_OBJ 44.
Definition SC_SPILL : nat := A_OBJ 51.
Definition SC_FMT_SP : nat := A_OBJ 71.
Definition SC_FMT : nat := A_OBJ 56.
Definition SC_VERB : nat := A_OBJ 72.
(* the frame of sup_chain: 112 bytes below the entry sp, written by the prologue *)
Definition SC_FRAME : Z := 112.
(* the program's own writable statics are RecBLemmas' recb_PG *)
(* the two zero-shadow ranges of the record that hold the recorder's globals: the one that ends at the end of
   g_rec, and record.spill's own (A/AF0m.v Tfib_zero_shadow, entries 133 and 134 of the regenerated table) *)
Definition SC_ZSH_REC : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition SC_ZSH_SPILL : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).

(* the slot the inlined record() picked: an entry of g_rec's call table, or record.spill *)
Definition sc_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < 16 /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma sc_slot_bounds : forall c, sc_slot_ok c ->
A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\ c mod 8 = 0.
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *.
- split; [lia|]. split; [lia|].
  replace (6174528 + 16 + 56 * i) with (8 * (771818 + 7 * i)) by lia.
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- split; [lia|]. split; [lia | reflexivity].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the regions of a segment of the walk: the frame, the two words that carry the shadow base, g_rec.ncalls, and
   (after the inlined record() picked it) the slot *)
Definition sc_stack : YP09.region := stack_region SC_FRAME.
Definition sc_ncalls : YP09.region :=
YP09.mkRegion (Some SC_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff SC_N 0))].
Definition sc_regions0 : smem := [sc_stack; got_regionP; bcell_regionP SC_SB; sc_ncalls].
Definition sc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SC_SB, mkAF SB SB 0); (SC_N, mkAF 0 16 0);
         (SC_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_sc0 : sstate := mkSS AF_sup_chain sr_atoms sc_regions0 None sc_facts0.
Definition sc_SH0 : list shent := [].
Definition sc_extra (n : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n].
Definition sc_E (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (sc_extra n)).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts about the program's own writable statics that the kit does not carry yet; each is a field
   of the coming lib/A/Prog/CmdRecFacts.v (its G_REC_UNOWNED item, cmd_prog_unowned, and the core's `ts_prog`) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis HB : CmdBSyms B.

Lemma sc_grec_val : VAL SC_GREC = A_G_REC.
Proof. unfold SC_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma sc_spill_val : VAL SC_SPILL = A_REC_SPILL.
Proof. unfold SC_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.


Lemma sc_in_zsh_of_existsb : forall r,
existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) Tfib_zero_shadow = true -> In r Tfib_zero_shadow.
Proof.
intros [x y] H. apply existsb_exists in H as ([u v] & Hin & He). cbn [fst snd] in He.
apply andb_true_iff in He as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. cbn in H1, H2. subst. exact Hin.
Qed.

Lemma sc_zsh_rec_in : In SC_ZSH_REC Tfib_zero_shadow.
Proof. apply sc_in_zsh_of_existsb. vm_compute. reflexivity. Qed.

Lemma sc_zsh_spill_in : In SC_ZSH_SPILL Tfib_zero_shadow.
Proof. apply sc_in_zsh_of_existsb. vm_compute. reflexivity. Qed.

(* every byte of g_rec is marked usable: the record's zero-shadow range covers it *)
Lemma sc_addr_rec : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0xada00 <= a -> a + n <= 0x5e3b00 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md SC_ZSH_REC a n HAR sc_zsh_rec_in
  ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

(* and every byte of record.spill *)
Lemma sc_addr_spill : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0x5e3be0 <= a -> a + n <= 0x5e3c18 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md SC_ZSH_SPILL a n HAR sc_zsh_spill_in
  ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

Lemma sc_slot_addressable : forall ly S (W : world SEGS) mem md c,
AR SEGS B ly S W mem md -> sc_slot_ok c -> range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(i & Hi & ->) | ->].
- apply (sc_addr_rec ly S W mem md);
  [exact HAR | unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; lia | unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; lia].
- apply (sc_addr_spill ly S W mem md);
  [exact HAR | unfold A_REC_SPILL, CALL_SIZE in *; lia | unfold A_REC_SPILL, CALL_SIZE in *; lia].
Qed.

Lemma sc_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma sc_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* the entry state of the walk: the prologue's frame, the GOT word and the shadow cell that carry the shadow
   base, and the one word of g_rec the inlined record() reads *)
Lemma sc_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md (n : Z),
AR SEGS B ly S W mem md ->
astk_ok SUP_CHAIN_STK ly (spZ regs) ->
(forall a, spZ regs - SUP_CHAIN_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (sc_E regs n) ss_sc0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_chain)) mem (seg_rom SEGS)))
/\ sh_ok SEGS SC_Bx sc_SH0 (sc_E regs n) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md n HAR Hstk Hpres HNC Hn.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as HO0. pose proof (pa_obj_img 12%nat ltac:(lia)) as HO12.
pose proof (pal_got_cell B TL) as Hgc.
set (E := sc_E regs n).
assert (HEI : img_env VAL A_LIM E) by (unfold E, sc_E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (unfold E, sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E SC_SB = Z_to_bv 64 SB)
  by (unfold E, sc_E, SC_SB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E SC_N = Z_to_bv 64 n)
  by (unfold E, sc_E, SC_N; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EG : ew E SC_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E SC_GREC HEI ltac:(unfold SC_GREC, A_OBJ, A_TEXT, A_LIM; lia)), sc_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (rewrite (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (rewrite (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| unfold sh_ok, sc_SH0; apply Forall_nil].
unfold ss_sc0, sc_regions0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, sc_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sc_stack, stack_region, got_regionP, bcell_regionP, sc_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [unfold SC_FRAME; lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold SC_FRAME in Ho. lia. }
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
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 SC_Bx SB);
    [cbn [sv_denot SC_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB SC_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md). exact HAR.
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff SC_N 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | zside | zside |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold sc_stack, stack_region, got_regionP, bcell_regionP, sc_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB SC_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp, V0, V12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SC_FRAME, A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [sc_facts0 f_atoms atoms_ok].
  split; [|split; [|split; [|split; [|exact I]]]].
  + assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity).
    apply (sc_afact E 2%nat (spZ regs));
    [exact E2' | lia | lia | change (2 ^ 4) with 16; exact Hal16 | lia].
  + apply (sc_afact E SC_SB SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (sc_afact E SC_N n); [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (sc_afact E SC_GREC A_G_REC);
    [exact EG | unfold A_G_REC; lia | lia | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
Qed.

End e.
End f.
End d.
