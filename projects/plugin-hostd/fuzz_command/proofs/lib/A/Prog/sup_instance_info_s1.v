(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states and seeds of sup_instance_info's ASan walk (plugin-hostd/fuzz_command), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed: the regions, facts and shadow entries of a walk segment and the proof that a machine state meets them) and lib/A/Prog/sup_reply_code_s1.v / RecBTemplate.v. *)

(* sup_instance_info (recorder.c:395-401, entry 0x8b5d8, 64 instructions) is walked in two segments:
   - segment A from the entry: the frame, the shadow base, g_rec.ncalls, and the branch of the inlined record()
     (the spill arm calls rec_calls_free on record.spill; the slot arm bumps g_rec.ncalls) up to 0x8b644;
   - segment B from 0x8b644 (SII_JOIN): the two checked stores of the slot c (fn, nargs), arg_i, rec_shape_of,
     the epilogue and the tail jump to answer.
   Segment B is seeded afresh from the facts both arms leave (`sii_seedB`), so its walk is done once. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c rec_shape_of_c answer_c sup_instance_info_c.
(* recb_PG, the program's writable statics as (start, length) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the member's offsets in the listing *)
Definition SII_FRAME : Z := 32.
Definition SII_RCF_RET : Z := AF_sup_instance_info + 0x4c.   (* after the call of rec_calls_free (0x8b624) *)
Definition SII_JOIN : Z := AF_sup_instance_info + 0x6c.      (* the arms meet (0x8b644) *)
Definition SII_ARGI_RET : Z := AF_sup_instance_info + 0xa8.  (* after the call of arg_i (0x8b680) *)
Definition SII_SHP_RET : Z := AF_sup_instance_info + 0xb8.   (* after the call of rec_shape_of (0x8b690) *)

(* the slot record() picks: an entry of g_rec's table, or record.spill *)
Definition sii_slot (n : Z) : Z := if n <? 16 then A_G_REC + OFF_CALLS + CALL_SIZE * n else A_REC_SPILL.
Definition sii_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma sii_slot_ok_of : forall n, 0 <= n <= 16 -> sii_slot_ok (sii_slot n).
Proof.
intros n Hn. unfold sii_slot, sii_slot_ok. destruct (Z.ltb_spec n 16); [left; exists n; unfold REC_CALLS_MAX; split; [lia | reflexivity] | right; reflexivity].
Qed.

Lemma sii_slot_bounds : forall c, sii_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *.
- split; [lia|]. split; [|left; lia].
  apply Z.mod_divide; [lia|]. exists (771818 + 7 * i). lia.
- split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

Lemma sii_in_PG : forall c a, sii_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. apply Exists_exists. destruct (sii_slot_bounds c Hc) as (_ & _ & [Hb | ->]).
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity|]. unfold in_zr. cbn [fst snd].
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE in *. lia.
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity|]. unfold in_zr. cbn [fst snd].
  unfold CALL_SIZE, SC_SIZE in *. lia.
Qed.

Lemma sii_in_zsh : forall r, existsb (fun x => (fst x =? fst r) && (snd x =? snd r)) AF0m.Tfib_zero_shadow = true ->
In r AF0m.Tfib_zero_shadow.
Proof.
intros r H. apply existsb_exists in H as (x & Hx & E). apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. destruct x as [x1 x2], r as [r1 r2]. cbn in E1, E2. subst. exact Hx.
Qed.

(* the verb rec_shape_of is handed: the 13 bytes of the literal .str.7 at 0x21da0 (CmdRo.v's RO_lit_21da0 less its NUL) *)
Definition sii_verb : list byte := map (Z_to_bv 8) [105; 110; 115; 116; 97; 110; 99; 101; 95; 105; 110; 102; 111].
Lemma sii_verb_lit : sii_verb ++ [Z_to_bv 8 0] = RO_lit_21da0.
Proof. vm_compute. reflexivity. Qed.
Lemma sii_verb_bstr : bstr "instance_info"%string = sii_verb.
Proof. vm_compute. reflexivity. Qed.
Lemma sii_verb_len : Z.of_nat (length sii_verb) = 13.
Proof. reflexivity. Qed.
Lemma sii_abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity.
Qed.

(* --- segment A: the entry ----------------------------------------------------------------------------- *)

(* atoms above the registers: 32 the shadow base, 33 g_rec.ncalls *)
Definition sii_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition sii_rsA : smem := [stack_region SII_FRAME; got_regionP; bcell_regionP 32; sii_ncalls].
Definition sii_factsA : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 16 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_siiA : sstate := mkSS AF_sup_instance_info sr_atoms sii_rsA None sii_factsA.
Definition sii_BxA : sv := SOff 32 0.
Definition sii_SHA : list shent := [].
Definition sii_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sii_extraA (n : Z) : list word := map (Z_to_bv 64) [SB; n].

(* --- segment B: from SII_JOIN ------------------------------------------------------------------------ *)

(* atoms above the registers: 32..35 the entry's ra, s0, s1, s2, which the frame holds at sp + 24, 16, 8, 0 *)
Definition sii_frameB : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 SII_FRAME 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition sii_slotB : YP09.region := YP09.mkRegion (Some 8%nat) 0 CALL_SIZE 0 8 [].
Definition sii_rsB : smem := [sii_frameB; sii_slotB].
Definition sii_factsB : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF SB SB 0);
         (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
Definition ss_siiB : sstate := mkSS SII_JOIN sr_atoms sii_rsB None sii_factsB.
(* the state at 0x8b680, after the call of arg_i (pass 4: arg_i returns at its own FP state, so the walk seeds the
   symbolic state afresh there): the frame only *)
Definition ss_siiC : sstate := mkSS SII_ARGI_RET sr_atoms [sii_frameB] None sii_factsB.
Definition sii_BxB : sv := SOff 18 0.
Definition sii_SHB : list shent := [mkSHE 8 0 CALL_SIZE].

(* the entry's ra, s0, s1, s2 in the frame of segment B, the order of sii_frameB's atoms *)
Definition sii_frvals (regs : bvmap 5 word) : list word := [getr regs 1; getr regs 8; getr regs 9; getr regs 18].
Definition sii_frame (segs : list Segment) (m : word -> option byte) (sp1 : Z) (regs : bvmap 5 word) : Prop :=
val_mem segs m (sp1 + 24) 8 (bv_unsigned (getr regs 1)) /\ val_mem segs m (sp1 + 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem segs m (sp1 + 8) 8 (bv_unsigned (getr regs 9)) /\ val_mem segs m (sp1 + 0) 8 (bv_unsigned (getr regs 18)).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sii_EA (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (sii_extraA n)).
Definition sii_EB (regs1 : bvmap 5 word) (fr : list word) : env := Eimg (Ereg regs1 fr).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
(* PROG_PRESENT, in the template's form *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md ->
Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma sii_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sii_spill_val : VAL (A_OBJ 51) = A_REC_SPILL.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sii_lit_val : VAL (A_OBJ 63) = 0x21da0.
Proof. rewrite (VOBJS 63%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sii_got_val : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sii_cell_val : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the slot's 56 bytes are marked usable: g_rec and record.spill lie in two zero-shadow ranges of the record *)
Lemma sii_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sii_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct (sii_slot_bounds c Hc) as (_ & _ & [Hb | ->]).
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) c CALL_SIZE HAR
    ltac:(apply sii_in_zsh; vm_compute; reflexivity) ltac:(reflexivity) ltac:(reflexivity));
  cbn [fst snd]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL CALL_SIZE HAR
    ltac:(apply sii_in_zsh; vm_compute; reflexivity) ltac:(reflexivity) ltac:(reflexivity));
  cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia.
Qed.

Lemma sii_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma sii_seedA : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n,
AR SEGS B ly S W mem md ->
astk_ok SUP_INSTANCE_INFO_STK ly (spZ regs) ->
(forall a, spZ regs - SUP_INSTANCE_INFO_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (sii_EA regs n) ss_siiA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_instance_info)) mem (seg_rom SEGS))) /\
sh_ok SEGS sii_BxA sii_SHA (sii_EA regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n HAR Hstk Hpres HNC Hn.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_INSTANCE_INFO_STK = 16592) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof sii_got_val as HO0. pose proof sii_cell_val as HO12.
split; [|unfold sh_ok, sii_SHA; apply Forall_nil].
rewrite restrict_mkst_fx.
set (E := sii_EA regs n).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold sii_EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold sii_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ subst E. unfold sii_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ subst E. unfold sii_EA. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite sii_grec_val. reflexivity. }
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U44 : base_val E (Some (A_OBJ 44)) = A_G_REC) by (apply VB; [exact E285 | unfold A_G_REC; lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_siiA. apply pa_entry_st_ok_full.
- subst E. unfold sii_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sii_rsA, stack_region, got_regionP, bcell_regionP, sii_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U2. unfold SII_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite U44. split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|]. split.
    * intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply Exists_exists.
      exists (A_G_REC, REC_SIZE). split; [left; reflexivity|]. unfold in_zr, A_G_REC, REC_SIZE, OFF_NCALLS in *. cbn [fst snd]. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      exact (val_mem_view SEGS (w_H W) mem _ 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold sii_rsA, stack_region, got_regionP, bcell_regionP, sii_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U0, U12, U44.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HO0, HO12. unfold SII_FRAME, A_G_REC, OFF_NCALLS in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [sii_factsA f_atoms atoms_ok].
  split; [apply (sii_afact E 2%nat (spZ regs)); [rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | change (2 ^ 4) with 16; exact Hal16 | lia]|].
  split; [apply (sii_afact E 32%nat SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (sii_afact E 33%nat n); [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (sii_afact E (A_OBJ 44) A_G_REC); [exact E285 | unfold A_G_REC; lia | lia | reflexivity | lia]|].
  exact I.
Qed.

Lemma sii_sh_okB : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> sii_slot_ok c ->
ew E 18 = Z_to_bv 64 SB -> ew E 8 = Z_to_bv 64 c ->
sh_ok SEGS sii_BxB sii_SHB E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hc E18 E8.
destruct (sii_slot_bounds c Hc) as (Hcb & Hc8 & _).
unfold sh_ok, sii_SHB. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E sii_BxB 8 c CALL_SIZE c 0 CALL_SIZE).
- exact (sii_slot_addressable ly S W mem md c HAR Hc).
- unfold sii_BxB. apply U_atom; [exact E18 | cbv [SB SHADOW_OFF]; lia].
- apply U_atom; [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

Lemma sii_seedB : forall ly S (W : world SEGS) mem md (regs1 : bvmap 5 word) (fr : list word) sp1 c,
AR SEGS B ly S W mem md ->
bv_unsigned (getr regs1 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
getr regs1 8 = Z_to_bv 64 c -> sii_slot_ok c -> getr regs1 18 = Z_to_bv 64 SB ->
length fr = 4%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned (nth 0 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 16) 8 (bv_unsigned (nth 1 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 8) 8 (bv_unsigned (nth 2 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 0) 8 (bv_unsigned (nth 3 fr (Z_to_bv 64 0))) ->
st_ok_pi SEGS VAL (sii_EB regs1 fr) ss_siiB
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + SII_JOIN)) mem (seg_rom SEGS))) /\
sh_ok SEGS sii_BxB sii_SHB (sii_EB regs1 fr) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 fr sp1 c HAR Hsp Hsp1 Hsp16 H8 Hc H18 Hfr F24 F16 F8 F0.
destruct (sii_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (E := sii_EB regs1 fr).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold sii_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = nth 0 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 0)).
assert (X33 : ew E 33 = nth 1 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 1)).
assert (X34 : ew E 34 = nth 2 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 2)).
assert (X35 : ew E 35 = nth 3 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 3)).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp).
assert (U8 : base_val E (Some 8%nat) = c).
{ cbn [base_val]. rewrite E8. apply unsigned_lit_small. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia. }
assert (U2 : base_val E (Some 2%nat) = sp1) by (cbn [base_val]; exact Usp).
split; [|exact (sii_sh_okB ly S W mem md E c HAR Hc E18 E8)].
rewrite restrict_mkst_fx. unfold ss_siiB. apply pa_entry_st_ok_full.
- subst E. unfold sii_EB. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sii_rsB, sii_frameB, sii_slotB.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U2. unfold SII_FRAME. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    pose proof (bv_unsigned_in_range 64 (nth 0 fr (Z_to_bv 64 0))) as R0.
    pose proof (bv_unsigned_in_range 64 (nth 1 fr (Z_to_bv 64 0))) as R1.
    pose proof (bv_unsigned_in_range 64 (nth 2 fr (Z_to_bv 64 0))) as R2.
    pose proof (bv_unsigned_in_range 64 (nth 3 fr (Z_to_bv 64 0))) as R3.
    change (bv_modulus 64) with (2 ^ 64) in R0, R1, R2, R3.
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 32 0) (bv_unsigned (nth 0 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X32, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F24].
    * apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 33 0) (bv_unsigned (nth 1 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X33, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F16].
    * apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 34 0) (bv_unsigned (nth 2 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X34, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F8].
    * apply (chunk_ok_val SEGS E _ sp1 0 8 (SOff 35 0) (bv_unsigned (nth 3 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X35, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F0].
  + rewrite U8. unfold CALL_SIZE. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply (sii_in_PG c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents.
  unfold sii_rsB, sii_frameB, sii_slotB, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SII_FRAME, CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [sii_factsB f_atoms atoms_ok].
  split; [apply (sii_afact E 2%nat sp1); [rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia]|].
  split; [apply (sii_afact E 18%nat SB); [exact E18 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (sii_afact E 8%nat c); [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia]|].
  exact I.
Qed.

Lemma sii_seedC : forall ly S (W : world SEGS) mem md (regs1 : bvmap 5 word) (fr : list word) sp1 c,
AR SEGS B ly S W mem md ->
bv_unsigned (getr regs1 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
getr regs1 8 = Z_to_bv 64 c -> sii_slot_ok c -> getr regs1 18 = Z_to_bv 64 SB ->
length fr = 4%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned (nth 0 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 16) 8 (bv_unsigned (nth 1 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 8) 8 (bv_unsigned (nth 2 fr (Z_to_bv 64 0))) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 0) 8 (bv_unsigned (nth 3 fr (Z_to_bv 64 0))) ->
st_ok_pi SEGS VAL (sii_EB regs1 fr) ss_siiC
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + SII_ARGI_RET)) mem (seg_rom SEGS))) /\
sh_ok SEGS sii_BxB sii_SHB (sii_EB regs1 fr) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 fr sp1 c HAR Hsp Hsp1 Hsp16 H8 Hc H18 Hfr F24 F16 F8 F0.
destruct (sii_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (E := sii_EB regs1 fr).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold sii_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = nth 0 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 0)).
assert (X33 : ew E 33 = nth 1 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 1)).
assert (X34 : ew E 34 = nth 2 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 2)).
assert (X35 : ew E 35 = nth 3 fr (Z_to_bv 64 0)) by (subst E; unfold sii_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fr 3)).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp).
assert (U8 : base_val E (Some 8%nat) = c).
{ cbn [base_val]. rewrite E8. apply unsigned_lit_small. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia. }
assert (U2 : base_val E (Some 2%nat) = sp1) by (cbn [base_val]; exact Usp).
split; [|exact (sii_sh_okB ly S W mem md E c HAR Hc E18 E8)].
rewrite restrict_mkst_fx. unfold ss_siiC. apply pa_entry_st_ok_full.
- subst E. unfold sii_EB. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sii_frameB.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U2. unfold SII_FRAME. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    pose proof (bv_unsigned_in_range 64 (nth 0 fr (Z_to_bv 64 0))) as R0.
    pose proof (bv_unsigned_in_range 64 (nth 1 fr (Z_to_bv 64 0))) as R1.
    pose proof (bv_unsigned_in_range 64 (nth 2 fr (Z_to_bv 64 0))) as R2.
    pose proof (bv_unsigned_in_range 64 (nth 3 fr (Z_to_bv 64 0))) as R3.
    change (bv_modulus 64) with (2 ^ 64) in R0, R1, R2, R3.
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 32 0) (bv_unsigned (nth 0 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X32, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F24].
    * apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 33 0) (bv_unsigned (nth 1 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X33, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F16].
    * apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 34 0) (bv_unsigned (nth 2 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X34, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F8].
    * apply (chunk_ok_val SEGS E _ sp1 0 8 (SOff 35 0) (bv_unsigned (nth 3 fr (Z_to_bv 64 0))));
      [cbn [sv_denot]; rewrite X35, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact F0].
- apply pairwise_disjoint_of_extents.
  unfold sii_frameB, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2.
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [sii_factsB f_atoms atoms_ok].
  split; [apply (sii_afact E 2%nat sp1); [rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia]|].
  split; [apply (sii_afact E 18%nat SB); [exact E18 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (sii_afact E 8%nat c); [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia]|].
  exact I.
Qed.
End e.
End f.
End d.
