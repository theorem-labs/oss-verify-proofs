(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states of pins_clear's ASan walk on plugin-hostd/fuzz_command,
   after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed / cl_seed_entry of the cgif_close walk) over
   fuzz_command's listing. *)

(* pins_clear (recorder.c:524-533, entry 0x8ccb4) walks in two segments:

   - the entry segment, from the entry to the test of g_rec.ncalls against 16 (0x8ccf4). Its regions are the
     64-byte frame, the two words that carry the shadow base (the GOT cell 0xa63f0 and the cell it points to) and
     g_rec.ncalls.
   - the join segment, from the point where the two arms of record() meet (0x8cd2c) to the tail jump into
     answer_code. Its regions are the frame with the saved registers, the slot the call was recorded in (either
     g_rec.calls[ncalls] or record.spill, as the atom `PCL_C`), and the two parts of g_rec the rest of the body
     reads or writes: refuse/code, and state.

   The slot is the one range the inline checks look at; the shadow entry `PCL_SH` covers it, so each of the four
   checks reads a shadow byte the executor already knows is zero and the error path falls away with no
   obligation. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdZsh RecBLemmas pins_clear_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of the walk's segments in the listing (M, the disassembly of pins_clear) *)
Definition PCL_FRAME : Z := 64.
Definition PCL_BR : Z := AF_pins_clear + 0x40.       (* bne a1,a2: ncalls against 16 *)
Definition PCL_SPILL : Z := AF_pins_clear + 0x44.    (* the spill arm *)
Definition PCL_RET_RCF : Z := AF_pins_clear + 0x58.  (* after the call of rec_calls_free *)
Definition PCL_SLOT : Z := AF_pins_clear + 0x5c.     (* the table arm *)
Definition PCL_JOIN : Z := AF_pins_clear + 0x78.     (* the two arms meet *)
Definition PCL_ARGBR : Z := AF_pins_clear + 0xa8.    (* bnez s1: the NULL argument's default *)
Definition PCL_DFLT : Z := AF_pins_clear + 0xac.     (* the default "(null)" *)
Definition PCL_ARG : Z := AF_pins_clear + 0xb4.      (* the call of xstrdup *)
Definition PCL_RETX : Z := AF_pins_clear + 0xbc.     (* after it *)
Definition PCL_REFBR : Z := AF_pins_clear + 0xf4.    (* beqz a2: g_rec.refuse *)
Definition PCL_REF : Z := AF_pins_clear + 0xf8.      (* the refusing arm *)
Definition PCL_MIX : Z := AF_pins_clear + 0x100.     (* the mixing arm *)
Definition PCL_RETM : Z := AF_pins_clear + 0x10c.    (* after the call of mix_call *)

(* the atoms the walk adds above the 32 registers *)
Definition PCL_SB : nat := 32.      (* the shadow base *)
Definition PCL_N : nat := 33.       (* g_rec.ncalls at the entry *)
Definition PCL_C : nat := 34.       (* the slot the call is recorded in *)
Definition PCL_RA : nat := 35.      (* the caller's ra and callee-saved registers, as the frame holds them *)
Definition PCL_S0 : nat := 36.
Definition PCL_S1 : nat := 37.
Definition PCL_S2 : nat := 38.
Definition PCL_S3 : nat := 39.
Definition PCL_S4 : nat := 40.
Definition PCL_S5 : nat := 41.
Definition PCL_RF : nat := 42.      (* g_rec.refuse and g_rec.code, as 32-bit words *)
Definition PCL_CD : nat := 43.
Definition PCL_ST : nat := 44.      (* g_rec.state *)
(* the listing's object atoms: g_rec, record.spill, the default "(null)" *)
Definition PCL_GR : nat := A_OBJ 44.
Definition PCL_SP : nat := A_OBJ 51.
Definition PCL_LIT : nat := A_OBJ 52.
Definition A_LIT_NULL : Z := 0x22480.

Definition Bxp : sv := SOff PCL_SB 0.
Definition PCL_SH : list shent := [mkSHE PCL_C 0 CALL_SIZE].
Definition PCL_SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* the slot: an entry of g_rec's table, or record.spill *)
Definition pcl_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma pcl_slot_bounds : forall c, pcl_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
(c + CALL_SIZE <= A_G_REC + OFF_ANSWER \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->].
- unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, OFF_ANSWER, REC_CALLS_MAX in *.
  split; [lia|]. split; [|lia].
  replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia.
  rewrite Z_mod_mult. reflexivity.
- unfold A_G_REC, A_REC_SPILL, OFF_CALLS. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

(* the entry segment's regions: the frame, the two shadow-base words, and g_rec.ncalls *)
Definition pcl_ncalls : YP09.region :=
YP09.mkRegion (Some PCL_GR) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff PCL_N 0))].
Definition pcl_rs_e : YP09.smem := [stack_region PCL_FRAME; got_regionP; bcell_regionP PCL_SB; pcl_ncalls].
Definition pcl_facts_e : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (PCL_SB, mkAF SB SB 0); (PCL_N, mkAF 0 16 0);
         (PCL_GR, mkAF A_G_REC A_G_REC 3)] [] [].
Definition pcl_ss_e : sstate := mkSS AF_pins_clear sr_atoms pcl_rs_e None pcl_facts_e.
Definition pcl_extra_e (n : Z) : list word := map (Z_to_bv 64) [SB; n].

(* the join segment's regions and facts *)
Definition pcl_stack_j : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 PCL_FRAME 0 PCL_FRAME
 [YP09.mkChunk 8 (CVal 8 (SOff PCL_S5 0)); YP09.mkChunk 16 (CVal 8 (SOff PCL_S4 0));
  YP09.mkChunk 24 (CVal 8 (SOff PCL_S3 0)); YP09.mkChunk 32 (CVal 8 (SOff PCL_S2 0));
  YP09.mkChunk 40 (CVal 8 (SOff PCL_S1 0)); YP09.mkChunk 48 (CVal 8 (SOff PCL_S0 0));
  YP09.mkChunk 56 (CVal 8 (SOff PCL_RA 0))].
Definition pcl_slot : YP09.region := YP09.mkRegion (Some PCL_C) 0 CALL_SIZE 0 CALL_SIZE [].
Definition pcl_grec_lo : YP09.region :=
YP09.mkRegion (Some PCL_GR) 0 8 0 0
 [YP09.mkChunk OFF_REFUSE (CVal 4 (SOff PCL_RF 0)); YP09.mkChunk OFF_CODE (CVal 4 (SOff PCL_CD 0))].
Definition pcl_grec_st : YP09.region :=
YP09.mkRegion (Some PCL_GR) OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8)
 [YP09.mkChunk OFF_STATE (CVal 8 (SOff PCL_ST 0))].
Definition pcl_rs_j : YP09.smem := [pcl_stack_j; pcl_slot; pcl_grec_lo; pcl_grec_st].
Definition pcl_facts_j : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - PCL_FRAME) (2 ^ 47) 4); (PCL_SB, mkAF SB SB 0);
         (PCL_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (PCL_GR, mkAF A_G_REC A_G_REC 3)] [] [].
Definition pcl_regs_j : list sv := Eval vm_compute in
sr_set (sr_set (sr_set sr_atoms 8%bv (SOff PCL_C 0)) 19%bv (SOff PCL_GR 0)) 20%bv (SOff PCL_SB 0).
Definition pcl_ss_j : sstate := mkSS PCL_JOIN pcl_regs_j pcl_rs_j None pcl_facts_j.
Definition pcl_extra_j (c ra s0 s1 s2 s3 s4 s5 rf cd st : Z) : list word :=
map (Z_to_bv 64) [SB; 0; c; ra; s0; s1; s2; s3; s4; s5; rf; cd; st].

(* the program's writable statics (lib/A/Prog/RecBLemmas.v recb_PG) carry g_rec and record.spill *)

Lemma pcl_in_PG_slot : forall c a, pcl_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a [(i & Hi & ->) | ->] Ha.
- apply recb_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, REC_CALLS_MAX in *. lia.
- apply recb_spill_in. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.


Lemma pcl_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. vm_compute. reflexivity. Qed.
Lemma pcl_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. vm_compute. reflexivity. Qed.
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
(* the per-binary facts about the program's writable statics, with the statements' names
   (shared by every recorder walk): every byte of g_rec / record.spill / g_quitting is in the image and present *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma pcl_grec_val : VAL PCL_GR = A_G_REC.
Proof. unfold PCL_GR. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma pcl_spill_val : VAL PCL_SP = A_REC_SPILL.
Proof. unfold PCL_SP. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma pcl_lit_val : VAL PCL_LIT = A_LIT_NULL.
Proof. unfold PCL_LIT. rewrite (VOBJS 52%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the slot of g_rec or record.spill is addressable: g_rec [0x5e3740, 0x5e3b00) lies in the record's zero-shadow
   range of the image's .bss (lib/A/AF0m.v), and record.spill [0x5e3be0, 0x5e3c18) is a zero-shadow range of its
   own *)
Lemma pcl_in_zz : forall (x : Z * Z) l,
existsb (fun y => (fst y =? fst x) && (snd y =? snd x)) l = true -> In x l.
Proof.
intros x l H. apply existsb_exists in H as (y & Hy & E). apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. destruct x as [x1 x2], y as [y1 y2]. cbn in E1, E2.
subst. exact Hy.
Qed.

Lemma pcl_zsh_bss : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow.
Proof. apply pcl_in_zz. vm_compute. reflexivity. Qed.

Lemma pcl_zsh_spill : In (0x5e3be0, 0x5e3c18 - 0x5e3be0) Tfib_zero_shadow.
Proof. apply pcl_in_zz. vm_compute. reflexivity. Qed.

Lemma pcl_addressable_bss : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0xada00 <= a -> a + n <= 0x5e3b00 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) a n HAR
  pcl_zsh_bss ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

Lemma pcl_addressable_spill : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0x5e3be0 <= a -> a + n <= 0x5e3c18 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) a n HAR
  pcl_zsh_spill ltac:(reflexivity) ltac:(reflexivity) Hlo Hhi).
Qed.

Lemma pcl_slot_addressable : forall ly S (W : world SEGS) mem md c,
AR SEGS B ly S W mem md -> pcl_slot_ok c -> range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(i & Hi & ->) | ->].
- apply (pcl_addressable_bss ly S W mem md);
  [exact HAR | unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia
  | unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia].
- apply (pcl_addressable_spill ly S W mem md);
  [exact HAR | unfold A_REC_SPILL; lia | unfold A_REC_SPILL, CALL_SIZE; lia].
Qed.

Lemma pcl_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma pcl_sh_ok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> pcl_slot_ok c ->
ew E PCL_SB = Z_to_bv 64 SB -> ew E PCL_C = Z_to_bv 64 c ->
sh_ok SEGS Bxp PCL_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hc ESB EC.
destruct (pcl_slot_bounds c Hc) as (Hcb & _ & _).
unfold sh_ok, PCL_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bxp PCL_C c CALL_SIZE c 0 CALL_SIZE).
- exact (pcl_slot_addressable ly S W mem md c HAR Hc).
- unfold Bxp. apply pcl_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply pcl_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* --- the entry segment's seed ------------------------------------------------------------------------- *)

Lemma pcl_seed_entry : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - PCL_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 -> aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (pcl_extra_e n))) pcl_ss_e
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pins_clear)) mem (seg_rom SEGS))).
Proof.
intros ly S W mem md regs n HAR Hsp Hsp16 Hpres Hn HNC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := Eimg (Ereg regs (pcl_extra_e n))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E2 : ew E 2%nat = getr regs 2)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E PCL_SB = Z_to_bv 64 SB)
  by (unfold E, PCL_SB; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E PCL_N = Z_to_bv 64 n)
  by (unfold E, PCL_N; change 33%nat with (32 + 1)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs _ 1)).
assert (EGR : ew E PCL_GR = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E PCL_GR HEI ltac:(unfold PCL_GR, A_OBJ, A_TEXT, A_LIM; lia)), pcl_grec_val;
      reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0)
  by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8)
  by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
  by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
assert (E2' : ew E 2%nat = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Usp : bv_unsigned (ew E 2%nat) = spZ regs) by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pcl_rs_e, stack_region, got_regionP, bcell_regionP, pcl_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat (spZ regs) E2' ltac:(lia)). unfold PCL_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold PCL_FRAME. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite pcl_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxp SHADOW_OFF);
    [cbn [sv_denot Bxp]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite pcl_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB PCL_GR A_G_REC EGR) by (unfold A_G_REC; lia).
    unfold OFF_NCALLS. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff PCL_N 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite pcl_pow4; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold pcl_rs_e, stack_region, got_regionP, bcell_regionP, pcl_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB PCL_GR A_G_REC EGR) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat (spZ regs) ltac:(rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity))
    by lia.
  rewrite EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PCL_FRAME, A_G_REC, OFF_NCALLS in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pcl_facts_e f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, EGR, !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 3) with 8. unfold SB, A_G_REC.
  repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; try lia.
Qed.

(* --- the join segment's seed ----------------------------------------------------------------------- *)

(* the caller's ra and callee-saved registers, where the prologue put them, over the current sp *)
Definition pcl_frame_at (rd : reader) (spc vra v0 v1 v2 v3 v4 v5 : Z) : Prop :=
aval_mem rd (spc + 8) 8 v5 /\ aval_mem rd (spc + 16) 8 v4 /\ aval_mem rd (spc + 24) 8 v3 /\
aval_mem rd (spc + 32) 8 v2 /\ aval_mem rd (spc + 40) 8 v1 /\ aval_mem rd (spc + 48) 8 v0 /\
aval_mem rd (spc + 56) 8 vra /\
0 <= vra < 2 ^ 64 /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 /\ 0 <= v2 < 2 ^ 64 /\ 0 <= v3 < 2 ^ 64 /\
0 <= v4 < 2 ^ 64 /\ 0 <= v5 < 2 ^ 64.

(* What record()'s two arms leave when they meet at 0x8cd2c, in one predicate: the slot the call will be written
   into, the allocator events the arm spent, and how the memory and the blocks differ from the entry.
   - the table arm (fewer than 16 calls): the slot is g_rec.calls[ncalls], g_rec.ncalls now holds ncalls + 1,
     every other byte of g_rec and all of record.spill are kept, and no block changed.
   - the spill arm (16 calls): the slot is record.spill, rec_calls_free freed the arguments the spill held and
     zeroed its argument count, g_rec is kept, and the blocks it freed are gone. *)
Definition pcl_at_join (ly S : _) (W : world SEGS) (mem : word -> option byte)
(R : rstate) (sp : list (Z * Z)) (lyc Sc : _) (Wc : world SEGS) (memc : word -> option byte) (c k : Z) : Prop :=
((length (r_calls R) < 16)%nat /\
 c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\ k = 0 /\
 ablocks B lyc Sc = ablocks B ly S /\
 aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
 (forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW Wc memc a = rdW W mem a) /\
 (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rdW Wc memc a = rdW W mem a) /\
 (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW Wc memc (p + i) = rdW W mem (p + i)))
\/
(length (r_calls R) = 16%nat /\ c = A_REC_SPILL /\ k = Z.of_nat (length sp) /\
 Permutation (ablocks B ly S) (ablocks B lyc Sc ++ sp) /\
 aval_mem (rdW Wc memc) (A_REC_SPILL + CALL_OFF_NARGS) 4 0 /\
 (forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW Wc memc a = rdW W mem a) /\
 (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
    ~ (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) ->
    rdW Wc memc a = rdW W mem a) /\
 (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW Wc memc (p + i) = rdW W mem (p + i))).

Lemma pcl_seed_join : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) c vra v0 v1 v2 v3 v4 v5 rf cd st,
AR SEGS B ly S W mem md -> pcl_slot_ok c ->
2 ^ 46 - PCL_FRAME <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
getr regs 8 = w64 c -> getr regs 19 = w64 A_G_REC -> getr regs 20 = w64 SB ->
(forall a, spZ regs <= a < spZ regs + PCL_FRAME -> apresent (w_H W) mem a) ->
pcl_frame_at (rdW W mem) (spZ regs) vra v0 v1 v2 v3 v4 v5 ->
aval_mem (rdW W mem) (A_G_REC + OFF_REFUSE) 4 rf -> 0 <= rf < 2 ^ 32 ->
aval_mem (rdW W mem) (A_G_REC + OFF_CODE) 4 cd -> 0 <= cd < 2 ^ 32 ->
aval_mem (rdW W mem) (A_G_REC + OFF_STATE) 8 st -> 0 <= st < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (pcl_extra_j c vra v0 v1 v2 v3 v4 v5 rf cd st))) pcl_ss_j
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PCL_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxp PCL_SH (Eimg (Ereg regs (pcl_extra_j c vra v0 v1 v2 v3 v4 v5 rf cd st)))
     (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs c vra v0 v1 v2 v3 v4 v5 rf cd st HAR Hc Hsp Hsp16 R8 R19 R20 Hpres HFR
  Vrf Rrf Vcd Rcd Vst Rst.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pcl_slot_bounds c Hc) as (Hcb & Hc8 & Hcf).
pose proof HFR as (F5 & F4 & F3 & F2 & F1 & F0 & FRA & Dra & D0 & D1 & D2 & D3 & D4 & D5).
unfold PCL_FRAME in *.
set (E := Eimg (Ereg regs (pcl_extra_j c vra v0 v1 v2 v3 v4 v5 rf cd st))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EX : forall j, (j < 13)%nat ->
  ew E (32 + j)%nat = nth j (pcl_extra_j c vra v0 v1 v2 v3 v4 v5 rf cd st) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32%nat = Z_to_bv 64 SB)
  by (change 32%nat with (32 + 0)%nat; rewrite (EX 0%nat ltac:(lia)); reflexivity).
assert (E34 : ew E 34%nat = Z_to_bv 64 c)
  by (change 34%nat with (32 + 2)%nat; rewrite (EX 2%nat ltac:(lia)); reflexivity).
assert (E35 : ew E 35%nat = Z_to_bv 64 vra)
  by (change 35%nat with (32 + 3)%nat; rewrite (EX 3%nat ltac:(lia)); reflexivity).
assert (E36 : ew E 36%nat = Z_to_bv 64 v0)
  by (change 36%nat with (32 + 4)%nat; rewrite (EX 4%nat ltac:(lia)); reflexivity).
assert (E37 : ew E 37%nat = Z_to_bv 64 v1)
  by (change 37%nat with (32 + 5)%nat; rewrite (EX 5%nat ltac:(lia)); reflexivity).
assert (E38 : ew E 38%nat = Z_to_bv 64 v2)
  by (change 38%nat with (32 + 6)%nat; rewrite (EX 6%nat ltac:(lia)); reflexivity).
assert (E39 : ew E 39%nat = Z_to_bv 64 v3)
  by (change 39%nat with (32 + 7)%nat; rewrite (EX 7%nat ltac:(lia)); reflexivity).
assert (E40 : ew E 40%nat = Z_to_bv 64 v4)
  by (change 40%nat with (32 + 8)%nat; rewrite (EX 8%nat ltac:(lia)); reflexivity).
assert (E41 : ew E 41%nat = Z_to_bv 64 v5)
  by (change 41%nat with (32 + 9)%nat; rewrite (EX 9%nat ltac:(lia)); reflexivity).
assert (E42 : ew E 42%nat = Z_to_bv 64 rf)
  by (change 42%nat with (32 + 10)%nat; rewrite (EX 10%nat ltac:(lia)); reflexivity).
assert (E43 : ew E 43%nat = Z_to_bv 64 cd)
  by (change 43%nat with (32 + 11)%nat; rewrite (EX 11%nat ltac:(lia)); reflexivity).
assert (E44 : ew E 44%nat = Z_to_bv 64 st)
  by (change 44%nat with (32 + 12)%nat; rewrite (EX 12%nat ltac:(lia)); reflexivity).
assert (EGR : ew E 285%nat = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E 285%nat HEI ltac:(unfold A_TEXT, A_LIM; lia));
      change 285%nat with PCL_GR; rewrite pcl_grec_val; reflexivity).
assert (EGR' : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC) by exact EGR.
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2%nat = getr regs 2) by (apply EE; reflexivity).
assert (E2' : ew E 2%nat = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
  by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
split; [|exact (pcl_sh_ok ly S W mem md E c HAR Hc E32 E34)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- (* the registers: s0 is the slot, s3 is g_rec, s4 is the shadow base, the rest are their own atoms *)
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr) =>
      let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    first [ rewrite E34; exact R8 | rewrite EGR; exact R19 | rewrite E32; exact R20
          | symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity ]
  | ]); try (destruct Hr; fail).
- vm_compute. reflexivity.
- unfold pcl_rs_j, pcl_stack_j, pcl_slot, pcl_grec_lo, pcl_grec_st,
    PCL_RA, PCL_S0, PCL_S1, PCL_S2, PCL_S3, PCL_S4, PCL_S5, PCL_RF, PCL_CD, PCL_ST, PCL_C, PCL_GR.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat (spZ regs) E2' ltac:(lia)). unfold PCL_FRAME.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: first
    [ apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (SOff 41 0) v5);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 8) 8%nat v5 F5)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 (SOff 40 0) v4);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 16) 8%nat v4 F4)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 24 8 (SOff 39 0) v3);
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 24) 8%nat v3 F3)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 32 8 (SOff 38 0) v2);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 32) 8%nat v2 F2)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 40 8 (SOff 37 0) v1);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 40) 8%nat v1 F1)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 48 8 (SOff 36 0) v0);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 48) 8%nat v0 F0)]
    | apply (chunk_ok_val SEGS E _ (spZ regs) 56 8 (SOff 35 0) vra);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow8; lia | cbn; lia | exact (val_mem_view SEGS (w_H W) mem (spZ regs + 56) 8%nat vra FRA)] ].
  + rewrite (VB 34%nat c E34 ltac:(unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia)).
    unfold CALL_SIZE. split; [unfold A_G_REC, OFF_CALLS in *; lia|].
    split; [unfold A_REC_SPILL in *; lia|]. split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
    apply (pcl_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia].
  + rewrite (VB (A_OBJ 44) A_G_REC EGR' ltac:(unfold A_G_REC; lia)).
    unfold OFF_REFUSE, OFF_CODE. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: first
    [ apply (chunk_ok_val SEGS E _ A_G_REC 0 4 (SOff 42 0) rf);
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow4; lia | cbn; lia
      | exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_REFUSE) 4%nat rf Vrf)]
    | apply (chunk_ok_val SEGS E _ A_G_REC 4 4 (SOff 43 0) cd);
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite pcl_pow4; lia | cbn; lia
      | exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_CODE) 4%nat cd Vcd)] ].
  + rewrite (VB (A_OBJ 44) A_G_REC EGR' ltac:(unfold A_G_REC; lia)).
    unfold OFF_STATE. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold REC_SIZE, A_G_REC in *. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_STATE 8 (SOff 44 0) st);
    [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite pcl_pow8; lia | cbn; lia
    | exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_STATE) 8%nat st Vst)].
- apply pairwise_disjoint_of_extents.
  unfold pcl_rs_j, pcl_stack_j, pcl_slot, pcl_grec_lo, pcl_grec_st, extent_of_region, PCL_C, PCL_GR.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 2%nat (spZ regs) E2' ltac:(lia)).
  rewrite (VB 34%nat c E34 ltac:(unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia)).
  rewrite (VB (A_OBJ 44) A_G_REC EGR' ltac:(unfold A_G_REC; lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PCL_FRAME, CALL_SIZE, OFF_STATE, A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pcl_facts_j f_atoms atoms_ok]. unfold afact_ok, PCL_SB, PCL_C, PCL_GR. cbn [af_lo af_hi af_al2].
  rewrite E2', E32, E34, EGR', !unsigned_lit_small
    by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
  unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS, PCL_FRAME in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; try lia.
Qed.
End e.
End f.
End d.
