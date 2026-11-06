(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the seeds of descriptors_add's ASan walk (plugin-hostd/fuzz_command), after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the region and fact tables and the seeds of cgif_close's walk) and
   lib/A/Prog/sup_reply_code_s1.v (the entry seed over fuzz_command's listing). *)

(* descriptors_add (recorder.c:538-544, entry BASE + AF_descriptors_add = 0x8ce34, 91 instructions).
   Three symbolic states start a segment of the walk:
   - the entry (0x8ce34): every register its own atom, atom 32 the shadow base the GOT cell gives, atom 33
     g_rec.ncalls; regions: the 64-byte frame, the GOT word, the shadow-base cell, g_rec.ncalls;
   - the join (0x8ceac, after the inlined record() picked the slot c in s0) and the call of xstrdup (0x8ceec):
     every register its own atom (s0 = c, s3 = g_rec, s4 = the shadow base), the frame with the caller's seven
     saved registers (atoms 32..38), the slot [c, c + 56), and g_rec.state (atom 39). The slot is the one shadow
     entry, so each instrumented check on c, c + 4 and c + 8 reads a shadow byte the walk knows is 0. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the entry segment ----------------------------------------------------------------------------------- *)
Definition DA_SB : Z := 0x7fff8000.
Definition DA_GREC : nat := A_OBJ 44.
Definition DA_SPILL : nat := A_OBJ 51.
Definition DA_LIT : nat := A_OBJ 52.
Definition da_Bspan : Z * Z := (DA_SB, DA_SB + 2 ^ 44 - 1).
(* g_rec.ncalls, the one word of g_rec the inlined record() reads (and, on the slot arm, writes) *)
Definition da_ncalls : YP09.region :=
YP09.mkRegion (Some DA_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition da_rs0 : smem := [stack_region 64; got_regionP; bcell_regionP 32; da_ncalls].
(* the slot the inlined record() picks for n = g_rec.ncalls: record.spill when the table is full, else the next
   entry of g_rec.calls (recorder.c:207-216) *)
Definition da_slot (n : Z) : Z := if n =? 16 then A_REC_SPILL else A_G_REC + OFF_CALLS + CALL_SIZE * n.
(* mix_call's form of the same fact (mix_call_c.v:63) *)
Definition da_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
(* atom 33 (g_rec.ncalls) carries the arm's bounds: [0, 15] where record() takes a slot of the table, [16, 16]
   where it spills; with them the symbolic executor decides record()'s `bne ncalls, 16` itself *)
Definition da_facts0 (lo hi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF DA_SB DA_SB 0); (33%nat, mkAF lo hi 0);
         (34%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (DA_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_da0 (lo hi : Z) : sstate := mkSS AF_descriptors_add sr_atoms da_rs0 None (da_facts0 lo hi).
Definition da_Bx0 : sv := SOff 32 0.
(* the slot is the one shadow entry: atom 34 = da_slot n *)
Definition da_SH0 : list shent := [mkSHE 34 0 CALL_SIZE].
Definition da_extra0 (n : Z) : list word := map (Z_to_bv 64) [DA_SB; n; da_slot n].
(* the slot region, added once s0 holds the slot as atom 34: the stores to c->fn and c->nargs, nothing else *)
Definition da_slot0 : YP09.region := YP09.mkRegion (Some 34%nat) 0 CALL_SIZE 0 8 [].

(* --- the middle segments (0x8cedc, 0x8ceec) ----------------------------------------------------------------- *)
(* the callee-saved registers the prologue stores, in frame order from sp0 - 8 down *)
Definition da_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
Definition da_extraM (regs : bvmap 5 word) (h : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) da_saved ++ [Z_to_bv 64 h].
(* the frame, relative to the current sp (atom 2): the caller's ra, s0..s5 at 56, 48, .., 8 (atoms 32..38) *)
Definition da_frameM : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
   YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0));
   YP09.mkChunk 8 (CVal 8 (SOff 38 0))].
(* the slot (s0, atom 8) after the stores of c->fn = 22 and c->nargs = 0; the walk writes only c->fn, c->nargs and
   c->args[0], so the window is the slot's first 16 bytes and the rest of the slot is kept *)
Definition da_slotM : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 CALL_SIZE 0 16
  [YP09.mkChunk 0 (CVal 4 (SLit 22)); YP09.mkChunk 4 (CVal 4 (SLit 0))].
(* g_rec.state (s3 = g_rec, atom 19; the state word atom 39) *)
Definition da_stateM : YP09.region :=
YP09.mkRegion (Some 19%nat) OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8)
  [YP09.mkChunk OFF_STATE (CVal 8 (SOff 39 0))].
Definition da_rsM : smem := [da_frameM; da_slotM; da_stateM].
Definition da_factsM : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (19%nat, mkAF A_G_REC A_G_REC 3); (20%nat, mkAF DA_SB DA_SB 0)] [] [].
(* s2 = c + 4 and s5 = the shadow byte address of c + 4, in the form the instrumented check's load reads it *)
Definition da_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 4) (SLit 3)) (SOff 20 0).
Definition da_sregsM : list sv := sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 8 4)) (21%bv : bv 5) da_shx.
Definition ss_daM (pc : Z) : sstate := mkSS pc da_sregsM da_rsM None da_factsM.
Definition da_BxM : sv := SOff 20 0.
Definition da_SHM : list shent := [mkSHE 8 0 CALL_SIZE].
Definition DA_BR_S1 : Z := AF_descriptors_add + 0xa8.   (* bnez s1 (0x8cedc) *)
Definition DA_CALL_XS : Z := AF_descriptors_add + 0xb8. (* jal xstrdup (0x8ceec) *)
Definition DA_JOIN : Z := AF_descriptors_add + 0x78.    (* the two arms of record() meet (0x8ceac) *)
(* the footprint the statement names: g_rec, record.spill and the recorder's blocks *)
Definition da_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Lemma da_inFP_prog : forall O a, Exists (in_zr a) recb_PG -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) -> inFP (da_FP O) a.
Proof.
intros O a Ha Hq. apply Exists_exists in Ha as ([b n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
unfold recb_PG in Hin. destruct Hin as [Hq1 | [Hq1 | [Hq1 | []]]]; injection Hq1 as <- <-.
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exfalso. lia.
Qed.
Lemma da_slot_okP : forall n, 0 <= n <= 16 -> da_slot_ok (da_slot n).
Proof.
intros n Hn. unfold da_slot, da_slot_ok. destruct (Z.eqb_spec n 16) as [->|Hne]; [right; reflexivity|].
left. exists n. unfold REC_CALLS_MAX. split; [lia | reflexivity].
Qed.
Lemma da_slot_bounds : forall c, da_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((c + CALL_SIZE <= A_G_REC + OFF_STATE) \/ c = A_REC_SPILL).
Proof.
intros c [(k & Hk & ->) | ->]; unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_STATE, REC_SIZE, CALL_SIZE in *.
- split; [lia|]. split; [|left; lia].
  apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (771818 + 7 * k). lia.
- split; [lia|]. split; [reflexivity|]. right; reflexivity.
Qed.
Lemma da_in_zsh : forall r, existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) Tfib_zero_shadow = true ->
In r Tfib_zero_shadow.
Proof.
intros [r1 r2] H. apply existsb_exists in H as ([q1 q2] & Hin & Hq). cbn [fst snd] in Hq.
apply andb_prop in Hq as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. exact Hin.
Qed.
Lemma da_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma da_srl3_lit : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. symmetry. apply unsigned_lit_small. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition da_E0 (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (da_extra0 n)).
Section e.
Variable B : asyms.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
(* every lemma of this section takes all of its hypotheses, so a walk applies them in one fixed order *)
#[local] Set Default Proof Using "All".
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma da_grec_val : VAL DA_GREC = A_G_REC.
Proof. unfold DA_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma da_spill_val : VAL DA_SPILL = A_REC_SPILL.
Proof. unfold DA_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma da_lit_val : VAL DA_LIT = 0x22480.
Proof. unfold DA_LIT. rewrite (VOBJS 52%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* a write of this call to g_rec or record.spill is one the journal admits: in the footprint, a byte of the
   program's statics, in the image (awr_byte's program-static disjunct, lib/Reusable/YCbq.v:496-505) *)
Lemma da_awr_prog : forall STK sp0 O bl0 blc fr0 lyx own a,
Exists (in_zr a) recb_PG -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) ->
awr_byte SEGS B STK sp0 (da_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha Hq. right; right; right; right. left.
split; [exact (da_inFP_prog O a Ha Hq)|].
split; [rewrite (ts_prog B HB); exact Ha | exact (cmd_prog_img a Ha)].
Qed.
Lemma da_awr_grec : forall STK sp0 O bl0 blc fr0 lyx own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (da_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha. apply da_awr_prog; [exact (recb_grec_in a Ha)|].
unfold A_G_REC, REC_SIZE, A_G_QUITTING in *. lia.
Qed.
Lemma da_awr_slot : forall STK sp0 O bl0 blc fr0 lyx own c a, da_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (da_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own c a Hc Ha.
destruct Hc as [(k & Hk & ->) | ->]; [apply da_awr_grec; unfold REC_CALLS_MAX, A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia|].
apply da_awr_prog; [apply recb_spill_in; unfold SC_SIZE, CALL_SIZE in *; lia|].
unfold A_REC_SPILL, A_G_QUITTING, CALL_SIZE in *. lia.
Qed.

(* the slot's 56 bytes lie in a zero-shadow range of the record (g_rec's or record.spill's), so every check on
   them passes *)
Lemma da_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> da_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(k & Hk & ->) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) _ CALL_SIZE HAR);
  [apply da_in_zsh; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst snd] | cbn [fst snd]];
  unfold REC_CALLS_MAX, A_G_REC, OFF_CALLS, CALL_SIZE in *; lia.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) _ CALL_SIZE HAR);
  [apply da_in_zsh; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst snd] | cbn [fst snd]];
  unfold A_REC_SPILL, CALL_SIZE in *; lia.
Qed.
Lemma da_slot_sh_ok : forall ly S (W : world SEGS) mem md E (m bx : nat) c,
AR SEGS B ly S W mem md -> da_slot_ok c ->
ew E m = Z_to_bv 64 c -> ew E bx = Z_to_bv 64 DA_SB ->
sh_ok SEGS (SOff bx 0) [mkSHE m 0 CALL_SIZE] E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E m bx c HAR Hc Em Ebx.
destruct (da_slot_bounds c Hc) as (Hcb & _ & _).
unfold sh_ok. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E (SOff bx 0) m c CALL_SIZE c 0 CALL_SIZE).
- exact (da_slot_addressable ly S W mem md c HAR Hc).
- apply U_atom; [exact Ebx | unfold SHADOW_OFF; lia].
- apply U_atom; [exact Em | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

Lemma da_entry : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n lo hi,
AR SEGS B ly S W mem md ->
astk_ok DESCRIPTORS_ADD_STK ly (spZ regs) ->
(forall a, spZ regs - DESCRIPTORS_ADD_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 -> lo <= n <= hi ->
st_ok_pi SEGS VAL (da_E0 regs n) (ss_da0 lo hi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_descriptors_add)) mem (seg_rom SEGS)))
/\ sh_ok SEGS da_Bx0 da_SH0 (da_E0 regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n lo hi HAR Hstk Hpres HNC Hn Hlh.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : 64 <= DESCRIPTORS_ADD_STK) by (vm_compute; congruence).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := da_E0 regs n).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 DA_SB).
{ subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E34 : ew E 34 = Z_to_bv 64 (da_slot n)).
{ subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
pose proof (da_slot_okP n Hn) as Hc.
destruct (da_slot_bounds _ Hc) as (Hcb & Hc8 & _).
assert (EG : ew E DA_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E DA_GREC HEI ltac:(unfold DA_GREC, A_OBJ, A_TEXT, A_LIM; lia)), da_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (rewrite (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (rewrite (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| exact (da_slot_sh_ok ly S W mem md E 34 32 (da_slot n) HAR Hc E34 E32)].
rewrite restrict_mkst_fx. unfold ss_da0.
apply pa_entry_st_ok_full.
- subst E. unfold da_E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold da_rs0, stack_region, got_regionP, bcell_regionP, da_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) DA_SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold DA_SB; change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB DA_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold da_rs0, stack_region, got_regionP, bcell_regionP, da_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB DA_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)). cbn [nth cmd_objs].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [da_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32, E33, E34, EG.
  rewrite !unsigned_lit_small by (unfold DA_SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DA_SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | reflexivity | lia].
Qed.

(* the caller's seven saved registers in the frame below sp0 (ra at sp0 - 8, s0 at sp0 - 16, ..., s5 at sp0 - 56) *)
Definition da_frame_at (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error da_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition da_EM (regsc regs : bvmap 5 word) (h : Z) : env := Eimg (Ereg regsc (da_extraM regs h)).

Lemma da_frame_chunk : forall E m sp0 (regs : bvmap 5 word) j r,
nth_error da_saved j = Some r -> da_frame_at m sp0 regs ->
ew E (32 + j) = getr regs (Z_to_bv 5 r) ->
YP09.chunk_ok SEGS E m (sp0 - 64) (YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))).
Proof.
intros E m sp0 regs j r Hj Hfr Ej.
apply (chunk_ok_val SEGS E m (sp0 - 64) (56 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
- cbn [sv_denot]. rewrite Ej, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  change (8 * Z.of_N 8) with 64. lia.
- change (Z.of_N 8) with 8. lia.
- replace (sp0 - 64 + (56 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (Hfr j r Hj).
Qed.


Lemma da_mid : forall lyc Sc (Wc : world SEGS) memc mdc (regsc regs : bvmap 5 word) pc sp0 c h,
AR SEGS B lyc Sc Wc memc mdc ->
bv_unsigned (getr regsc 2) = sp0 - 64 -> sp0 mod 16 = 0 -> 2 ^ 46 + 64 <= sp0 <= 2 ^ 47 ->
da_frame_at (mrestrict (w_H Wc) memc) sp0 regs ->
getr regsc 8 = Z_to_bv 64 c -> da_slot_ok c ->
aval_mem (rdW Wc memc) c 4 22 -> aval_mem (rdW Wc memc) (c + 4) 4 0 ->
getr regsc 19 = Z_to_bv 64 A_G_REC -> getr regsc 20 = Z_to_bv 64 DA_SB ->
getr regsc 18 = Z_to_bv 64 (c + 4) -> getr regsc 21 = Z_to_bv 64 ((c + 4) / 8 + DA_SB) ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
st_ok_pi SEGS VAL (da_EM regsc regs h) (ss_daM pc)
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS da_BxM da_SHM (da_EM regsc regs h) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc regsc regs pc sp0 c h HAR Hsp Hsp16 Hsp47 Hfr H8 Hc Hfn Hna H19 H20 H18 H21 Hst Hh.
destruct (da_slot_bounds c Hc) as (Hcb & Hc8 & Hcs).
set (E := da_EM regsc regs h).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. unfold da_EM. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (da_extraM regs h) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold da_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E19 : ew E 19 = Z_to_bv 64 A_G_REC) by (rewrite (EL 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 DA_SB) by (rewrite (EL 20%nat 20%bv eq_refl); exact H20).
assert (E39 : ew E 39 = Z_to_bv 64 h) by (change 39%nat with (32 + 7)%nat; rewrite EX by lia; reflexivity).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite E8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U19 : bv_unsigned (ew E 19) = A_G_REC) by (rewrite E19; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U20 : bv_unsigned (ew E 20) = DA_SB) by (rewrite E20; apply unsigned_lit_small; unfold DA_SB; lia).
assert (Hslot : forall o, 0 <= o < CALL_SIZE -> Exists (in_zr (c + o)) recb_PG).
{ intros o Ho. destruct Hc as [(k & Hk & ->) | ->];
  [apply recb_grec_in | apply recb_spill_in];
  unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia. }
split; [| exact (da_slot_sh_ok lyc Sc Wc memc mdc E 8 20 c HAR Hc E8 E20)].
rewrite restrict_mkst_fx. unfold ss_daM.
apply pa_entry_st_ok_full.
- unfold da_sregsM. apply regs_ok_rereg; [apply regs_ok_rereg; [subst E; unfold da_EM; apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
  + cbn [sv_denot]. rewrite U8. exact H18.
  + unfold da_shx. cbn [sv_denot]. rewrite U8, E20.
    rewrite da_srl3_lit by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia). rewrite da_add_lit. exact H21.
- vm_compute. reflexivity.
- unfold da_rsM, da_frameM, da_slotM, da_stateM.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (Hfj : forall j r, nth_error da_saved j = Some r ->
      YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp0 - 64)
        (YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
    { intros j r Hj. assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      apply (da_frame_chunk E _ sp0 regs j r Hj Hfr). rewrite EX by (cbn in Hj7; lia). unfold da_extraM.
      rewrite app_nth1 by (rewrite length_map; exact Hj7).
      apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
    repeat apply Forall_cons; try apply Forall_nil;
    [exact (Hfj 0%nat 1 eq_refl) | exact (Hfj 1%nat 8 eq_refl) | exact (Hfj 2%nat 9 eq_refl)
    | exact (Hfj 3%nat 18 eq_refl) | exact (Hfj 4%nat 19 eq_refl) | exact (Hfj 5%nat 20 eq_refl) | exact (Hfj 6%nat 21 eq_refl)].
  + rewrite U8. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable lyc Sc Wc memc mdc); [exact HAR | exact (Hslot o ltac:(unfold CALL_SIZE; lia))]. }
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ c 0 4 (SLit 22) 22); [reflexivity | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia |].
      rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H Wc) memc c 4%nat 22 Hfn).
    * apply (chunk_ok_val SEGS E _ c 4 4 (SLit 0) 0); [reflexivity | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia |].
      exact (val_mem_view SEGS (w_H Wc) memc (c + 4) 4%nat 0 Hna).
  + rewrite U19. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable lyc Sc Wc memc mdc); [exact HAR|]. apply recb_grec_in.
      unfold OFF_STATE, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_STATE 8 (SOff 39 0) h);
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia |].
    exact (val_mem_view SEGS (w_H Wc) memc (A_G_REC + OFF_STATE) 8%nat h Hst).
- apply pairwise_disjoint_of_extents.
  unfold da_rsM, da_frameM, da_slotM, da_stateM, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, U8, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_STATE, CALL_SIZE in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [da_factsM f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, U8, U19, U20.
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hsp16' : (sp0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  unfold DA_SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | reflexivity | lia].
Qed.

End e.
End f.
End d.
