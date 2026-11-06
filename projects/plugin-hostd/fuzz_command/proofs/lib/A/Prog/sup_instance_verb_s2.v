(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command,
   0x8b3b8), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed, regsB_okX of A/ACh1.v) and the entry seed of
   lib/A/Prog/sup_worker_list.v (the template walk), over lib/A/Prog/RecBTemplateSiv.v's atoms. *)

(* sup_instance_verb (recorder.c:379-388): frame 48 bytes; ra, s0, s1, s2, s3 saved at sp+40 .. sp+8 of the new sp.
   Atoms (RecBTemplateSiv.v): 2 = sp, 32 = the shadow base SB, 33 = g_rec.ncalls at entry, 34 = the slot c, 35 .. 40 =
   the entry values of ra, s0, s1, s2, s3, s4. Three seeds: the entry (frame being written, the GOT word of the shadow
   base, its cell, g_rec.ncalls), the join after record()'s two arms (the frame and the slot, s0 = slot, s3 = SB, so
   the two inline checks of the slot are covered), and every later segment (the frame only). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBTemplateSiv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of the member's program points from its entry (listing slots 5045 .. 5122; CmdList.v:5123-5200) *)
Definition SIV_E : Z := AF_sup_instance_verb.
Definition SIV_BR : Z := AF_sup_instance_verb + 0x3c.       (* bne a2,a3: ncalls <> 16 (0x8b3f4) *)
Definition SIV_RCF_RET : Z := AF_sup_instance_verb + 0x54.  (* after rec_calls_free(&spill, 1) (0x8b40c) *)
Definition SIV_J : Z := AF_sup_instance_verb + 0x74.        (* the join of record()'s two arms (0x8b42c) *)
Definition SIV_L_RET : Z := AF_sup_instance_verb + 0xb0.    (* after arg_line (0x8b468) *)
Definition SIV_I_RET : Z := AF_sup_instance_verb + 0xbc.    (* after arg_i (0x8b474) *)
Definition SIV_SPN_RET : Z := AF_sup_instance_verb + 0xd0.  (* after the strspn wrapper (0x8b488) *)
Definition SIV_CSPN_RET : Z := AF_sup_instance_verb + 0xe0. (* after the strcspn wrapper (0x8b498) *)
Definition SIV_RSO_RET : Z := AF_sup_instance_verb + 0xec.  (* after rec_shape_of (0x8b4a4) *)

(* the frame below the entry sp, as the walk sees it after the prologue: [sp, sp + 48) of the current sp, with the
   five saved words *)
Definition siv_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 39 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0));
   YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0))].
Definition siv_saved : list Z := [1; 8; 9; 18; 19].
(* the join's registers: s0 is the slot atom, s3 the shadow base *)
Definition siv_regsJ : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 8 (SOff RB_C 0)) 19 (SOff RB_SB 0).
Definition siv_rsJ : YP09.smem := [siv_frame; rbs_slot []].
(* the entry's regions: the frame being written, the GOT word of the shadow base and its cell, g_rec.ncalls *)
Definition siv_rs0 : YP09.smem := [rbs_stack (-48) []; got_regionP; bcell_regionP RB_SB; rbs_ncalls].
Definition siv_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the saved words of the frame, at the entry sp0: register r_j at sp0 - 8 - 8 j *)
Definition siv_frame_ok (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error siv_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

Definition siv_E (regs regs1 : bvmap 5 word) (n c : Z) : env := Eimg (Ereg regs1 (rbs_extra regs n c)).

Lemma siv_E_extra : forall regs1 ex k, (32 + k < A_TEXT)%nat ->
ew (Eimg (Ereg regs1 ex)) (32 + k) = nth k ex (Z_to_bv 64 0).
Proof. intros regs1 ex k Hk. rewrite Eimg_low by exact Hk. apply ew_Ereg_extra. Qed.

Lemma siv_E_reg : forall regs regs1 n c k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (siv_E regs regs1 n c) k = getr regs1 r.
Proof.
intros regs regs1 n c k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold siv_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma siv_E_SB : forall regs regs1 n c, ew (siv_E regs regs1 n c) 32 = Z_to_bv 64 SB.
Proof. intros. unfold siv_E. exact (siv_E_extra regs1 _ 0 ltac:(unfold A_TEXT; lia)). Qed.
Lemma siv_E_N : forall regs regs1 n c, ew (siv_E regs regs1 n c) 33 = Z_to_bv 64 n.
Proof. intros. unfold siv_E. exact (siv_E_extra regs1 _ 1 ltac:(unfold A_TEXT; lia)). Qed.
Lemma siv_E_C : forall regs regs1 n c, ew (siv_E regs regs1 n c) 34 = Z_to_bv 64 c.
Proof. intros. unfold siv_E. exact (siv_E_extra regs1 _ 2 ltac:(unfold A_TEXT; lia)). Qed.

Lemma siv_E_saved : forall regs regs1 n c j r, nth_error siv_saved j = Some r ->
ew (siv_E regs regs1 n c) (35 + j) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs1 n c j r Hj. unfold siv_E.
replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
rewrite (siv_E_extra regs1 _ (3 + j)) by (assert (j < 5)%nat by (apply (proj1 (nth_error_Some siv_saved j)); rewrite Hj; discriminate);
  unfold A_TEXT; lia).
do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). destruct j; discriminate.
Qed.

Lemma siv_env : forall regs regs1 n c, rbs_env_ok (siv_E regs regs1 n c) (spZ regs1) n c.
Proof.
intros regs regs1 n c. split; [unfold siv_E; apply Eimg_env|].
rewrite (siv_E_reg regs regs1 n c 2%nat 2%bv eq_refl), siv_E_SB, siv_E_N, siv_E_C.
split; [unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|]. split; [reflexivity | split; reflexivity].
Qed.

Lemma siv_chunk_ok : forall E m sp0 (regs : bvmap 5 word) j r, nth_error siv_saved j = Some r ->
ew E (35 + j) = getr regs (Z_to_bv 5 r) -> siv_frame_ok m sp0 regs ->
YP09.chunk_ok SEGS E m (sp0 - 48) (YP09.mkChunk (40 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))).
Proof.
intros E m sp0 regs j r Hj HE HF.
apply (chunk_ok_val SEGS E m (sp0 - 48) (40 - 8 * Z.of_nat j) 8 (SOff (35 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
- cbn [sv_denot]. rewrite HE, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HR.
- cbn. lia.
- replace (sp0 - 48 + (40 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (HF j r Hj).
Qed.

Lemma siv_frame_region_ok : forall E m sp0 (regs : bvmap 5 word),
bv_unsigned (ew E 2) = sp0 - 48 -> 0 <= sp0 - 48 -> sp0 <= 2 ^ 64 ->
(forall j r, nth_error siv_saved j = Some r -> ew E (35 + j) = getr regs (Z_to_bv 5 r)) ->
siv_frame_ok m sp0 regs -> YP09.region_ok SEGS E m siv_frame.
Proof.
intros E m sp0 regs E2 H0 H1 ES HF. unfold YP09.region_ok, siv_frame.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
change (YP09.mkChunk 8 (CVal 8 (SOff 39 0))) with (YP09.mkChunk (40 - 8 * Z.of_nat 4) (CVal 8 (SOff (35 + 4) 0))).
change (YP09.mkChunk 16 (CVal 8 (SOff 38 0))) with (YP09.mkChunk (40 - 8 * Z.of_nat 3) (CVal 8 (SOff (35 + 3) 0))).
change (YP09.mkChunk 24 (CVal 8 (SOff 37 0))) with (YP09.mkChunk (40 - 8 * Z.of_nat 2) (CVal 8 (SOff (35 + 2) 0))).
change (YP09.mkChunk 32 (CVal 8 (SOff 36 0))) with (YP09.mkChunk (40 - 8 * Z.of_nat 1) (CVal 8 (SOff (35 + 1) 0))).
change (YP09.mkChunk 40 (CVal 8 (SOff 35 0))) with (YP09.mkChunk (40 - 8 * Z.of_nat 0) (CVal 8 (SOff (35 + 0) 0))).
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk (40 - 8 * Z.of_nat ?j) _) =>
  let r := eval compute in (nth j siv_saved 0) in
  exact (siv_chunk_ok E m sp0 regs j r eq_refl (ES j r eq_refl) HF) end.
Qed.

(* the registers of the join: as their own atoms, but s0 the slot atom and s3 the shadow base atom *)
Lemma siv_regsJ_ok : forall regs regs1 n c,
getr regs1 8 = Z_to_bv 64 c -> getr regs1 19 = Z_to_bv 64 SB ->
regs_ok (siv_E regs regs1 n c) siv_regsJ regs1.
Proof.
intros regs regs1 n c R8 R19.
set (E := siv_E regs regs1 n c).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros; apply siv_E_reg; assumption).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by apply siv_E_SB.
assert (E34 : ew E 34 = Z_to_bv 64 c) by apply siv_E_C.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
        | rewrite E34; exact R8 | rewrite E32; exact R19 ]
| ]); try (destruct Hr; fail).
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* every segment after the join: the frame only *)
Lemma siv_seed_mid : forall pc sregs ly1 S1 (W1 : world SEGS) mem1 md1 (regs regs1 : bvmap 5 word) sp0 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= sp0 - 48 <= 2 ^ 47 -> sp0 mod 16 = 0 -> 0 <= n <= 16 -> rbs_slot_ok c ->
spZ regs1 = sp0 - 48 ->
siv_frame_ok (mrestrict (w_H W1) mem1) sp0 regs ->
regs_ok (siv_E regs regs1 n c) sregs regs1 ->
st_ok_pi SEGS VAL (siv_E regs regs1 n c) (mkSS pc sregs [siv_frame] None rbs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbs_SH (siv_E regs regs1 n c) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs ly1 S1 W1 mem1 md1 regs regs1 sp0 n c HAR Hsp Hsp16 Hn Hc Hsp1 HF HREG.
pose proof (siv_env regs regs1 n c) as HE. rewrite Hsp1 in HE.
pose proof HE as (HEI & E2 & _).
split; [| exact (rbs_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 _ (sp0 - 48) n c HAR HE Hc)].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (siv_frame_region_ok _ _ sp0 regs);
  [ rewrite E2; apply unsigned_lit_small; lia | lia | lia | intros j r Hj; apply siv_E_saved; exact Hj | exact HF ].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
- apply (rbs_facts_ok VOBJS _ (sp0 - 48) n c HE); [lia | | exact Hn | exact Hc].
  replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* the join: the frame and the slot; s0 = the slot atom, s3 = the shadow base atom *)
Lemma siv_seed_join : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs regs1 : bvmap 5 word) sp0 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= sp0 - 48 <= 2 ^ 47 -> sp0 mod 16 = 0 -> 0 <= n <= 16 -> rbs_slot_ok c ->
spZ regs1 = sp0 - 48 -> getr regs1 8 = Z_to_bv 64 c -> getr regs1 19 = Z_to_bv 64 SB ->
siv_frame_ok (mrestrict (w_H W1) mem1) sp0 regs ->
st_ok_pi SEGS VAL (siv_E regs regs1 n c) (mkSS SIV_J siv_regsJ siv_rsJ None rbs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SIV_J)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbs_SH (siv_E regs regs1 n c) (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs regs1 sp0 n c HAR Hsp Hsp16 Hn Hc Hsp1 R8 R19 HF.
pose proof (siv_env regs regs1 n c) as HE. rewrite Hsp1 in HE.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (rbs_slot_bounds c Hc) as [Hcb Hc8].
assert (Hc56 : c + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\
  forall o, 0 <= o < CALL_SIZE -> Exists (in_zr (c + o)) recb_PG).
{ destruct Hc as [(H1 & H2 & H3) | ->].
  - split; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia|].
    intros o Ho. apply recb_grec_in. unfold CALL_SIZE, OFF_CALLS in *. lia.
  - split; [unfold CALL_SIZE, SC_SIZE; lia|]. intros o Ho. apply recb_spill_in. unfold CALL_SIZE, SC_SIZE in *. lia. }
split; [| exact (rbs_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 _ (sp0 - 48) n c HAR HE Hc)].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply siv_regsJ_ok; assumption.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (siv_frame_region_ok _ _ sp0 regs);
    [ rewrite E2; apply unsigned_lit_small; lia | lia | lia | intros j r Hj; apply siv_E_saved; exact Hj | exact HF ].
  + unfold rbs_slot, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EC, unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia|].
    split; [intros o Ho; apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR | apply (proj2 Hc56); exact Ho]|].
    apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold siv_rsJ, siv_frame, rbs_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, EC, !unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE in *. repeat split; lia.
- apply (rbs_facts_ok VOBJS _ (sp0 - 48) n c HE); [lia | | exact Hn | exact Hc].
  replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* the entry: the frame being written below the entry sp, the GOT word of the shadow base, its cell, and
   g_rec.ncalls (sup_worker_list.v's entry seed, frame 48) *)
Lemma siv_seed_entry : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 -> 0 <= n <= 16 -> rbs_slot_ok c ->
(forall a, spZ regs1 - 48 <= a < spZ regs1 -> apresent (w_H W1) mem1 a) ->
aval_mem (rdW W1 mem1) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (siv_E regs1 regs1 n c) (mkSS SIV_E sr_atoms siv_rs0 None rbs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SIV_E)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbs_SH (siv_E regs1 regs1 n c) (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 n c HAR Hsp Hsp16 Hn Hc Hpres HNC.
pose proof (siv_env regs1 regs1 n c) as HE.
set (E := siv_E regs1 regs1 n c) in *. set (sp := spZ regs1) in *.
pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbs_grec_val VOBJS); reflexivity).
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
split; [| exact (rbs_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E, siv_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold siv_rs0, rbs_stack, got_regionP, bcell_regionP, rbs_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat sp E2) by lia. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbs_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxr SHADOW_OFF);
    [cbn [sv_denot Bxr]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbs_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff RB_N 0) n);
    [cbn [sv_denot]; rewrite EN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbs_pow4; lia | cbn; lia |].
    exact (RecBLemmas.val_mem_view SEGS (w_H W1) mem1 (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold siv_rs0, rbs_stack, got_regionP, bcell_regionP, rbs_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat sp E2) by lia.
  rewrite EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- exact (rbs_facts_ok VOBJS E sp n c HE Hsp Hsp16 Hn Hc).
Qed.

End e.
End f.
End d.
