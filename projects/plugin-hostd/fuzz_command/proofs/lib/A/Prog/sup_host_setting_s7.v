(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_after_reply on plugin-hostd/fuzz_command.asan (0x8c658, 100 instructions), in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (a seed state rebuilt from concrete facts at each return point) and A/ACh1.v (the segment walk of cgif_close: run, call, return); the entry seed and the slot's denotation after lib/A/Prog/sup_worker_list.v, two lemmas copied from lib/A/Prog/RecBLemmas.v; the named per-binary hypotheses take the one name and form per fact that the recorder walks share. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_after_reply.v, with its module names and numbers changed; 954 of its 1043 lines of code are new or changed and 1898 lines of the source are left out. *)
(* The last three segments of sup_host_setting's ASan walk (plugin-hostd/fuzz_command): XS -> FR (0x8b2a8: the
   third argument recorded, the free wrapper on the word list), FR -> MIX (0x8b2e4: mix_call on g_rec's host
   digest and the slot) and MIX (0x8b2f0: the digest stored, the frame reloaded, the return). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1 sup_host_setting_s0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the shadow base atom (s7) and the shadow span *)
Definition hs7_Bx : sv := SOff 23 0.
Definition hs7_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
Definition hs7_shx (m : nat) (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m o) (SLit 3)) (SOff 23 0).

(* XS 0x8b2a8: the slot's nargs cell (c + 4) and the third argument slot (c + 24), each its own region so that
   the run's frame keeps every other byte of the slot *)
Definition hs7_fXS : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
  (23%nat, mkAF HS_SB HS_SB 0)] [] [].
Definition hs7_rXSn : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit 2))].
Definition hs7_rXSa : YP09.region := YP09.mkRegion (Some 8%nat) 24 32 24 32 [].
Definition hs7_SHXS : list shent := [mkSHE 8 0 56].
Definition hs7_ssXS : sstate :=
mkSS HS_XS (sr_set (sr_set sr_atoms 24 (hs7_shx 8 4)) 19 (SOff 8 4)) [hs7_rXSn; hs7_rXSa] None hs7_fXS.

(* FR 0x8b2e4 / MIX 0x8b2f0: g_rec.host_settings (+ 952) and the 112-byte frame with the 13 saved registers
   (atom 33 + i holds the register HS_SAVED names at 12 - i) *)
Definition hs7_fFR : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
  (22%nat, mkAF A_G_REC A_G_REC 3)] [] [].
Definition hs7_rG (wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some 22%nat) OFF_HOST (OFF_HOST + 8) wlo whi [YP09.mkChunk OFF_HOST (CVal 8 (SOff 32 0))].
Definition hs7_rFrame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 112 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0));
 YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0)); YP09.mkChunk 48 (CVal 8 (SOff 38 0));
 YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0)); YP09.mkChunk 72 (CVal 8 (SOff 41 0));
 YP09.mkChunk 80 (CVal 8 (SOff 42 0)); YP09.mkChunk 88 (CVal 8 (SOff 43 0)); YP09.mkChunk 96 (CVal 8 (SOff 44 0));
 YP09.mkChunk 104 (CVal 8 (SOff 45 0))].
Definition hs7_ssFR : sstate := mkSS HS_FR sr_atoms [hs7_rG 960 960; hs7_rFrame] None hs7_fFR.
Definition hs7_ssMIX : sstate := mkSS HS_MIX sr_atoms [hs7_rG 952 960; hs7_rFrame] None hs7_fFR.

(* the env's extra atoms: the old host digest, then the saved registers in the frame's order *)
Definition hs7_extra (regs : bvmap 5 word) (h0 : Z) : list word :=
[Z_to_bv 64 h0; getr regs (Z_to_bv 5 27); getr regs (Z_to_bv 5 26); getr regs (Z_to_bv 5 25);
 getr regs (Z_to_bv 5 24); getr regs (Z_to_bv 5 23); getr regs (Z_to_bv 5 22); getr regs (Z_to_bv 5 21);
 getr regs (Z_to_bv 5 20); getr regs (Z_to_bv 5 19); getr regs (Z_to_bv 5 18); getr regs (Z_to_bv 5 9);
 getr regs (Z_to_bv 5 8); getr regs (Z_to_bv 5 1)].

Definition hs7_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma hs7_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (hs_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.

Lemma hs7_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (hs_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma hs7_rhost_rec : forall R fn A, r_host (rec_record R fn A) = r_host R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma hs7_bv5_eq : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r.
Proof. intros z r <-. apply Z_to_bv_bv_unsigned. Qed.

Lemma hs7_saved_lt : forall j r, nth_error HS_SAVED j = Some r -> (j < 13)%nat.
Proof.
intros j r H. assert (Hne : nth_error HS_SAVED j <> None) by (rewrite H; discriminate).
apply nth_error_Some in Hne. exact Hne.
Qed.

(* every byte of the slot lies in g_rec or in record.spill *)
Lemma hs7_slot_in : forall R o, 0 <= o < CALL_SIZE ->
(A_G_REC <= hs_slot R + o < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= hs_slot R + o < A_REC_SPILL + SC_SIZE).
Proof.
intros R o Ho. pose proof (hs_slot_bounds R) as (H1 & H2 & H3 & [H4 | H4]).
- left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, REC_SIZE, CALL_SIZE in *. lia.
- right. rewrite H4. unfold CALL_SIZE, SC_SIZE in *. lia.
Qed.

Lemma hs7_slot_pg : forall R o, 0 <= o < CALL_SIZE -> Exists (in_zr (hs_slot R + o)) recb_PG.
Proof. intros R o Ho. destruct (hs7_slot_in R o Ho) as [H | H]; [apply recb_grec_in | apply recb_spill_in]; exact H. Qed.

Lemma hs7_slot_FP : forall R O o, 0 <= o < CALL_SIZE -> inFP (hs_FP O) (hs_slot R + o).
Proof. intros R O o Ho. destruct (hs7_slot_in R o Ho) as [H | H]; [apply hs7_inFP_grec | apply hs7_inFP_spill]; exact H. Qed.

(* the joined word list is one byte shorter than the bytes the length loop adds up *)
Lemma hs7_join_len : forall toks, toks <> [] -> Z.of_nat (length (join_sp toks)) + 1 = hs_words_len toks.
Proof.
induction toks as [|w ws IH]; intros Hne; [congruence|].
destruct ws as [|w2 ws'].
- unfold hs_words_len. cbn [join_sp fold_right]. lia.
- change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  rewrite length_app. cbn [length].
  specialize (IH ltac:(discriminate)). unfold hs_words_len in *. cbn [fold_right] in *. lia.
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

(* one saved register of the frame, as a chunk of the stack region *)
Lemma hs7_chunk_fr : forall (E : env) (W : world SEGS) memc sp0 (regs : bvmap 5 word) (i j : nat) (r : Z),
hs_frame (aview SEGS (w_H W) memc) sp0 regs ->
nth_error HS_SAVED j = Some r ->
ew E (33 + i)%nat = getr regs (Z_to_bv 5 r) ->
(i + j = 12)%nat ->
YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) (sp0 - 112) (YP09.mkChunk (8 + 8 * Z.of_nat i) (CVal 8 (SOff (33 + i) 0))).
Proof.
intros E W memc sp0 regs i j r HFR Hj Hew Hij.
apply (chunk_ok_val SEGS E _ (sp0 - 112) (8 + 8 * Z.of_nat i) 8 (SOff (33 + i) 0) (bv_unsigned (ew E (33 + i)))).
- cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range 64 (ew E (33 + i))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
- apply val_mem_view. rewrite Hew. change (N.to_nat 8) with 8%nat.
  replace (sp0 - 112 + (8 + 8 * Z.of_nat i)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
  exact (HFR j r Hj).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the recorder's own blocks are live, below the allocation ceiling and above 4096 *)
Lemma hs7_own_bounds : forall ly S (W : world SEGS) mem md rd R O pn,
AR SEGS B ly S W mem md -> rec_repA B ly S rd R O -> In pn O ->
In pn (ablocks B ly S) /\ 4096 <= fst pn /\ fst pn + snd pn <= alloc_ceiling /\ 0 <= snd pn.
Proof.
intros ly S W mem md rd R O pn HAR HREP Hpn.
destruct (hs_rec_own B ly S rd R O HREP pn Hpn) as (Hin & _ & _).
destruct pn as [p n]. cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as Hq. split; [exact Hin|]. split; [lia|]. split; lia.
Qed.

(* the seed at MIX: the digest cell writable, the frame read-only *)
Lemma hs7_seed_MIX : forall (W : world SEGS) (regs1 regs : bvmap 5 word) memc ly S md sp0 c h0,
AR SEGS B ly S W memc md ->
bv_unsigned (getr regs1 2) = sp0 - 112 -> 2 ^ 46 <= sp0 - 112 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
getr regs1 8 = w64 c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL -> c mod 8 = 0 ->
getr regs1 22 = w64 A_G_REC ->
hs_frame (aview SEGS (w_H W) memc) sp0 regs ->
aval_mem (aview SEGS (w_H W) memc) (A_G_REC + OFF_HOST) 8 h0 -> 0 <= h0 < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hs7_extra regs h0))) hs7_ssMIX
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_MIX)) memc (seg_rom SEGS))).
Proof.
intros W regs1 regs memc ly S md sp0 c h0 HAR Usp Hsp1 Hsp2 Hsp16 R8 Hc1 Hc8 R22 HFR Hh Hh64.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (hs7_extra regs h0))) in *.
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HEX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (hs7_extra regs h0) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U2 : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (HEE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U22 : bv_unsigned (ew E 22) = A_G_REC)
  by (rewrite (HEE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U32 : ew E 32 = Z_to_bv 64 h0) by (change 32%nat with (32 + 0)%nat; rewrite HEX by lia; reflexivity).
assert (EX : forall i j r, (i < 13)%nat -> (i + j = 12)%nat -> nth_error HS_SAVED j = Some r ->
  ew E (33 + i)%nat = getr regs (Z_to_bv 5 r)).
{ intros i j r Hi Hij Hn. change (33 + i)%nat with (32 + (1 + i))%nat. rewrite HEX by lia.
  assert (Hj : j = (12 - i)%nat) by lia. subst j.
  do 13 (destruct i as [|i]; [cbn in Hn; injection Hn as <-; reflexivity|]). lia. }
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hs7_ssMIX, hs7_rG, hs7_rFrame. cbn [ss_mem].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [unfold A_G_REC, OFF_HOST; lia|]. split; [unfold A_G_REC, OFF_HOST; lia|]. split.
    { intros o Ho. apply (hh_prog_writable B MT HH ly S W memc md (A_G_REC + o) HAR).
      apply recb_grec_in. unfold REC_SIZE, OFF_HOST in *. lia. }
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_HOST 8 (SOff 32 0) h0).
    * cbn [sv_denot]. rewrite U32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * change (N.to_nat 8) with 8%nat. apply val_mem_view. exact Hh.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (hs7_chunk_fr E W memc sp0 regs 0%nat 12%nat 27 HFR eq_refl (EX 0%nat 12%nat 27 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 1%nat 11%nat 26 HFR eq_refl (EX 1%nat 11%nat 26 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 2%nat 10%nat 25 HFR eq_refl (EX 2%nat 10%nat 25 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 3%nat 9%nat 24 HFR eq_refl (EX 3%nat 9%nat 24 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 4%nat 8%nat 23 HFR eq_refl (EX 4%nat 8%nat 23 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 5%nat 7%nat 22 HFR eq_refl (EX 5%nat 7%nat 22 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 6%nat 6%nat 21 HFR eq_refl (EX 6%nat 6%nat 21 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 7%nat 5%nat 20 HFR eq_refl (EX 7%nat 5%nat 20 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 8%nat 4%nat 19 HFR eq_refl (EX 8%nat 4%nat 19 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 9%nat 3%nat 18 HFR eq_refl (EX 9%nat 3%nat 18 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 10%nat 2%nat 9 HFR eq_refl (EX 10%nat 2%nat 9 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 11%nat 1%nat 8 HFR eq_refl (EX 11%nat 1%nat 8 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 12%nat 0%nat 1 HFR eq_refl (EX 12%nat 0%nat 1 ltac:(lia) eq_refl eq_refl) eq_refl).
- apply pairwise_disjoint_of_extents. unfold hs7_ssMIX, hs7_rG, hs7_rFrame, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_HOST. repeat split; lia.
- unfold facts_ok, hs7_fFR.
  cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U22.
  repeat match goal with |- _ /\ _ => split end;
  try exact I;
  try (change (2 ^ 4) with 16; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia;
       rewrite Z_mod_plus_full; exact Hsp16);
  try (change (2 ^ 3) with 8; first [exact Hc8 | unfold A_G_REC; reflexivity]);
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
Qed.

(* MIX 0x8b2f0: the digest is stored, the frame is reloaded, the call returns *)
Lemma hs_seg_mix : forall x, ST_MIX B MT x.
Proof.
intros x. unfold ST_MIX.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b2 CX MID Eb0 Eb1 Eb2 HREP HR0 R10.
destruct x as [ly S W regs mem md ch pl ptok ps line toks R O].
unfold hs_cx in CX; cbv zeta in CX.
unfold hs_mid in MID; cbv zeta in MID.
unfold hs_regs0 in HR0; cbv zeta in HR0.
destruct HR0 as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
destruct MID as (HJ & Hk & MLE & HBB & HFR & HBA).
unfold hs_ba in HBA; cbv zeta in HBA.
destruct HBA as (HPerm & HRest1 & HRest2 & HO1a & HO1b & HNw & HO1R).
destruct CX as (HPRE & HROD & HRO & HROin & HGUARD & Hr10 & Hr11 & Hr12 & Hnt & HSTRL & Hpt0 & Hpt8 & HTOK &
  Hlps & Hps & HF2 & HWL & HREPA & Hfr8 & Hev & Hlive & HMOK & HTAILS).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
cbn [i_ly i_S i_W i_regs i_mem i_md i_ch i_pl i_ptok i_ps i_line i_toks i_R i_O] in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof (hs_slot_bounds R) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (hh_MTL B MT HH) as MTL.
assert (WS : 112 + ASTACK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hsp0 : alloc_ceiling <= spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
assert (Hslot : A_G_REC + OFF_CALLS <= hs_slot R <= A_REC_SPILL).
{ clear - Hs1 Hs2. unfold CALL_SIZE, SC_SIZE in Hs2. lia. }
destruct (hs_rec_hostval B lyc Sc (rdW Wc memc) (rec_record R REC_HOST_SETTING (hs_args line toks))
  (O1 ++ [b0; b1; b2]) HREP) as [Hh0 Hh0r].
rewrite hs7_rhost_rec in Hh0, Hh0r.
assert (Usp : bv_unsigned (getr regs1 2) = spZ regs - 112)
  by (rewrite R2; apply unsigned_lit_small; clear - Hsp0 C1; lia).
pose proof (hs7_seed_MIX Wc regs1 regs memc lyc Sc mdc (spZ regs) (hs_slot R) (r_host R) HARc Usp
  ltac:(clear - Hsp0 C1; lia) ltac:(clear - Hsp0; lia) Hal16
  R8 Hslot Hs3 R22 HFR Hh0 Hh0r) as HS.
unfold hs_at.
set (E := Eimg (Ereg regs1 (hs7_extra regs (r_host R)))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HEX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (hs7_extra regs (r_host R)) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U22 : bv_unsigned (ew E 22) = A_G_REC)
  by (rewrite (HEE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (SHOK : sh_ok SEGS hs7_Bx (@nil shent) E (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HV : 0 <= mixcall (r_host R) REC_HOST_SETTING (hs_args line toks) < 2 ^ 64)
  by (apply mixcall_range; exact Hh0r).
assert (U10 : sv_denot E (SOff 10 0) = Z_to_bv 64 (mixcall (r_host R) REC_HOST_SETTING (hs_args line toks))).
{ cbn [sv_denot]. rewrite (HEE 10%nat 10%bv eq_refl), R10, Z.add_0_r.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
change (mkst regs1 (Z_to_bv 64 (BASE + HS_MIX)) memc (seg_rom SEGS)) with
  (mkst regs1 (Z_to_bv 64 (BASE + HS_MIX)) memc (seg_rom SEGS)) in HS.
paj_run_tok RUN HS HJ SHOK hs7_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?bl0 ?blc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp bl0 blc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U22 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    apply (recb_grec_awr_m B (hh_HB B MT HH) (hh_prog_img B MT HH)); [apply hs7_inFP_grec|];
    unfold REC_SIZE in *; lia. }
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the run stored the digest and reloaded the 13 saved registers; the frame is read-only, so every byte of the
   recorder outside g_rec.host_settings is kept *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_HOST <= a < A_G_REC + OFF_HOST + 8) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hno.
  apply (kept_of_frame E (ss_mem hs7_ssMIX) (w_H Wc) memc (ms_mem ms)
    (fun a => A_G_REC + OFF_HOST <= a < A_G_REC + OFF_HOST + 8) HFr); [| exact Ha | exact Hno].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; inversion Hq; subst;
  cbn [base_val] in Hrr; rewrite ?U2, ?U22 in Hrr; unfold A_G_REC, OFF_HOST in *; lia. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (EXs : forall i j r, (i < 13)%nat -> (i + j = 12)%nat -> nth_error HS_SAVED j = Some r ->
  ew E (33 + i)%nat = getr regs (Z_to_bv 5 r)).
{ intros i j r Hi Hij Hn. change (33 + i)%nat with (32 + (1 + i))%nat. rewrite HEX by lia.
  assert (Hj : j = (12 - i)%nat) by lia. subst j.
  do 13 (destruct i as [|i]; [cbn in Hn; injection Hn as <-; reflexivity|]). lia. }
assert (A33 : ew E 33 = getr regs 27%bv)
  by (rewrite <- (hs7_bv5_eq 27 27%bv ltac:(vm_compute; reflexivity)); exact (EXs 0%nat 12%nat 27 ltac:(lia) eq_refl eq_refl)).
assert (A34 : ew E 34 = getr regs 26%bv)
  by (rewrite <- (hs7_bv5_eq 26 26%bv ltac:(vm_compute; reflexivity)); exact (EXs 1%nat 11%nat 26 ltac:(lia) eq_refl eq_refl)).
assert (A35 : ew E 35 = getr regs 25%bv)
  by (rewrite <- (hs7_bv5_eq 25 25%bv ltac:(vm_compute; reflexivity)); exact (EXs 2%nat 10%nat 25 ltac:(lia) eq_refl eq_refl)).
assert (A36 : ew E 36 = getr regs 24%bv)
  by (rewrite <- (hs7_bv5_eq 24 24%bv ltac:(vm_compute; reflexivity)); exact (EXs 3%nat 9%nat 24 ltac:(lia) eq_refl eq_refl)).
assert (A37 : ew E 37 = getr regs 23%bv)
  by (rewrite <- (hs7_bv5_eq 23 23%bv ltac:(vm_compute; reflexivity)); exact (EXs 4%nat 8%nat 23 ltac:(lia) eq_refl eq_refl)).
assert (A38 : ew E 38 = getr regs 22%bv)
  by (rewrite <- (hs7_bv5_eq 22 22%bv ltac:(vm_compute; reflexivity)); exact (EXs 5%nat 7%nat 22 ltac:(lia) eq_refl eq_refl)).
assert (A39 : ew E 39 = getr regs 21%bv)
  by (rewrite <- (hs7_bv5_eq 21 21%bv ltac:(vm_compute; reflexivity)); exact (EXs 6%nat 6%nat 21 ltac:(lia) eq_refl eq_refl)).
assert (A40 : ew E 40 = getr regs 20%bv)
  by (rewrite <- (hs7_bv5_eq 20 20%bv ltac:(vm_compute; reflexivity)); exact (EXs 7%nat 5%nat 20 ltac:(lia) eq_refl eq_refl)).
assert (A41 : ew E 41 = getr regs 19%bv)
  by (rewrite <- (hs7_bv5_eq 19 19%bv ltac:(vm_compute; reflexivity)); exact (EXs 8%nat 4%nat 19 ltac:(lia) eq_refl eq_refl)).
assert (A42 : ew E 42 = getr regs 18%bv)
  by (rewrite <- (hs7_bv5_eq 18 18%bv ltac:(vm_compute; reflexivity)); exact (EXs 9%nat 3%nat 18 ltac:(lia) eq_refl eq_refl)).
assert (A43 : ew E 43 = getr regs 9%bv)
  by (rewrite <- (hs7_bv5_eq 9 9%bv ltac:(vm_compute; reflexivity)); exact (EXs 10%nat 2%nat 9 ltac:(lia) eq_refl eq_refl)).
assert (A44 : ew E 44 = getr regs 8%bv)
  by (rewrite <- (hs7_bv5_eq 8 8%bv ltac:(vm_compute; reflexivity)); exact (EXs 11%nat 1%nat 8 ltac:(lia) eq_refl eq_refl)).
assert (A45 : ew E 45 = getr regs 1%bv)
  by (rewrite <- (hs7_bv5_eq 1 1%bv ltac:(vm_compute; reflexivity)); exact (EXs 12%nat 0%nat 1 ltac:(lia) eq_refl eq_refl)).
(* the digest cell of the end state holds a0 *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let rr := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 0 rr HS ltac:(vm_compute; reflexivity)) as HRg
end.
cbn [ms_mem restrict] in HRg.
pose proof (field_of_region E (mrestrict (w_H Wc) (ms_mem ms)) 22 A_G_REC _ 952 960 952 960 952 8 (SOff 10 0)
  (mixcall (r_host R) REC_HOST_SETTING (hs_args line toks)) HRg U22 ltac:(cbn; tauto) U10
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HV) ltac:(cbn; lia)) as Vh.
(* the return *)
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold hs_post, hs_Q. cbv zeta.
cbn [i_ly i_S i_W i_regs i_mem i_md i_line i_toks i_R i_O].
unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyc, Sc, r, m, d end.
split.
{ rewrite F1, A45. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  eapply (ajournal_mono_k SEGS B); [exact HJ|].
  unfold hs_k5, hs_k4, hs_k3, hs_k2, hs_k0, EV_SUP_HOST_SETTING in *.
  cbn [i_R i_line i_toks] in *. lia. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcase : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat match type of Hcase with _ \/ _ => destruct Hcase as [Hcase | Hcase] end; subst r.
  - rewrite (hs7_bv5_eq 2 2%bv ltac:(vm_compute; reflexivity)), F2, U2.
    replace (spZ regs - 112 + 112) with (spZ regs) by lia.
    unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (hs7_bv5_eq 3 3%bv ltac:(vm_compute; reflexivity)), F3, (HEE 3%nat 3%bv eq_refl). exact R3.
  - rewrite (hs7_bv5_eq 4 4%bv ltac:(vm_compute; reflexivity)), F4, (HEE 4%nat 4%bv eq_refl). exact R4.
  - rewrite (hs7_bv5_eq 8 8%bv ltac:(vm_compute; reflexivity)), F8. exact A44.
  - rewrite (hs7_bv5_eq 9 9%bv ltac:(vm_compute; reflexivity)), F9. exact A43.
  - rewrite (hs7_bv5_eq 18 18%bv ltac:(vm_compute; reflexivity)), F18. exact A42.
  - rewrite (hs7_bv5_eq 19 19%bv ltac:(vm_compute; reflexivity)), F19. exact A41.
  - rewrite (hs7_bv5_eq 20 20%bv ltac:(vm_compute; reflexivity)), F20. exact A40.
  - rewrite (hs7_bv5_eq 21 21%bv ltac:(vm_compute; reflexivity)), F21. exact A39.
  - rewrite (hs7_bv5_eq 22 22%bv ltac:(vm_compute; reflexivity)), F22. exact A38.
  - rewrite (hs7_bv5_eq 23 23%bv ltac:(vm_compute; reflexivity)), F23. exact A37.
  - rewrite (hs7_bv5_eq 24 24%bv ltac:(vm_compute; reflexivity)), F24. exact A36.
  - rewrite (hs7_bv5_eq 25 25%bv ltac:(vm_compute; reflexivity)), F25. exact A35.
  - rewrite (hs7_bv5_eq 26 26%bv ltac:(vm_compute; reflexivity)), F26. exact A34.
  - rewrite (hs7_bv5_eq 27 27%bv ltac:(vm_compute; reflexivity)), F27. exact A33. }
exists (O1 ++ [b0; b1; b2]).
split.
{ unfold sup_host_setting_m. cbv zeta. unfold rec_mix_host. cbn [fst snd].
  rewrite hs7_rhost_rec.
  change [canon line; dec (Z.of_nat (length toks)); join_sp toks] with (hs_args line toks).
  apply (hs_rec_host B lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms))
    (rec_record R REC_HOST_SETTING (hs_args line toks)) (O1 ++ [b0; b1; b2])
    (mixcall (r_host R) REC_HOST_SETTING (hs_args line toks)) HREP HV).
  - change (N.to_nat 8) with 8%nat in Vh. apply (aval_mem_view SEGS). exact Vh.
  - intros a Ha Hno. apply KEEP; [|exact Hno].
    destruct Ha as [Ha | (pn & Hpn & Ha)].
    + unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
    + destruct (hs7_own_bounds lyc Sc Wc memc mdc (rdW Wc memc) _ _ pn HARc HREP Hpn) as (_ & Hp4 & Hpc & Hpn0).
      lia. }
split.
{ intros pn Hpn. apply in_app_or in Hpn as [Hp | Hp].
  - left. exact (HO1b pn Hp).
  - destruct (in_dec hs7_pair_dec pn (ablocks B ly S)) as [Hin | Hin].
    + left. exact (HNw pn Hp Hin).
    + right. exact Hin. }
split.
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right.
  exact (HRest2 pn Hpn Hno). }
split.
{ intros pn Hpn. apply (Permutation_in _ HPerm) in Hpn. apply in_app_or in Hpn as [Hn | Hr].
  - right. apply in_or_app. right. exact Hn.
  - destruct (in_dec hs7_pair_dec pn O) as [Hin | Hin].
    + right. apply in_or_app. left. exact (HO1a pn Hr Hin).
    + left. split; [exact (HRest1 pn Hr) | exact Hin]. }
split.
{ assert (Htoks : toks <> []) by (intros Ht; rewrite Ht in Hnt; cbn in Hnt; lia).
  pose proof (hs7_join_len toks Htoks) as HJL.
  unfold bsum in HBB. cbn [fold_right] in HBB. rewrite Eb0, Eb1, Eb2 in HBB.
  unfold LIVE_SUP_HOST_SETTING. lia. }
apply (mle_weaken MT S Sc _ _ MTL MLE).
unfold hs_m5, hs_m4, hs_m3, hs_m2, hs_m0, XM_SUP_HOST_SETTING.
cbn [i_R i_line i_toks]. lia.
Qed.
(* a read-only byte of the image is outside the call's footprint *)
Lemma hs7_ro_notFP : forall ly S (W : world SEGS) mem md R O,
AR SEGS B ly S W mem md -> rec_repA B ly S (aview SEGS (w_H W) mem) R O ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md R O HAR HREP a Hro Hin.
destruct (hh_ro_prog_apart B MT HH a Hro) as [Himg Hpg].
unfold hs_FP in Hin. apply inFP_cons in Hin. destruct Hin as [Ha | Hin].
{ apply Hpg. apply recb_grec_in. exact Ha. }
apply inFP_cons in Hin. destruct Hin as [Ha | Hin].
{ apply Hpg. apply recb_spill_in. exact Ha. }
destruct (inFP_ablocks_fp_inv O a Hin) as (p & n & Hpn & Ha).
exact (recb_heap_noimg_m B ly S W mem md p n a HAR (proj1 (hs_rec_own B ly S _ R O HREP (p, n) Hpn)) Ha Himg).
Qed.

(* the seed at FR: the digest cell is only read here, so both regions are read-only *)
Lemma hs7_seed_FR : forall (W : world SEGS) (regs1 regs : bvmap 5 word) memc sp0 c h0,
bv_unsigned (getr regs1 2) = sp0 - 112 -> 2 ^ 46 <= sp0 - 112 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
getr regs1 8 = w64 c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL -> c mod 8 = 0 ->
getr regs1 22 = w64 A_G_REC ->
hs_frame (aview SEGS (w_H W) memc) sp0 regs ->
aval_mem (aview SEGS (w_H W) memc) (A_G_REC + OFF_HOST) 8 h0 -> 0 <= h0 < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hs7_extra regs h0))) hs7_ssFR
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_FR)) memc (seg_rom SEGS))).
Proof.
intros W regs1 regs memc sp0 c h0 Usp Hsp1 Hsp2 Hsp16 R8 Hc1 Hc8 R22 HFR Hh Hh64.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (hs7_extra regs h0))) in *.
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HEX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (hs7_extra regs h0) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U2 : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (HEE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U22 : bv_unsigned (ew E 22) = A_G_REC)
  by (rewrite (HEE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U32 : ew E 32 = Z_to_bv 64 h0) by (change 32%nat with (32 + 0)%nat; rewrite HEX by lia; reflexivity).
assert (EX : forall i j r, (i < 13)%nat -> (i + j = 12)%nat -> nth_error HS_SAVED j = Some r ->
  ew E (33 + i)%nat = getr regs (Z_to_bv 5 r)).
{ intros i j r Hi Hij Hn. change (33 + i)%nat with (32 + (1 + i))%nat. rewrite HEX by lia.
  assert (Hj : j = (12 - i)%nat) by lia. subst j.
  do 13 (destruct i as [|i]; [cbn in Hn; injection Hn as <-; reflexivity|]). lia. }
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hs7_ssFR, hs7_rG, hs7_rFrame. cbn [ss_mem].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [unfold A_G_REC, OFF_HOST; lia|]. split; [unfold A_G_REC, OFF_HOST; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_HOST 8 (SOff 32 0) h0).
    * cbn [sv_denot]. rewrite U32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * change (N.to_nat 8) with 8%nat. apply val_mem_view. exact Hh.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (hs7_chunk_fr E W memc sp0 regs 0%nat 12%nat 27 HFR eq_refl (EX 0%nat 12%nat 27 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 1%nat 11%nat 26 HFR eq_refl (EX 1%nat 11%nat 26 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 2%nat 10%nat 25 HFR eq_refl (EX 2%nat 10%nat 25 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 3%nat 9%nat 24 HFR eq_refl (EX 3%nat 9%nat 24 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 4%nat 8%nat 23 HFR eq_refl (EX 4%nat 8%nat 23 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 5%nat 7%nat 22 HFR eq_refl (EX 5%nat 7%nat 22 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 6%nat 6%nat 21 HFR eq_refl (EX 6%nat 6%nat 21 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 7%nat 5%nat 20 HFR eq_refl (EX 7%nat 5%nat 20 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 8%nat 4%nat 19 HFR eq_refl (EX 8%nat 4%nat 19 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 9%nat 3%nat 18 HFR eq_refl (EX 9%nat 3%nat 18 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 10%nat 2%nat 9 HFR eq_refl (EX 10%nat 2%nat 9 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 11%nat 1%nat 8 HFR eq_refl (EX 11%nat 1%nat 8 ltac:(lia) eq_refl eq_refl) eq_refl).
    * exact (hs7_chunk_fr E W memc sp0 regs 12%nat 0%nat 1 HFR eq_refl (EX 12%nat 0%nat 1 ltac:(lia) eq_refl eq_refl) eq_refl).
- apply pairwise_disjoint_of_extents. unfold hs7_ssFR, hs7_rG, hs7_rFrame, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_HOST. repeat split; lia.
- unfold facts_ok, hs7_fFR.
  cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U22.
  repeat match goal with |- _ /\ _ => split end;
  try exact I;
  try (change (2 ^ 4) with 16; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia;
       rewrite Z_mod_plus_full; exact Hsp16);
  try (change (2 ^ 3) with 8; first [exact Hc8 | unfold A_G_REC; reflexivity]);
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
Qed.

(* FR 0x8b2e4: a0 := g_rec.host_settings, a1 := c, then the call of mix_call *)
Lemma hs_seg_fr : forall x, ST_MIX B MT x -> ST_FR B MT x.
Proof.
intros x MIXN. unfold ST_FR.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b2 CX MID Eb0 Eb1 Eb2 HREP HR0.
destruct x as [ly S W regs mem md ch pl ptok ps line toks R O].
pose proof CX as CXc. unfold hs_cx in CXc; cbv zeta in CXc.
pose proof MID as MIDc. unfold hs_mid in MIDc; cbv zeta in MIDc.
pose proof HR0 as HR0c. unfold hs_regs0 in HR0c; cbv zeta in HR0c.
destruct HR0c as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
destruct MIDc as (HJ & Hk & MLE & HBB & HFR & HBA).
unfold hs_ba in HBA; cbv zeta in HBA.
destruct HBA as (HPerm & HRest1 & HRest2 & HO1a & HO1b & HNw & HO1R).
destruct CXc as (HPRE & HROD & HRO & HROin & HGUARD & Hr10 & Hr11 & Hr12 & Hnt & HSTRL & Hpt0 & Hpt8 & HTOK &
  Hlps & Hps & HF2 & HWL & HREPA & Hfr8 & Hev & Hlive & HMOK & HTAILS).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
cbn [i_ly i_S i_W i_regs i_mem i_md i_ch i_pl i_ptok i_ps i_line i_toks i_R i_O] in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof (hs_slot_bounds R) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (hh_MTL B MT HH) as MTL.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : 112 + ASTACK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (WSM : 112 + MIX_CALL_STK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HES : MIX_CALL_STK = 4176) by reflexivity.
assert (Hsp0 : alloc_ceiling <= spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
assert (Hsp1 : alloc_ceiling + 16384 <= spZ regs) by (clear - Hceil Hslo Hstk0 WS HAS; lia).
assert (Hslot : A_G_REC + OFF_CALLS <= hs_slot R <= A_REC_SPILL).
{ clear - Hs1 Hs2. unfold CALL_SIZE, SC_SIZE in Hs2. lia. }
destruct (hs_rec_hostval B lyc Sc (rdW Wc memc) (rec_record R REC_HOST_SETTING (hs_args line toks))
  (O1 ++ [b0; b1; b2]) HREP) as [Hh0 Hh0r].
rewrite hs7_rhost_rec in Hh0, Hh0r.
assert (Usp : bv_unsigned (getr regs1 2) = spZ regs - 112)
  by (rewrite R2; apply unsigned_lit_small; clear - Hsp0 C1; lia).
pose proof (hs7_seed_FR Wc regs1 regs memc (spZ regs) (hs_slot R) (r_host R) Usp
  ltac:(clear - Hsp0 C1; lia) ltac:(clear - Hsp0; lia) Hal16 R8 Hslot Hs3 R22 HFR Hh0 Hh0r) as HS.
unfold hs_at.
set (E := Eimg (Ereg regs1 (hs7_extra regs (r_host R)))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HEX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (hs7_extra regs (r_host R)) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U8 : bv_unsigned (ew E 8) = hs_slot R)
  by (rewrite (HEE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small;
      clear - Hslot; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U32 : ew E 32 = Z_to_bv 64 (r_host R))
  by (change 32%nat with (32 + 0)%nat; rewrite HEX by lia; reflexivity).
assert (SHOK : sh_ok SEGS hs7_Bx (@nil shent) E (mrestrict (w_H Wc) memc)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK hs7_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?bl0 ?blc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp bl0 blc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the two instructions write nothing *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha.
  apply (kept_of_frame E (ss_mem hs7_ssFR) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
  [| exact Ha | intros Hf; exact Hf].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; inversion Hq; subst; cbn [base_val] in Hrr; lia. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (11%bv : bv 5) F11.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
assert (F1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + HS_MIX)) by (rewrite F1; unfold HS_MIX; reflexivity).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))).
{ apply (arodata_ok_journalP SEGS RLO RHI (hh_RELRO_IMG B MT HH) (RO := hh_RRO B MT HH)
    B SUP_HOST_SETTING_STK (spZ regs) (hs_FP O) ly S W mem md [] lyc Sc Wc (ms_mem ms) _ _ HJ
    (hs7_ro_notFP ly S W mem md R O HAR0 HREPA) HROD). }
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms)))
  by exact (hh_ro_ok_of_aro B MT HH lyc Sc Wc (ms_mem ms) _ (proj1 HJ) HRODc).
destruct (hs_rec_last B lyc Sc (rdW Wc memc) R (hs_args line toks) (O1 ++ [b0; b1; b2]) HREP) as (P & Hcall & HPO).
assert (Hcall2 : acall_at (ablocks B lyc Sc) (rdW Wc (ms_mem ms)) (hs_slot R)
  (REC_HOST_SETTING, hs_args line toks) P).
{ apply (acall_at_agree (ablocks B lyc Sc) (ablocks B lyc Sc) (rdW Wc memc) (rdW Wc (ms_mem ms))
    (hs_slot R) (REC_HOST_SETTING, hs_args line toks) P Hcall).
  - intros i Hi. apply KEEP. unfold CALL_SIZE in Hi.
    clear - Hi Hslot. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
  - intros pn Hpn.
    destruct (hs7_own_bounds lyc Sc Wc memc mdc (rdW Wc memc) _ _ pn HARc HREP (HPO pn Hpn))
      as (Hin & Hp4 & Hpc & Hn0).
    split; [exact Hin|]. intros i Hi. apply KEEP. clear - Hp4 Hpc Hn0 Hi C1. lia. }
assert (Hshape : (exists i, 0 <= i < REC_CALLS_MAX /\ hs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i)
  \/ hs_slot R = A_REC_SPILL).
{ unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
  - left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
  - right. reflexivity. }
assert (H10c : getr (ms_regs ms) 10 = w64 (r_host R)) by (rewrite F10; exact U32).
assert (H11c : getr (ms_regs ms) 11 = w64 (hs_slot R))
  by (rewrite F11, (HEE 8%nat 8%bv eq_refl); exact R8).
assert (Hnevc : st_nev Sc + EV_MIX_CALL <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  unfold hs_k5, hs_k4, hs_k3, hs_k2, hs_k0 in Hk. cbn [i_R] in Hk.
  unfold EV_SUP_HOST_SETTING in Hev. unfold EV_MIX_CALL. lia. }
assert (Hsp2 : spZ (ms_regs ms) = spZ regs + -112)
  by (unfold spZ at 1; rewrite F2, U2; lia).
pmkst HS.
rewrite (hh_sigp B MT HH CS_mix_call ltac:(vm_compute; tauto)).
change (cmd_af CS_mix_call) with AF_mix_call.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_mix_call))
    SUP_HOST_SETTING_STK (spZ regs) (hs_FP O) ly S W mem md [] lyc Sc _ k MIX_CALL_STK [] EV_MIX_CALL (-112)
    (Z_to_bv 64 (BASE + HS_MIX))
    (fun ly2 S2 (W2 : world SEGS) regs2 mem2 md2 =>
      getr regs2 10 = w64 (mixcall (r_host R) REC_HOST_SETTING (hs_args line toks)) /\
      Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc) HJ).
  - exact Hsp2.
  - reflexivity.
  - lia.
  - unfold MIX_CALL_STK, ESTACK. lia.
  - clear - WSM HES. lia.
  - rewrite F3, (HEE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite F4, (HEE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact F1'.
  - apply ret_ok_codeptr_v; [unfold HS_MIX; lia | reflexivity].
  - rewrite unsigned_lit_small; [unfold HS_MIX; lia | unfold HS_MIX; lia].
  - intros HPREc.
    eapply SRr_mono.
    { apply (hh_mix B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (r_host R) (hs_slot R)
        (REC_HOST_SETTING, hs_args line toks) P HPREc HRODc H10c Hh0r H11c Hshape Hcall2 HROc Hnevc). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPc & HKc).
    exists ly2, S2, regs2, mem2, md2. rewrite F1' in Hc2.
    split; [exact Hc2|]. split; [exact HJc|]. split; [exact HPc|]. cbn [fst snd] in HKc. exact HKc.
  - intros a (rg & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJin & HP2 & HK10 & HKperm & Ely2 & ES2).
assert (PRES : forall (z : Z) (rr : bv 5), bv_unsigned rr = z -> acallee_saved z ->
  getr regs2 rr = getr (ms_regs ms) rr).
{ intros z rr Hz Hc. rewrite <- (hs7_bv5_eq z rr Hz). rewrite (HP2 z Hc). rewrite (hs7_bv5_eq z rr Hz). reflexivity. }
pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & Hkeep & Hblk & Himgk & _).
apply (MIXN ly2 S2 W2 mem2 md2 regs2 (k + EV_MIX_CALL) O1 Rest b0 b1 b2).
- exact CX.
- unfold hs_mid. cbv zeta. cbn [i_ly i_S i_W i_regs i_mem i_md i_O i_R i_line i_toks].
  split; [exact HJ2|].
  split.
  { unfold EV_MIX_CALL. unfold hs_k5, hs_k4, hs_k3, hs_k2, hs_k0 in Hk |- *. cbn [i_R] in Hk |- *. lia. }
  split.
  { eapply (mle_weaken MT S S2); [exact MTL | |].
    - apply (mle_station MT S Sc S2 _ 0 MTL MLE).
      rewrite ES2. exact (mo_le_refl MT MTL Sc).
    - lia. }
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HKperm), <- (blocks_bytes_bsum B lyc Sc). exact HBB. }
  split.
  { intros j r Hj kk Hkk.
    pose proof (hs7_saved_lt j r Hj) as Hj13.
    rewrite (Hkeep (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat kk)
      ltac:(clear - Hsp0 Hsp1 Hj13 Hkk C1; lia) ltac:(clear - Hj13 Hkk; lia) (inFP_nil _)).
    rewrite (KEEP (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(clear - Hsp0 Hsp1 Hj13 Hkk C1; lia)).
    exact (HFR j r Hj kk Hkk). }
  unfold hs_ba. cbv zeta. cbn [i_ly i_S i_O].
  split; [exact (Permutation_trans HKperm HPerm)|].
  split; [exact HRest1|]. split; [exact HRest2|]. split; [exact HO1a|]. split; [exact HO1b|].
  split; [exact HNw | exact HO1R].
- exact Eb0.
- exact Eb1.
- exact Eb2.
- cbn [i_R i_line i_toks].
  apply (hs_rec_kept B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2)
    (rec_record R REC_HOST_SETTING (hs_args line toks)) (O1 ++ [b0; b1; b2]) HREP).
  + intros a Ha.
    assert (Hab : 0 <= a < 2 ^ 64).
    { destruct Ha as [Har | (pn & Hpn & Har)].
      - clear - Har. unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Har. lia.
      - destruct (hs7_own_bounds lyc Sc Wc memc mdc (rdW Wc memc) _ _ pn HARc HREP Hpn)
          as (_ & Hp4 & Hpc & Hn0). clear - Har Hp4 Hpc Hn0 C1. lia. }
    rewrite <- (KEEP a Hab).
    destruct Ha as [Har | (pn & Hpn & Har)].
    * destruct (recb_prog_unowned_m B (hh_HB B MT HH) (hh_prog_img B MT HH) a
        ltac:(clear - Har; destruct Har as [Hg | Hs];
        [apply recb_grec_in; lia | apply recb_spill_in; lia])) as (Hi1 & Hi2 & Hi3).
      exact (Himgk a Hi1 Hi2 Hi3 (fp_spares_closed [] a sink_closed_nil (inFP_nil a))).
    * destruct pn as [p n]. cbn [fst snd] in Har.
      destruct (hs7_own_bounds lyc Sc Wc memc mdc (rdW Wc memc) _ _ (p, n) HARc HREP Hpn)
        as (Hin & Hp4 & Hpc & Hn0). cbn [fst snd] in Hin, Hp4, Hpc, Hn0.
      pose proof (req_size_pos n Hn0) as Hrq.
      replace a with (p + (a - p)) by lia.
      exact (Hblk p n (a - p) Hin (Permutation_in _ (Permutation_sym HKperm) Hin) ltac:(lia) (inFP_nil _)).
  + intros pn Hpn. apply (Permutation_in _ (Permutation_sym HKperm)).
    exact (proj1 (hs_rec_own B lyc Sc (rdW Wc memc) _ _ HREP pn Hpn)).
- unfold hs_regs0. cbv zeta. cbn [i_regs i_toks i_R].
  split; [rewrite (PRES 2 2%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F2,
    (HEE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite (PRES 3 3%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F3,
    (HEE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite (PRES 4 4%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F4,
    (HEE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite (PRES 8 8%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F8,
    (HEE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite (PRES 9 9%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F9,
    (HEE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite (PRES 22 22%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F22,
    (HEE 22%nat 22%bv eq_refl); exact R22|].
  rewrite (PRES 23 23%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F23,
    (HEE 23%nat 23%bv eq_refl). exact R23.
- cbn [i_R i_line i_toks]. exact HK10.
Qed.

Lemma hs7_slot_awr : forall R O STK sp0 bl0 blc fr0 ly own o, 0 <= o < CALL_SIZE ->
awr_byte SEGS B STK sp0 (hs_FP O) bl0 blc fr0 ly own (hs_slot R + o).
Proof.
intros R O STK sp0 bl0 blc fr0 ly own o Ho. pose proof (hs7_slot_pg R o Ho) as HP.
right; right; right; right; left. split; [exact (hs7_slot_FP R O o Ho)|].
split; [rewrite (recb_ts_prog_m B (hh_HB B MT HH)); exact HP | exact (hh_prog_img B MT HH _ HP)].
Qed.

(* the seed at XS: s3 = c + 4, s8 = its shadow byte's address; the nargs cell and the third argument slot *)
Lemma hs7_seed_XS : forall (W : world SEGS) (regs1 : bvmap 5 word) memc ly S md sp0 c,
AR SEGS B ly S W memc md ->
bv_unsigned (getr regs1 2) = sp0 - 112 -> 2 ^ 46 <= sp0 - 112 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL -> c mod 8 = 0 ->
(c + CALL_SIZE <= A_G_REC + OFF_ANSWER \/ c = A_REC_SPILL) ->
(forall o, 0 <= o < CALL_SIZE -> Exists (in_zr (c + o)) recb_PG) ->
getr regs1 8 = w64 c -> getr regs1 23 = w64 HS_SB ->
getr regs1 19 = w64 (c + 4) -> getr regs1 24 = w64 (HS_SB + (c + 4) / 8) ->
aval_mem (aview SEGS (w_H W) memc) (c + CALL_OFF_NARGS) 4 2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) hs7_ssXS
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_XS)) memc (seg_rom SEGS))) /\
sh_ok SEGS hs7_Bx hs7_SHXS (Eimg (Ereg regs1 [])) (mrestrict (w_H W) memc).
Proof.
intros W regs1 memc ly S md sp0 c HAR Usp Hsp1 Hsp2 Hsp16 Hc1 Hc8 Hc4 HPG R8 R23 R19 R24 Hnargs.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 [])).
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Hc64 : 0 <= c < 2 ^ 64) by (clear - Hc1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (HEE 8%nat 8%bv eq_refl); exact R8).
assert (E23 : ew E 23 = Z_to_bv 64 HS_SB) by (rewrite (HEE 23%nat 23%bv eq_refl); exact R23).
assert (U2 : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; exact Hc64).
assert (U23 : bv_unsigned (ew E 23) = HS_SB) by (rewrite E23; apply unsigned_lit_small; unfold HS_SB; lia).
assert (HW : forall o, 0 <= o < CALL_SIZE -> writable_at SEGS (mrestrict (w_H W) memc) (c + o))
  by (intros o Ho; exact (hh_prog_writable B MT HH ly S W memc md (c + o) HAR (HPG o Ho))).
split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_rereg; [| reflexivity |].
    * apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
      rewrite R24. unfold hs7_shx.
      rewrite (denot_shx E 8 23 4 c HS_SB E8 E23 ltac:(lia) ltac:(lia)
        ltac:(clear - Hc1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia) ltac:(unfold HS_SB; lia)).
      reflexivity.
    * rewrite R19. cbn [sv_denot]. rewrite U8. reflexivity.
  + vm_compute. reflexivity.
  + unfold hs7_ssXS, hs7_rXSn, hs7_rXSa. cbn [ss_mem].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [clear - Hc1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
      split; [intros o Ho; apply HW; unfold CALL_SIZE; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | cbn; lia |].
      change (N.to_nat 4) with 4%nat. apply val_mem_view. exact Hnargs.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [clear - Hc1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
      split; [intros o Ho; apply HW; unfold CALL_SIZE; lia | apply Forall_nil].
  + apply pairwise_disjoint_of_extents. unfold hs7_ssXS, hs7_rXSn, hs7_rXSa, extent_of_region.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold facts_ok, hs7_fXS.
    cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U23.
    repeat match goal with |- _ /\ _ => split end;
    try exact I;
    try (change (2 ^ 4) with 16; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia;
         rewrite Z_mod_plus_full; exact Hsp16);
    try (change (2 ^ 3) with 8; exact Hc8);
    try (change (2 ^ 0) with 1; apply Z.mod_1_r);
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS, HS_SB in *; lia.
- unfold sh_ok, hs7_SHXS. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) memc E hs7_Bx 8 c CALL_SIZE c 0 56).
  + destruct Hc4 as [Hg | Hsp].
    * apply (cmd_addressable_in SEGS B LAWS (hh_HB B MT HH) ly S W memc md
        (0xada00, 0x5e3b00 - 0xada00) c CALL_SIZE HAR);
      [unfold Tfib_zero_shadow; cbn; tauto | reflexivity | reflexivity | cbn [fst] | cbn [fst snd]];
      clear - Hc1 Hg; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia.
    * apply (cmd_addressable_in SEGS B LAWS (hh_HB B MT HH) ly S W memc md
        (0x5e3be0, 0x5e3c18 - 0x5e3be0) c CALL_SIZE HAR);
      [unfold Tfib_zero_shadow; cbn; tauto | reflexivity | reflexivity | cbn [fst] | cbn [fst snd]];
      rewrite Hsp; unfold A_REC_SPILL, CALL_SIZE; lia.
  + unfold hs7_Bx. rewrite (U_atom E 23 HS_SB E23 ltac:(unfold HS_SB; lia)). reflexivity.
  + exact (U_atom E 8 c E8 Hc64).
  + lia.
  + unfold CALL_SIZE. lia.
  + intros y Hy. clear - Hy Hc1. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, SHADOW_OFF in *. lia.
Qed.

(* XS 0x8b2a8: nargs := 3, c->args[2] := q, then the free wrapper on the word list *)
Lemma hs_seg_xs : forall x, ST_FR B MT x -> ST_XS B MT x.
Proof.
intros x FRN. unfold ST_XS.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w q CX MID Eb0 Eb1 HREP HQS HQA HR1 R20 Hw4 R10 Hq4.
destruct x as [ly S W regs mem md ch pl ptok ps line toks R O].
pose proof CX as CXc. unfold hs_cx in CXc; cbv zeta in CXc.
pose proof MID as MIDc. unfold hs_mid in MIDc; cbv zeta in MIDc.
unfold hs_regs1, hs_regs0 in HR1; cbv zeta in HR1.
destruct HR1 as ((R2 & R3 & R4 & R8 & R9 & R22 & R23) & R19 & R24).
destruct MIDc as (HJ & Hk & MLE & HBB & HFR & HBA).
unfold hs_ba in HBA; cbv zeta in HBA.
destruct HBA as (HPerm & HRest1 & HRest2 & HO1a & HO1b & HNw & HO1R).
destruct CXc as (HPRE & HROD & HRO & HROin & HGUARD & Hr10 & Hr11 & Hr12 & Hnt & HSTRL & Hpt0 & Hpt8 & HTOK &
  Hlps & Hps & HF2 & HWL & HREPA & Hfr8 & Hev & Hlive & HMOK & HTAILS).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold hs_wsz, hs_A2 in *.
cbn [i_ly i_S i_W i_regs i_mem i_md i_ch i_pl i_ptok i_ps i_line i_toks i_R i_O] in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof (hs_slot_bounds R) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (hh_MTL B MT HH) as MTL.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : 112 + ASTACK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hsp0 : alloc_ceiling <= spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
assert (Hsp1 : alloc_ceiling + 16384 <= spZ regs) by (clear - Hceil Hslo Hstk0 WS HAS; lia).
assert (Hslot : A_G_REC + OFF_CALLS <= hs_slot R <= A_REC_SPILL).
{ clear - Hs1 Hs2. unfold CALL_SIZE, SC_SIZE in Hs2. lia. }
(* the word list's block and its copy's block *)
assert (Hwin : In (w, hs_words_len toks + 1) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. right; right; left. reflexivity. }
assert (Hqin : In (q, LIVE_XSTRDUP (join_sp toks)) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. right; right; right; left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ q _ HARc Hqin) as (_ & Hq4096 & Hqceil & _ & _ & _ & [Hqn0 _]).
pose proof (req_size_pos _ Hqn0) as Hqrq.
assert (ND : List.NoDup ([b0; b1; (w, hs_words_len toks + 1); (q, LIVE_XSTRDUP (join_sp toks))] ++ Rest))
  by exact (Permutation_NoDup HPerm (recb_ablocks_nodup_m B lyc Sc Wc memc mdc HARc)).
cbn [app] in ND.
apply NoDup_cons_iff in ND as [Nb0 ND]. apply NoDup_cons_iff in ND as [Nb1 ND].
apply NoDup_cons_iff in ND as [Nwq ND].
(* no block the recorder keeps is the word list's *)
assert (HNW : forall pn, (In pn (O1 ++ [b0; b1]) \/ pn = (q, LIVE_XSTRDUP (join_sp toks))) ->
  pn <> (w, hs_words_len toks + 1)).
{ intros pn [Hpn | ->] Heq.
  - subst pn. apply in_app_or in Hpn as [Ho1 | Hb].
    + apply Nwq. right. exact (HO1R _ Ho1).
    + destruct Hb as [Hb | [Hb | []]].
      * apply Nb0. rewrite Hb. right. left. reflexivity.
      * apply Nb1. rewrite Hb. left. reflexivity.
  - apply Nwq. left. exact Heq. }
assert (HDJ : forall p n, In (p, n) (ablocks B lyc Sc) -> (p, n) <> (w, hs_words_len toks + 1) ->
  forall i, 0 <= i < req_size n -> ~ (w <= p + i < w + req_size (hs_words_len toks + 1))).
{ intros p n Hin Hne i Hi Hwi.
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc p n w _ HARc Hin Hwin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HWIN : forall a, (hs_slot R + 4 <= a < hs_slot R + 8) \/ (hs_slot R + 24 <= a < hs_slot R + 32) ->
  in_img SEGS a).
{ intros a Ha. replace a with (hs_slot R + (a - hs_slot R)) by lia.
  apply (hh_prog_img B MT HH). apply hs7_slot_pg. unfold CALL_SIZE. lia. }
(* the seed *)
assert (Usp : bv_unsigned (getr regs1 2) = spZ regs - 112)
  by (rewrite R2; apply unsigned_lit_small; clear - Hsp0 C1; lia).
destruct (hs_rec_last B lyc Sc (rdW Wc memc) R [canon line; dec (Z.of_nat (length toks))] (O1 ++ [b0; b1]) HREP)
  as (P & Hcall & HPO).
pose proof Hcall as (_ & _ & _ & _ & Hnargs & _).
destruct (hs7_seed_XS Wc regs1 memc lyc Sc mdc (spZ regs) (hs_slot R) HARc Usp
  ltac:(clear - Hsp0 C1; lia) ltac:(clear - Hsp0; lia) Hal16 Hslot Hs3 Hs4 (hs7_slot_pg R) R8 R23 R19 R24 Hnargs)
  as [HS SHOK].
unfold hs_at.
set (E := Eimg (Ereg regs1 [])) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite (HEE 2%nat 2%bv eq_refl); exact Usp).
assert (U8 : bv_unsigned (ew E 8) = hs_slot R)
  by (rewrite (HEE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small;
      clear - Hslot; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (Uq : sv_denot E (SOff 10 0) = Z_to_bv 64 q).
{ cbn [sv_denot]. rewrite (HEE 10%nat 10%bv eq_refl), R10, Z.add_0_r. unfold w64.
  rewrite unsigned_lit_small by (clear - Hq4096 Hqceil Hqrq C1; lia). reflexivity. }
paj_run_tok RUN HS HJ SHOK hs7_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?bl0 ?blc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp bl0 blc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U8 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (hs_slot R + (a - hs_slot R)) by lia.
    apply hs7_slot_awr. unfold CALL_SIZE. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U8 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (hs_slot R + (a - hs_slot R)) by lia.
  apply hs7_slot_awr. unfold CALL_SIZE. lia. }
(* the run wrote only the nargs cell and the third argument slot *)
assert (KEEPX : forall a, 0 <= a < 2 ^ 64 -> ~ (hs_slot R + 4 <= a < hs_slot R + 8) ->
  ~ (hs_slot R + 24 <= a < hs_slot R + 32) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn1 Hn2.
  apply (kept_of_frame E (ss_mem hs7_ssXS) (w_H Wc) memc (ms_mem ms)
    (fun a => (hs_slot R + 4 <= a < hs_slot R + 8) \/ (hs_slot R + 24 <= a < hs_slot R + 32)) HFr);
  [| exact Ha | intros [Hx | Hx]; [exact (Hn1 Hx) | exact (Hn2 Hx)]].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; inversion Hq; subst; cbn [base_val] in Hrr; rewrite U8 in Hrr; lia. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
assert (F1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + HS_FR)) by (rewrite F1; unfold HS_FR; reflexivity).
assert (Hsp2 : spZ (ms_regs ms) = spZ regs + -112) by (unfold spZ at 1; rewrite F2, U2; lia).
(* the nargs cell holds 3 and the third argument slot holds q *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg0;
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRg1
end.
cbn [ms_mem restrict] in HRg0, HRg1.
assert (Vn : aval_mem (rdW Wc (ms_mem ms)) (hs_slot R + 4) 4 3).
{ pose proof (field_of_region E (mrestrict (w_H Wc) (ms_mem ms)) 8 (hs_slot R) _ 0 8 4 8 4 4 (SLit 3) 3 HRg0 U8
    ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  apply (aval_mem_view SEGS). exact V. }
assert (Va : aval_mem (rdW Wc (ms_mem ms)) (hs_slot R + 24) 8 q).
{ pose proof (field_of_region E (mrestrict (w_H Wc) (ms_mem ms)) 8 (hs_slot R) _ 24 32 24 32 24 8 (SOff 10 0) q HRg1
    U8 ltac:(cbn; tauto) Uq ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hq4096 Hqceil Hqrq C1; lia)
    ltac:(cbn; lia)) as V.
  apply (aval_mem_view SEGS). exact V. }
(* the free wrapper on the word list *)
pmkst HS. rewrite (pal_free B (hh_TL B MT HH)).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (hh_free B MT HH fx) Wc (ms_regs ms) (ms_mem ms)
    SUP_HOST_SETTING_STK (spZ regs) (hs_FP O) ly S W mem md [] lyc Sc _ k w (hs_words_len toks + 1) (-112)
    (Z_to_bv 64 (BASE + HS_FR)) [] HJ Hwin).
  - rewrite F10, (HEE 20%nat 20%bv eq_refl). exact R20.
  - exact Hsp2.
  - reflexivity.
  - lia.
  - clear - WS HAS. lia.
  - rewrite F3, (HEE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite F4, (HEE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact F1'.
  - apply ret_ok_codeptr_v; [unfold HS_FR; lia | reflexivity].
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
    unfold hs_k4, hs_k3, hs_k2, hs_k0 in Hk. cbn [i_R] in Hk. unfold EV_SUP_HOST_SETTING in Hev. lia.
  - apply (achain_chain_pre lyc _ (spZ (ms_regs ms)) (s0Z (ms_regs ms)) [] (ms_regs ms)).
    + left. split; [left | reflexivity]. unfold s0Z. rewrite F8, (HEE 8%nat 8%bv eq_refl), R8. unfold w64.
      rewrite unsigned_lit_small by (clear - Hslot; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
      clear - Hslot C1. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
    + rewrite Hsp2. clear - Hsp1 Hsp0 C1. lia.
    + reflexivity.
    + unfold raZ. rewrite F1', unsigned_lit_small by (unfold HS_FR; lia). unfold HS_FR. lia.
  - intros Hin0 i Hi.
    pose proof (HNw (w, hs_words_len toks + 1) ltac:(right; right; left; reflexivity) Hin0) as HwO.
    unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
    exact (inFP_ablocks_fp O w _ i HwO Hi).
  - eapply (mok_station MT S Sc); [exact MTL | exact HMOK | exact MLE | exact (mo_free_nonneg MT MTL) |].
    unfold hs_m4, hs_m3, hs_m2, hs_m0, XM_SUP_HOST_SETTING. cbn [i_R i_line i_toks]. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfrm & HK & MLE2 & HJin).
assert (HIN2 : forall pn, In pn (ablocks B lyc Sc) -> pn <> (w, hs_words_len toks + 1) -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn Hne. rewrite El1 in Hpn. rewrite El2.
  apply in_app_or in Hpn as [H | [H | H]]; apply in_or_app; [left; exact H | congruence | right; exact H]. }
assert (PRES : forall (z : Z) (rr : bv 5), bv_unsigned rr = z -> acallee_saved z ->
  getr regs2 rr = getr (ms_regs ms) rr).
{ intros z rr Hz Hc. rewrite <- (hs7_bv5_eq z rr Hz). rewrite (HP2 z Hc). rewrite (hs7_bv5_eq z rr Hz). reflexivity. }
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
assert (KR : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a)
  by (intros a Ha; exact (recb_kept_prog_m B (hh_HB B MT HH) (hh_prog_img B MT HH)
        lyc Sc Wc (ms_mem ms) W2 mem2 _ _ _ a HK Ha)).
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> (p, n) <> (w, hs_words_len toks + 1) ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW Wc (ms_mem ms) (p + i)).
{ intros p n i Hin Hne Hi. apply (HK2 p n i Hin Hi). exact (HDJ p n Hin Hne i Hi). }
(* a byte of a live block other than the word list's is kept by the run and by the free *)
assert (KH : forall p n i, In (p, n) (ablocks B lyc Sc) -> (p, n) <> (w, hs_words_len toks + 1) ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW Wc memc (p + i)).
{ intros p n i Hin Hne Hi. rewrite (KB p n i Hin Hne Hi).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn0).
  apply KEEPX; [clear - Hp4096 Hpceil Hi C1; lia | |];
  intros Hx; apply (recb_heap_noimg_m B lyc Sc Wc memc mdc p n (p + i) HARc Hin ltac:(lia)); apply HWIN;
  [left | right]; exact Hx. }
apply (FRN ly2 S2 W2 mem2 md2 regs2 (k + 1) O1 Rest b0 b1 (q, LIVE_XSTRDUP (join_sp toks))).
- exact CX.
- unfold hs_mid. cbv zeta. cbn [i_ly i_S i_W i_regs i_mem i_md i_O i_R i_line i_toks].
  split; [exact HJ2|].
  split; [unfold hs_k5, hs_k4, hs_k3, hs_k2, hs_k0 in Hk |- *; cbn [i_R] in Hk |- *; lia|].
  split.
  { eapply (mle_weaken MT S S2); [exact MTL | apply (mle_station MT S Sc S2 _ _ MTL MLE MLE2) |].
    unfold hs_m5. lia. }
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), El2, bsum_app.
    rewrite (blocks_bytes_bsum B lyc Sc), El1, bsum_app, bsum_cons in HBB.
    unfold bsum in HBB |- *. cbn [fold_right snd] in HBB |- *. lia. }
  split.
  { intros j r Hj kk Hkk. pose proof (hs7_saved_lt j r Hj) as Hj13.
    rewrite (HK1 (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(clear - Hsp0 Hsp1 Hj13 Hkk C1; lia)
      ltac:(clear - Hj13 Hkk HAS; lia)).
    rewrite (KEEPX (spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(clear - Hsp0 Hsp1 Hj13 Hkk C1; lia)
      ltac:(clear - Hsp1 Hslot Hj13 Hkk C1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia)
      ltac:(clear - Hsp1 Hslot Hj13 Hkk C1; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia)).
    exact (HFR j r Hj kk Hkk). }
  unfold hs_ba. cbv zeta. cbn [i_ly i_S i_O].
  split.
  { rewrite El2.
    assert (PP : Permutation ((w, hs_words_len toks + 1) :: l1 ++ l2)
      ((w, hs_words_len toks + 1) :: [b0; b1; (q, LIVE_XSTRDUP (join_sp toks))] ++ Rest)).
    { eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- El1.
      eapply Permutation_trans; [exact HPerm|].
      apply Permutation_sym. exact (Permutation_middle [b0; b1] ((q, LIVE_XSTRDUP (join_sp toks)) :: Rest)
        (w, hs_words_len toks + 1)). }
    exact (Permutation_cons_inv PP). }
  split; [exact HRest1|]. split; [exact HRest2|]. split; [exact HO1a|]. split; [exact HO1b|].
  split; [|exact HO1R].
  intros pn Hpn Hin0. apply HNw; [|exact Hin0].
  destruct Hpn as [<- | [<- | [<- | []]]]; [left | right; left | right; right; right; left]; reflexivity.
- exact Eb0.
- exact Eb1.
- reflexivity.
- cbn [i_R i_line i_toks]. unfold hs_args.
  replace (O1 ++ [b0; b1; (q, LIVE_XSTRDUP (join_sp toks))])
    with ((O1 ++ [b0; b1]) ++ [(q, LIVE_XSTRDUP (join_sp toks))]) by (rewrite <- app_assoc; reflexivity).
  change [canon line; dec (Z.of_nat (length toks)); join_sp toks]
    with ([canon line; dec (Z.of_nat (length toks))] ++ [join_sp toks]).
  assert (Htoks : toks <> []) by (intros ->; cbn in Hnt; lia).
  pose proof (hs7_join_len toks Htoks) as HJL.
  apply (hs_rec_arg B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2) R [canon line; dec (Z.of_nat (length toks))]
    (O1 ++ [b0; b1]) q (LIVE_XSTRDUP (join_sp toks)) (join_sp toks) HREP).
  + cbn. lia.
  + intros kk Hkk. unfold CALL_OFF_NARGS.
    replace (hs_slot R + 4 + Z.of_nat kk) with (hs_slot R + (4 + Z.of_nat kk)) by lia.
    rewrite KR; [|apply hs7_slot_pg; unfold CALL_SIZE; cbn in Hkk; lia].
    replace (hs_slot R + (4 + Z.of_nat kk)) with (hs_slot R + 4 + Z.of_nat kk) by lia.
    exact (Vn kk Hkk).
  + intros kk Hkk.
    replace (hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [canon line; dec (Z.of_nat (length toks))]) + Z.of_nat kk)
      with (hs_slot R + (24 + Z.of_nat kk)) by (unfold CALL_OFF_ARGS; cbn [length]; lia).
    rewrite KR; [|apply hs7_slot_pg; unfold CALL_SIZE; lia].
    replace (hs_slot R + (24 + Z.of_nat kk)) with (hs_slot R + 24 + Z.of_nat kk) by lia.
    exact (Va kk Hkk).
  + intros a Ha Hn1 Hn2.
    unfold CALL_OFF_NARGS in Hn1. unfold CALL_OFF_ARGS in Hn2. cbn [length] in Hn2.
    destruct Ha as [Har | (pn & Hpn & Har)].
    * assert (HPa : Exists (in_zr a) recb_PG)
        by (destruct Har as [Hg | Hs]; [apply recb_grec_in | apply recb_spill_in]; exact Hs || exact Hg).
      rewrite (KR a HPa). apply KEEPX; [| lia | lia].
      clear - Har. unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Har. lia.
    * destruct pn as [p n]. cbn [fst snd] in Har.
      destruct (hs7_own_bounds lyc Sc Wc memc mdc (rdW Wc memc) _ _ (p, n) HARc HREP Hpn)
        as (Hin & Hp4 & Hpc & Hn0). cbn [fst snd] in Hp4, Hpc, Hn0.
      pose proof (req_size_pos n Hn0) as Hrq.
      replace a with (p + (a - p)) by lia.
      exact (KH p n (a - p) Hin (HNW (p, n) (or_introl Hpn)) ltac:(lia)).
  + lia.
  + apply (astr_atR_agree_in (rdW Wc memc) (rdW W2 mem2) q (LIVE_XSTRDUP (join_sp toks)) q (join_sp toks) HQS).
    * intros i Hi. exact (KH q _ i Hqin (HNW _ (or_intror eq_refl)) ltac:(lia)).
    * lia.
    * unfold LIVE_XSTRDUP. lia.
  + unfold LIVE_XSTRDUP. lia.
  + lia.
  + exact (HIN2 _ Hqin (HNW _ (or_intror eq_refl))).
  + intros pn Hpn.
    exact (HIN2 pn (proj1 (hs_rec_own B lyc Sc _ _ _ HREP pn Hpn)) (HNW pn (or_introl Hpn))).
  + exact HQA.
  + apply (recb_heap_apart_m B lyc Sc Wc memc mdc q _ A_G_REC REC_SIZE HARc Hqin Hqn0 ltac:(unfold REC_SIZE; lia)).
    intros a Ha. exact (hh_prog_img B MT HH a (recb_grec_in a Ha)).
  + apply (recb_heap_apart_m B lyc Sc Wc memc mdc q _ A_REC_SPILL SC_SIZE HARc Hqin Hqn0 ltac:(unfold SC_SIZE; lia)).
    intros a Ha. exact (hh_prog_img B MT HH a (recb_spill_in a Ha)).
- unfold hs_regs0. cbv zeta. cbn [i_regs i_toks i_R].
  split; [rewrite (PRES 2 2%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F2,
    (HEE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite (PRES 3 3%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F3,
    (HEE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite (PRES 4 4%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F4,
    (HEE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite (PRES 8 8%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F8,
    (HEE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite (PRES 9 9%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F9,
    (HEE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite (PRES 22 22%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F22,
    (HEE 22%nat 22%bv eq_refl); exact R22|].
  rewrite (PRES 23 23%bv ltac:(vm_compute; reflexivity) ltac:(unfold acallee_saved; lia)), F23,
    (HEE 23%nat 23%bv eq_refl). exact R23.
Qed.

End e.
End f.
End d.
