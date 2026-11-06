(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first part of sup_policy_set's ASan walk (plugin-hostd/fuzz_command, 0x8b9b0), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and AChc.v (cgif_close: the seed of a walk segment, the run, the step through a program call) and of an earlier version of lib/A/Prog/sup_reply_code.v: the entry, the inlined record() with both arms (the call of rec_calls_free on record.spill when the table holds 16 calls), the two checked stores into the slot, and the walk to the call of xstrdup on the first argument. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4 and 5: the bundled pre
   carries the rounding-mode-0 premise where astack_pres was, the post is apost_baseF, the callees' contracts are taken
   at every FP state; the frame chains at the two calls are achain_low (s0 = the slot, below alloc_ceiling). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_policy_set_s1.v, with its module paths and module names changed; 851 of its 943 lines of code are new or changed and 1422 lines of the source are left out. *)
(* The first segments of sup_host_setting's ASan walk (plugin-hostd/fuzz_command, lib/A/Prog/sup_host_setting_s0.v):
   - hs_seg_entry: from the entry (0x8b094) the prologue, the load of the shadow base through the GOT, the load of
     g_rec.ncalls and the branch of the inlined record(): on the table arm g_rec.ncalls := n + 1 and c := the slot,
     then JOIN; on the spill arm the call of rec_calls_free(&record.spill, 1), then RCF;
   - hs_seg_rcf: RCF (0x8b10c) jumps to JOIN;
   - hs_seg_join: JOIN (0x8b12c) stores c->fn := 6 and c->nargs := 0 (two inline store checks), then calls
     arg_line(c, line); back at AL (0x8b168). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_canonical_c
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1 sup_host_setting_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the shadow band the inline checks read (s7 = 0x7fff8000) *)
Definition hs3_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
(* JOIN's seed: c (atom 8) a slot of g_rec's table or record.spill, s7 (atom 23) the shadow base; the 8 bytes c->fn,
   c->nargs written; the 56 bytes of the slot covered for the two inline store checks *)
Definition hs3_fJ : facts := mkFacts [(8%nat, mkAF (A_G_REC + 16) A_REC_SPILL 3); (23%nat, mkAF HS_SB HS_SB 0)] [] [].
Definition hs3_rJ : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
Definition hs3_SHJ : list shent := [mkSHE 8 0 56].
(* the entry's seed: atom 32 the shadow base, atom 33 g_rec.ncalls, A_OBJ 44 g_rec, A_OBJ 51 record.spill; the
   112-byte frame, the GOT word of the shadow base and the cell it names, and g_rec.ncalls *)
Definition hs3_fE : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF HS_SB HS_SB 0);
  (33%nat, mkAF 0 16 0); (A_OBJ 44, mkAF A_G_REC A_G_REC 3); (A_OBJ 51, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
Definition hs3_rsE : YP09.smem := [stack_region 112; got_regionP; bcell_regionP 32;
  YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
    [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))]].

Lemma hs3_wl_nonneg : forall toks, 0 <= hs_words_len toks.
Proof. intros toks. unfold hs_words_len. induction toks as [|w t IH]; cbn [fold_right]; lia. Qed.

Lemma hs3_bsum_nonneg : forall l, (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
intros l. unfold bsum. induction l as [|y l IH]; intros H; cbn [fold_right]; [lia|].
pose proof (H y (or_introl eq_refl)). pose proof (IH (fun pn Hp => H pn (or_intror Hp))). lia.
Qed.

(* two readers that hold the same value at a field agree on its bytes *)
Lemma hs3_aval_eq : forall (rd rd' : reader) a k v, aval_mem rd a k v -> aval_mem rd' a k v ->
forall y, a <= y < a + Z.of_nat k -> rd' y = rd y.
Proof.
intros rd rd' a k v H H' y Hy.
assert (Hi : Z.of_nat (Z.to_nat (y - a)) = y - a) by (apply Z2Nat.id; lia).
assert (Hik : (Z.to_nat (y - a) < k)%nat) by (apply Nat2Z.inj_lt; lia).
pose proof (H' _ Hik) as A1. pose proof (H _ Hik) as A2. rewrite Hi in A1, A2.
replace (a + (y - a)) with y in A1, A2 by lia. rewrite A1, A2. reflexivity.
Qed.

(* where record() puts the call: a slot of g_rec's table or record.spill *)
Lemma hs3_slot_form : forall R,
(exists i, 0 <= i < REC_CALLS_MAX /\ hs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ hs_slot R = A_REC_SPILL.
Proof.
intros R. unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; [left|right; reflexivity].
exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
Qed.

Lemma hs3_slot_rec : forall R a, hs_slot R <= a < hs_slot R + CALL_SIZE -> hs_in_rec a.
Proof.
intros R a Ha. destruct (hs_slot_bounds R) as (B1 & B2 & _ & [B4 | B4]); unfold hs_in_rec; [left | right];
unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, OFF_ANSWER, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma hs3_in_PG : forall a, hs_in_rec a -> Exists (in_zr a) recb_PG.
Proof.
intros a [Ha|Ha]; [apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd]; unfold in_zr; cbn [fst snd]; exact Ha.
Qed.

Lemma hs3_rec_FP : forall O a, hs_in_rec a -> inFP (hs_FP O) a.
Proof.
intros O a [Ha|Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
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

(* register r of an environment seeded from regs *)
Lemma hs3_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma hs3_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* a seed with every register its own atom and no region *)
Lemma hs3_seed_nil : forall (W : world SEGS) regs mem pc extra G,
facts_ok (Eimg (Ereg regs extra)) G ->
st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc sr_atoms [] None G)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc extra G HG. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
[apply regs_ok_Eimg_Ereg | reflexivity | apply Forall_nil | exact I | exact HG].
Qed.

(* a run that writes no region keeps every byte *)
Lemma hs3_view_nil : forall E (W : world SEGS) m m',
frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forall a, rdW W m' a = rdW W m a.
Proof. intros E W m m' Hf a. apply (aview_eq_of SEGS). apply Hf. intros (r & Hr & _). destruct Hr. Qed.

Lemma hs3_frame_ext : forall (rd rd' : reader) sp0 regs,
(forall a, rd' a = rd a) -> hs_frame rd sp0 regs -> hs_frame rd' sp0 regs.
Proof. intros rd rd' sp0 regs Hx H j r Hj k Hk. rewrite Hx. exact (H j r Hj k Hk). Qed.

(* a callee-saved register kept by a run or a call *)
Lemma hs3_pres_reg : forall regs1 regs2 (r : bv 5), aregs_preserved regs1 regs2 -> acallee_saved (bv_unsigned r) ->
getr regs2 r = getr regs1 r.
Proof. intros regs1 regs2 r Hp Hr. pose proof (Hp _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Local Ltac hs3_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end;
  lia.

Lemma hs3_regs0_pres : forall x regs1 regs2, hs_regs0 x regs1 -> aregs_preserved regs1 regs2 -> hs_regs0 x regs2.
Proof.
intros x regs1 regs2 (R2 & R3 & R4 & R8 & R9 & R22 & R23) Hp.
split; [rewrite (hs3_pres_reg regs1 regs2 2 Hp ltac:(hs3_cs)); exact R2|].
split; [rewrite (hs3_pres_reg regs1 regs2 3 Hp ltac:(hs3_cs)); exact R3|].
split; [rewrite (hs3_pres_reg regs1 regs2 4 Hp ltac:(hs3_cs)); exact R4|].
split; [rewrite (hs3_pres_reg regs1 regs2 8 Hp ltac:(hs3_cs)); exact R8|].
split; [rewrite (hs3_pres_reg regs1 regs2 9 Hp ltac:(hs3_cs)); exact R9|].
split; [rewrite (hs3_pres_reg regs1 regs2 22 Hp ltac:(hs3_cs)); exact R22|].
rewrite (hs3_pres_reg regs1 regs2 23 Hp ltac:(hs3_cs)); exact R23.
Qed.

Lemma hs3_regs0_eq : forall x regs1 regs2, hs_regs0 x regs1 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 22 = getr regs1 22 ->
getr regs2 23 = getr regs1 23 -> hs_regs0 x regs2.
Proof.
intros x regs1 regs2 (R2 & R3 & R4 & R8 & R9 & R22 & R23) E2 E3 E4 E8 E9 E22 E23.
split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|]. split; [rewrite E22; exact R22|].
rewrite E23; exact R23.
Qed.

(* the frame's 13 words lie in [sp0 - 104, sp0) *)
Lemma hs3_frame_kept : forall (rd rd' : reader) sp0 regs,
hs_frame rd sp0 regs -> (forall a, sp0 - 104 <= a < sp0 -> rd' a = rd a) -> hs_frame rd' sp0 regs.
Proof.
intros rd rd' sp0 regs H Hk j r Hj k Hk8.
assert (Hjl : (j < length HS_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length HS_SAVED) with 13%nat in Hjl.
rewrite Hk by lia. exact (H j r Hj k Hk8).
Qed.

(* s8 = the shadow byte's address of c + 4 *)
Lemma hs3_denot_shx : forall E (m : nat) v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 40 -> ew E 23%nat = Z_to_bv 64 HS_SB ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m 4) (SLit 3)) (SOff 23 0)) = Z_to_bv 64 (HS_SB + (v + 4) / 8).
Proof.
intros E m v Hm Hv H23. cbn [sv_denot]. rewrite Hm, H23.
rewrite !unsigned_lit_small by (unfold HS_SB; lia).
rewrite Z.add_0_r, !zalu64_sound.
f_equal. unfold zalu64. cbn [zalu_raw]. unfold zcanon, M64.
assert (Hq : 0 <= (v + 4) / 8 < 2 ^ 40) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small (v + 4)) by lia. rewrite (Z.mod_small 3) by lia. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite !(Z.mod_small ((v + 4) / 8)) by lia. rewrite (Z.mod_small HS_SB) by (unfold HS_SB; lia).
rewrite Z.mod_small by (unfold HS_SB; lia). lia.
Qed.

Lemma hs3_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma hs3_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* the frame after the prologue: the 13 saved registers of the stack region's chunks *)
Lemma hs3_frame_of_region : forall E (m : word -> option byte) H sp0 regs cs,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) ->
bv_unsigned (ew E 2%nat) = sp0 ->
(forall j r, nth_error HS_SAVED j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
(forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
hs_frame (aview SEGS H m) sp0 regs.
Proof.
intros E m H sp0 regs cs HR Hsp Hin HE j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold HS_SAVED in Hj. cbn [In] in Hj. lia. }
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
pose proof (field_of_region E _ 2 sp0 cs (-112) 0 (-112) 0 (-8 - 8 * Z.of_nat j) 8%N (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)) as V.
assert (V' : val_mem SEGS (mrestrict H m) (sp0 + (-8 - 8 * Z.of_nat j)) (N.to_nat 8) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ apply V; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].
  cbn [sv_denot]. rewrite (HE r Hr), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) in V' by lia.
exact (RecBLemmas.aval_mem_view SEGS _ _ _ _ _ V').
Qed.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls (the shifts and the subtraction folded to one product) *)
Lemma hs3_denot_slot : forall E n, ew E 33%nat = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E 285%nat = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n HN Hn HG. cbn [sv_denot].
assert (HG64 : 0 <= A_G_REC < 2 ^ 64) by (cbv [A_G_REC]; lia).
assert (HN64 : 0 <= n < 2 ^ 64) by lia.
rewrite HN, HG, (unsigned_lit_small n HN64), (unsigned_lit_small _ HG64).
rewrite !Z.add_0_r, zmd64_sound, !zalu64_sound.
f_equal.
cbv [zmd64 zalu64 zcanon M64 zmd_raw zalu_raw bv_swrap bv_half_modulus bv_modulus].
cbn [Z.of_N]. cbv [A_G_REC OFF_CALLS CALL_SIZE].
assert (H56 : 56 mod 2 ^ 64 = 56) by reflexivity.
assert (H16 : 16 mod 2 ^ 64 = 16) by reflexivity.
assert (HGR : 6174528 mod 2 ^ 64 = 6174528) by reflexivity.
assert (Hnm : n mod 2 ^ 64 = n) by (apply Z.mod_small; lia).
rewrite H56, H16, HGR, Hnm, !Zmod_mod.
rewrite (Z.mod_small (n * 56) (2 ^ 64)) by lia.
rewrite (Z.mod_small (n * 56 + 16) (2 ^ 64)) by lia.
rewrite (Z.mod_small (n * 56 + 16 + 6174528) (2 ^ 64)) by lia.
lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a byte of g_rec / record.spill: in the call's footprint, a program static, in the image, owned by no runtime *)
Lemma hs3_rec_prog : forall O a, hs_in_rec a ->
inFP (hs_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros O a Ha. split; [exact (hs3_rec_FP O a Ha)|]. rewrite (RecBLemmas.recb_ts_prog_m B (hh_HB _ _ HH)).
split; [exact (hs3_in_PG a Ha) | exact (hh_prog_img _ _ HH a (hs3_in_PG a Ha))].
Qed.

Lemma hs3_awr_rec : forall STK sp0 O bl0 blc fr0 ly own a, hs_in_rec a ->
awr_byte SEGS B STK sp0 (hs_FP O) bl0 blc fr0 ly own a.
Proof. intros STK sp0 O bl0 blc fr0 ly own a Ha. right; right; right; right; left. exact (hs3_rec_prog O a Ha). Qed.

Lemma hs3_rec_unowned : forall a, hs_in_rec a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. assert (HP : Exists (in_zr a) (as_prog_static B))
  by (rewrite (RecBLemmas.recb_ts_prog_m B (hh_HB _ _ HH)); exact (hs3_in_PG a Ha)).
destruct (prog_static_sep B a (ts_ok B (hh_HB _ _ HH)) HP) as (H1 & H2 & _). split; assumption.
Qed.

(* the slot's 56 bytes are addressable: g_rec and record.spill lie in zero-shadow ranges of the record *)
Lemma hs3_slot_addr : forall ly S (W : world SEGS) mem md R, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF (hs_slot R) CALL_SIZE.
Proof.
intros ly S W mem md R HAR. destruct (hs_slot_bounds R) as (B1 & B2 & _ & [B4 | B4]).
- apply (cmd_addressable_in SEGS B LAWS (hh_HB _ _ HH) ly S W mem md (0xada00, 0x5e3b00 - 0xada00));
  [exact HAR | unfold Tfib_zero_shadow; cbn; tauto | cbn; reflexivity | cbn; reflexivity | | ];
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; cbn [fst snd]; lia.
- rewrite B4. apply (cmd_addressable_in SEGS B LAWS (hh_HB _ _ HH) ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0));
  [exact HAR | unfold Tfib_zero_shadow; cbn; tauto | cbn; reflexivity | cbn; reflexivity | | ];
  unfold A_REC_SPILL, CALL_SIZE; cbn [fst snd]; lia.
Qed.

Lemma hs3_own_bounds : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> hs_in_rec a \/ hs_in_own O a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO [Ha | ([p n] & Hpn & Ha)].
- pose proof asan_consts as (C1 & _). unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
- cbn [fst snd] in Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & H4 & Hc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. lia.
Qed.

(* a read-only byte is no byte of the call's footprint *)
Lemma hs3_FP_ro : forall x a, hs_cx B MT x -> in_roP SEGS RLO RHI a -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x a HCX Hro (r & Hr & Ha).
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR & _).
destruct (hh_ro_prog_apart _ _ HH a Hro) as [Himg HnPG].
destruct Hr as [<- | [<- | Hr]].
- apply HnPG. apply hs3_in_PG. left. cbn [fst snd] in Ha. exact Ha.
- apply HnPG. apply hs3_in_PG. right. cbn [fst snd] in Ha. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Ha.
  destruct (hs_rec_own B _ _ _ _ _ HREP0 (p, n) Hpn) as (Hin & _).
  exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR Hin Ha Himg).
Qed.

(* the read-only data seen at any state the call's journal reaches *)
Lemma hs3_aro : forall x lyc Sc Wc memc mdc k, hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros x lyc Sc Wc memc mdc k HCX HJ. pose proof HCX as (_ & HROD & _).
pose proof (hh_RRO _ _ HH) as RRO.
apply (arodata_ok_journalP SEGS RLO RHI (hh_RELRO_IMG _ _ HH) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
- intros a Hro. exact (hs3_FP_ro x a HCX Hro).
- exact HROD.
Qed.

(* an input string of the entry, seen at any state the call's journal reaches *)
Lemma hs3_str_kept : forall x lyc Sc Wc memc mdc k O1 Nw Rest p s,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k ->
hs_ba B x lyc Sc O1 Nw Rest ->
hs_str B (i_ly x) (i_S x) (rdW (i_W x) (i_mem x)) (i_O x) p s ->
hs_str B lyc Sc (rdW Wc memc) [] p s.
Proof.
intros x lyc Sc Wc memc mdc k O1 Nw Rest p s HCX HJ HBA HSTR.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR & _).
pose proof HBA as (HPm & _ & HRest & _).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
cbv zeta in HSTR. destruct HSTR as (Hnz & Hstr & Hlen & Hblk & Hap).
destruct Hblk as (q & k0 & Hq & Hq1 & Hq2).
assert (HqO : ~ In (q, k0) (i_O x)).
{ intros HqO. rewrite Forall_forall in Hap. specialize (Hap _ HqO). unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hqc : In (q, k0) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. exact (HRest _ Hq HqO). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ q k0 HAR Hq) as (_ & _ & _ & _ & _ & _ & Hk0).
pose proof (req_size_pos k0 ltac:(lia)) as [_ Hreq].
split; [exact Hnz|]. split.
{ apply (hs_str_kept (rdW (i_W x) (i_mem x))); [exact Hstr|]. intros y Hy.
  replace y with (q + (y - q)) by lia. apply (J2 q k0 (y - q)); [exact Hq | exact Hqc | lia |].
  replace (q + (y - q)) with y by lia. intros (r & Hr & Ha).
  destruct Hr as [<- | [<- | Hr]].
  + cbn [fst snd] in Ha. apply (blk_img SEGS B LAWS _ _ _ _ _ q k0 y HAR Hq ltac:(lia)).
    apply (hh_prog_img _ _ HH). apply hs3_in_PG. left. exact Ha.
  + cbn [fst snd] in Ha. apply (blk_img SEGS B LAWS _ _ _ _ _ q k0 y HAR Hq ltac:(lia)).
    apply (hh_prog_img _ _ HH). apply hs3_in_PG. right. exact Ha.
  + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm). cbn [fst snd] in Ha.
    destruct (RecBLemmas.recb_pair_dec (b, m) (q, k0)) as [Heq | Hne]; [rewrite Heq in Hbm; exact (HqO Hbm)|].
    destruct (hs_rec_own B _ _ _ _ _ HREP0 (b, m) Hbm) as (Hbin & _).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b m q k0 HAR Hbin Hq Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [exact Hlen|]. split; [exact (ex_intro _ q (ex_intro _ k0 (conj Hqc (conj Hq1 Hq2)))) | constructor].
Qed.

(* a fresh block joins Nw *)
Lemma hs3_ba_new : forall x lyc Sc ly2 S2 O1 Nw Rest b,
hs_ba B x lyc Sc O1 Nw Rest -> Permutation (ablocks B ly2 S2) (b :: ablocks B lyc Sc) -> ~ In b (ablocks B lyc Sc) ->
hs_ba B x ly2 S2 O1 (Nw ++ [b]) Rest.
Proof.
intros x lyc Sc ly2 S2 O1 Nw Rest b (H1 & H2 & H3 & H4 & H5 & H6 & H7) HP Hn.
split; [|split; [exact H2|split; [exact H3|split; [exact H4|split; [exact H5|split; [|exact H7]]]]]].
- eapply perm_trans; [exact HP|]. rewrite <- app_assoc. cbn [app].
  exact (perm_trans (perm_skip b H1) (Permutation_middle Nw Rest b)).
- intros pn Hpn Hin. apply in_app_or in Hpn as [Hpn | [<- | []]]; [exact (H6 pn Hpn Hin)|].
  destruct (in_dec RecBLemmas.recb_pair_dec b (i_O x)) as [Ho | Ho]; [exact Ho|]. exfalso. apply Hn.
  apply (Permutation_in _ (Permutation_sym H1)). apply in_or_app. right. exact (H3 b Hin Ho).
Qed.

(* a callee keeps the recorder's bytes outside its footprint *)
Lemma hs3_call_keeps : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 EV1 O1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
~ YI16.sink_open_fp FP1 ->
(forall pn, In pn O1 -> In pn (ablocks B lyc Sc) /\ In pn (ablocks B ly2 S2)) ->
hs_in_rec a \/ hs_in_own O1 a -> ~ inFP FP1 a ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 EV1 O1 a HJ Hsk HO Ha HnF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & J3 & _).
destruct Ha as [Ha | ([b m] & Hbm & Ha)].
- destruct (hs3_rec_unowned a Ha) as [Ho He].
  apply J3; [exact (hh_prog_img _ _ HH a (hs3_in_PG a Ha)) | exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk HnF)].
- cbn [fst snd] in Ha. destruct (HO _ Hbm) as [H1 H2].
  replace a with (b + (a - b)) by lia. apply (J2 b m (a - b)); [exact H1 | exact H2 | unfold req_size; destruct (Z.eqb_spec m 0); lia |].
  replace (b + (a - b)) with a by lia. exact HnF.
Qed.

(* the meter amounts are nonnegative *)
Lemma hs3_xm_nonneg : forall x, 0 <= hs_m0 MT x /\ 0 <= XM_ARG_LINE MT (i_line x) /\
0 <= XM_ARG_I MT (Z.of_nat (length (i_toks x))) /\ 0 <= mo_malloc MT (hs_words_len (i_toks x) + 1) /\
0 <= XM_XSTRDUP MT (join_sp (i_toks x)) /\ 0 <= mo_free MT.
Proof.
intros x. pose proof (hh_MTL _ _ HH) as ML. pose proof (mo_free_nonneg MT ML) as F.
pose proof (hs3_wl_nonneg (i_toks x)) as Hw.
unfold hs_m0, rec_spill_frees, XM_ARG_LINE, XM_REC_CANONICAL, XM_ARG_I, XM_XSTRDUP.
split; [destruct (Nat.ltb _ _); nia|].
split; [apply (mo_malloc_nonneg MT ML); lia|]. split; [apply (mo_malloc_nonneg MT ML); lia|].
split; [apply (mo_malloc_nonneg MT ML); lia|]. split; [apply (mo_malloc_nonneg MT ML); lia|]. exact F.
Qed.

Lemma hs3_repJ_ext : forall ly S (rd rd2 : reader) R O,
rec_repJ B ly S rd R O -> (forall a, rd2 a = rd a) -> rec_repJ B ly S rd2 R O.
Proof. intros ly S rd rd2 R O H Hx rd' Hk H1 H2. apply H; [intros a Ha Hs; rewrite (Hk a Ha Hs); apply Hx | exact H1 | exact H2]. Qed.

(* RCF 0x8b10c: `j 0x8b12c` *)
Lemma hs_seg_rcf : forall x, ST_JOIN B MT x -> ST_RCF B MT x.
Proof.
intros x HJOIN lyc Sc Wc memc mdc regs1 k O1 Rest H16 HCX HMID HREP HR0 H18 H20.
pose proof HMID as (HJ & Hk & HMO & HBB & HFR & HBA).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
destruct (hs_rec_ncalls B _ _ _ _ _ HREP0) as [Hle16 _].
assert (HL16 : length (r_calls (i_R x)) = 16%nat) by lia.
pose proof (hs3_seed_nil Wc regs1 memc HS_RCF [] (mkFacts [] [] []) (conj I (conj I I))) as HS.
set (E := Eimg (Ereg regs1 [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 23 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
unfold hs_atF.
paj_run_to_tok RUNTO HS HJ SHOK hs3_Bspan HS_JOIN.
{ awr_ok_tac. }
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs1 [] HS (hs3_agree regs1 []) ltac:(vm_compute; reflexivity)) as HP.
cbn [ms_regs restrict] in HP.
pmkst HS.
pose proof (hs3_view_nil E Wc memc _ HFr) as HV.
refine (HJOIN lyc Sc Wc (ms_mem ms) _ (ms_regs ms) k O1 Rest HCX _ _ _ _ _).
- exact (conj HJ (conj Hk (conj HMO (conj HBB (conj (hs3_frame_ext _ _ _ _ HV HFR) HBA))))).
- apply (hs3_repJ_ext lyc Sc (rdW Wc memc)); [|exact HV].
  exact (hs_rec_join_spill B lyc Sc (rdW Wc memc) (i_R x) O1 HREP HL16).
- exact (hs3_regs0_pres x regs1 _ HR0 HP).
- rewrite (hs3_pres_reg regs1 _ 18 HP ltac:(hs3_cs)). exact H18.
- rewrite (hs3_pres_reg regs1 _ 20 HP ltac:(hs3_cs)). exact H20.
Qed.

Local Ltac hs3_in := repeat (first [left; reflexivity | right]).

(* JOIN 0x8b12c .. 0x8b164: the inline checks of c->fn and c->nargs, c->fn := 6, c->nargs := 0, the call of
   arg_line(c, line); back at AL 0x8b168 *)
Lemma hs_seg_join : forall x, ST_AL B MT x -> ST_JOIN B MT x.
Proof.
intros x HAL lyc Sc Wc memc mdc regs1 k O1 Rest HCX HMID HREPJ HR0 H18 H20.
pose proof HMID as (HJ & Hk & HMO & HBB & HFR & HBA).
pose proof HR0 as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
pose proof HCX as (HPRE & HROD & _ & _ & HPLB & _ & _ & _ & HNT & HLINE & _ & _ & _ & _ & _ & _ & _ & HREP0 & _ &
  HEV & HLIVE & HMOK & _).
pose proof HPRE as (HAR & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hsp16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HARc.
pose proof (hh_MTL _ _ HH) as ML.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_HOST_SETTING_STK = 16640) by reflexivity.
assert (WAL : ARG_LINE_STK = 16464) by reflexivity.
set (c := hs_slot (i_R x)) in *.
pose proof (hs_slot_bounds (i_R x)) as (Hc1 & Hc2 & Hc8 & _). fold c in Hc1, Hc2, Hc8.
assert (Hcr : forall a, c <= a < c + CALL_SIZE -> hs_in_rec a) by (intros a Ha; exact (hs3_slot_rec (i_R x) a Ha)).
assert (Hc64 : 0 <= c < 2 ^ 40) by (unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia).
set (sp0 := spZ (i_regs x)) in *.
assert (Hsp : alloc_ceiling + 112 <= sp0 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (E2 : ew (Eimg (Ereg regs1 [])) 2 = Z_to_bv 64 (sp0 - 112)) by exact (eq_trans (hs3_E_reg regs1 [] 2 2 eq_refl) R2).
assert (E3 : ew (Eimg (Ereg regs1 [])) 3 = getr regs1 3) by exact (hs3_E_reg regs1 [] 3 3 eq_refl).
assert (E4 : ew (Eimg (Ereg regs1 [])) 4 = getr regs1 4) by exact (hs3_E_reg regs1 [] 4 4 eq_refl).
assert (E8 : ew (Eimg (Ereg regs1 [])) 8 = Z_to_bv 64 c) by exact (eq_trans (hs3_E_reg regs1 [] 8 8 eq_refl) R8).
assert (E20 : ew (Eimg (Ereg regs1 [])) 20 = Z_to_bv 64 (i_pl x)) by exact (eq_trans (hs3_E_reg regs1 [] 20 20 eq_refl) H20).
assert (E23 : ew (Eimg (Ereg regs1 [])) 23 = Z_to_bv 64 HS_SB) by exact (eq_trans (hs3_E_reg regs1 [] 23 23 eq_refl) R23).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
(* the seed *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (mkSS HS_JOIN sr_atoms [hs3_rJ] None hs3_fJ)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_JOIN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor; [|constructor]. unfold hs3_rJ, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (hh_prog_writable _ _ HH lyc Sc Wc memc mdc); [exact HARc|].
    apply hs3_in_PG. apply Hcr. unfold CALL_SIZE. lia.
  - exact (conj I I).
  - unfold hs3_fJ. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [apply (hs3_afact _ 8 c); [exact E8 | lia | unfold OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia
      | change (2 ^ 3) with 8; exact Hc8 | lia]|].
    split; [apply (hs3_afact _ 23 HS_SB); [exact E23 | unfold HS_SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I. }
assert (SHOK : sh_ok SEGS (SOff 23 0) hs3_SHJ (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, hs3_SHJ. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc _ (SOff 23 0) 8 c CALL_SIZE c 0 CALL_SIZE).
  - exact (hs3_slot_addr lyc Sc Wc memc mdc (i_R x) HARc).
  - rewrite (hs3_U_atom _ 23 HS_SB E23 ltac:(unfold HS_SB; lia)). reflexivity.
  - exact (hs3_U_atom _ 8 c E8 ltac:(lia)).
  - lia.
  - lia.
  - intros y Hy. change (Z.min 0 CALL_SIZE) with 0 in Hy. change (Z.max 0 CALL_SIZE) with 56 in Hy.
    clear - Hy Hc2. unfold SHADOW_OFF, CALL_SIZE, A_REC_SPILL, SC_SIZE in *. lia. }
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
unfold hs_atF.
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 8%nat).
  - reflexivity.
  - rewrite E8. apply unsigned_lit_small. lia.
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply hs3_awr_rec. apply Hcr. unfold CALL_SIZE. lia.
  - apply awr_ok_nil. }
lazymatch goal with |- context [with_vm_backing ?l ?m ?d] => set (mdv1 := with_vm_backing l m d) in *; clearbody mdv1 end.
assert (SIGAL : SIG CS_arg_line = BASE + AF_arg_line).
{ rewrite (hh_sigp _ _ HH CS_arg_line ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))).
  reflexivity. }
pmkst HS. rewrite SIGAL.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (19%bv : bv 5) P19.
pose proof (st_ok_restrict_reg SEGS (w_H Wc) E _ ms (24%bv : bv 5) HS) as P24.
lazymatch type of P24 with context [sr_get (ss_regs ?ss) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P24 end.
cbn [ms_regs restrict] in P24.
rewrite (hs3_denot_shx E 8 c E8 Hc64 E23) in P24.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 [] [2; 3; 4; 8; 9; 18; 20; 22; 23]%bv HS
  ltac:(rewrite HE; apply hs3_agree) ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (Qsp : spZ (ms_regs ms) = sp0 + -112) by (unfold spZ at 1; rewrite P2, E2, unsigned_lit_small by lia; lia).
(* the two stores, and every other byte kept *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
assert (V4 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (c + 4) 4 0).
{ exact (field_of_region E _ 8 c _ 0 8 0 8 4 4%N (SLit 0) 0 HRG ltac:(rewrite E8; apply unsigned_lit_small; lia)
    ltac:(cbn [In]; hs3_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (V0 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (c + 0) 4 6).
{ exact (field_of_region E _ 8 c _ 0 8 0 8 0 4%N (SLit 6) 6 HRG ltac:(rewrite E8; apply unsigned_lit_small; lia)
    ltac:(cbn [In]; hs3_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (RecBLemmas.recb_run_keeps_m E [hs3_rJ] (w_H Wc) memc (ms_mem ms) a HFr Ha).
  intros (r & Hr & Hra). destruct Hr as [<- | []].
  cbn [hs3_rJ YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite E8, unsigned_lit_small in Hra by lia. lia. }
(* arg_line's premises *)
pose proof (hs3_aro x lyc Sc Wc (ms_mem ms) _ k HCX HJ) as HROD1.
pose proof (hs3_str_kept x lyc Sc Wc (ms_mem ms) _ k O1 [] Rest (i_pl x) (i_line x) HCX HJ HBA HLINE) as HSTR1.
pose proof HSTR1 as (_ & Hstr1 & Hlen1 & Hblk1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (hs3_xm_nonneg x) as (M0 & M1 & M2 & M3 & M4 & M5).
pose proof (hs3_wl_nonneg (i_toks x)) as Hwl0.
assert (HEV1 : st_nev Sc + EV_ARG_LINE <= EV_MAX)
  by (clear - Hnev Hk HEV; unfold EV_SUP_HOST_SETTING, hs_k0, EV_ARG_LINE, EV_ARG_I, EV_XSTRDUP, EV_REC_CANONICAL in *; lia).
assert (HLIVE1 : blocks_bytes Sc + LIVE_ARG_LINE (i_line x) <= LIVE_MAX)
  by (clear - HBB HLIVE Hwl0; unfold LIVE_SUP_HOST_SETTING, LIVE_ARG_I, LIVE_XSTRDUP in *; cbn [bsum fold_right] in HBB; lia).
assert (HMOK1 : mo_ok MT Sc (XM_ARG_LINE MT (i_line x))).
{ apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m0 MT x) _ ML HMOK HMO M1).
  clear - M1 M2 M3 M4 M5. unfold XM_SUP_HOST_SETTING, hs_m0. lia. }
(* the call of arg_line *)
eapply SRr_bind.
{ eapply (hh_CL _ _ HH fx Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_line)) SUP_HOST_SETTING_STK sp0
    (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc _ k ARG_LINE_STK
    [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]
    EV_ARG_LINE (-112) (getr (ms_regs ms) 1) [] _ HJ Qsp).
  - reflexivity.
  - lia.
  - rewrite WAL; lia.
  - rewrite WAL, WS; lia.
  - rewrite P3, E3, R3. exact Hgp.
  - rewrite P4, E4, R4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, E8, unsigned_lit_small by lia. lia.
  - intros HPRE1.
    exact (hh_arg_line _ _ HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ [] c (i_pl x) 0 (i_line x) HPRE1 HROD1
      (eq_trans P10 E8) (eq_trans P11 E20) (proj1 HPLB) (hs3_slot_form (i_R x))
      (RecBLemmas.aval_mem_view SEGS _ _ _ _ _ V4)
      ltac:(unfold REC_ARGS_MAX; lia) Hblk1 Hstr1 Hlen1 HEV1 HLIVE1 HMOK1).
  - intros a (r & Hr & Ha). right; right. apply hs3_rec_prog. apply Hcr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; cbv [CALL_OFF_NARGS CALL_OFF_ARGS CALL_SIZE] in Ha |- *; lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK2).
destruct HK2 as (_ & HML & [(H06 & _) | (_ & p & Hp4096 & Hperm & Hapart & Hnarg & Harg & Hcan)]);
  [unfold REC_ARGS_MAX in H06; lia|].
rewrite P1.
pose proof (proj1 HJ2) as HAR2.
pose proof HLINE as (_ & _ & Hlen & _).
pose proof (canon_length (i_line x)) as Hcl.
assert (Hpin : In (p, Z.of_nat (length (i_line x)) + 1) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hpnot : ~ In (p, Z.of_nat (length (i_line x)) + 1) (ablocks B lyc Sc)).
{ intros Hin. rewrite Forall_forall in Hapart. pose proof (Hapart _ Hin) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. pose proof HBA as (HPm & _ & _ & _ & _ & _ & HO1R).
  apply (Permutation_in _ (Permutation_sym HPm)). exact (HO1R pn Hpn). }
assert (HO12 : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact (HO1c pn Hpn). }
(* the recorder after the two stores, then with the line *)
assert (HREPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (rec_record (i_R x) REC_HOST_SETTING []) O1).
{ apply HREPJ.
  - intros a Ha Hs. apply KR; [|exact Hs]. pose proof (hs3_own_bounds lyc Sc Wc memc mdc O1 a HARc HO1c Ha). lia.
  - pose proof (RecBLemmas.aval_mem_view SEGS _ _ _ _ _ V0) as A0. rewrite Z.add_0_r in A0. exact A0.
  - exact (RecBLemmas.aval_mem_view SEGS _ _ _ _ _ V4). }
assert (HREP2 : rec_repA B ly2 S2 (rdW W2 mem2) (rec_record (i_R x) REC_HOST_SETTING ([] ++ [canon (i_line x)]))
  (O1 ++ [(p, Z.of_nat (length (i_line x)) + 1)])).
{ apply (hs_rec_arg B lyc Sc ly2 S2 (rdW Wc (ms_mem ms)) (rdW W2 mem2) (i_R x) [] O1 p
    (Z.of_nat (length (i_line x)) + 1) (canon (i_line x)) HREPc).
  - cbn; lia.
  - exact Hnarg.
  - exact Harg.
  - intros a Ha Hn1 Hn2.
    apply (hs3_call_keeps ARG_LINE_STK (sp0 + -112) _ lyc Sc Wc (ms_mem ms) _ ly2 S2 W2 mem2 md2 EV_ARG_LINE O1 a HJ2c).
    + apply sink_closed_pos. repeat constructor; cbn [fst]; cbv [CALL_OFF_NARGS CALL_OFF_ARGS]; lia.
    + intros pn Hpn. split; [exact (HO1c pn Hpn) | exact (HO12 pn Hpn)].
    + exact Ha.
    + intros (r & Hr & Hra). cbn [length Z.of_nat] in Hn2.
      destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; [apply Hn1 | apply Hn2]; lia.
  - lia.
  - exact Hcan.
  - lia.
  - lia.
  - exact Hpin.
  - exact HO12.
  - rewrite Forall_forall in Hapart |- *. intros qk Hqk. exact (Hapart qk (HO1c qk Hqk)).
  - apply (RecBLemmas.recb_heap_apart_m B ly2 S2 W2 mem2 md2 p _ A_G_REC REC_SIZE HAR2 Hpin); [lia | unfold REC_SIZE; lia|].
    intros a Ha. apply (hh_prog_img _ _ HH). apply hs3_in_PG. left. exact Ha.
  - apply (RecBLemmas.recb_heap_apart_m B ly2 S2 W2 mem2 md2 p _ A_REC_SPILL SC_SIZE HAR2 Hpin); [lia | unfold SC_SIZE; lia|].
    intros a Ha. apply (hh_prog_img _ _ HH). apply hs3_in_PG. right. exact Ha. }
(* AL *)
refine (HAL ly2 S2 W2 mem2 md2 regs2 (k + EV_ARG_LINE) O1 Rest (p, Z.of_nat (length (i_line x)) + 1) HCX _ _ HREP2 _ _).
- split; [exact HJ2|]. split; [unfold EV_ARG_LINE, EV_REC_CANONICAL in *; lia|].
  split; [exact (mle_station MT _ _ _ _ _ ML HMO HML)|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hperm), bsum_cons. rewrite (blocks_bytes_bsum B lyc Sc) in HBB.
    cbn [bsum fold_right snd] in HBB |- *. lia. }
  split.
  { apply (hs3_frame_kept (rdW Wc memc)); [exact HFR|]. intros a Ha.
    pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
    rewrite (K1 a); [apply KR; lia | lia | rewrite WAL; lia |].
    intros (r & Hr & Hra). destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; cbv [CALL_OFF_NARGS CALL_OFF_ARGS] in Hra; lia. }
  exact (hs3_ba_new x lyc Sc ly2 S2 O1 [] Rest _ HBA Hperm Hpnot).
- unfold LIVE_ARG_LINE, LIVE_REC_CANONICAL. reflexivity.
- split.
  + apply (hs3_regs0_pres x (ms_regs ms) regs2); [|exact HP2].
    apply (hs3_regs0_eq x regs1 (ms_regs ms) HR0); apply HKR; hs3_in.
  + split.
    * rewrite (hs3_pres_reg _ regs2 19 HP2 ltac:(hs3_cs)), P19, E8, unsigned_lit_small by lia. reflexivity.
    * rewrite (hs3_pres_reg _ regs2 24 HP2 ltac:(hs3_cs)), P24. reflexivity.
- rewrite (hs3_pres_reg _ regs2 18 HP2 ltac:(hs3_cs)), (HKR (18%bv : bv 5) ltac:(hs3_in)). exact H18.
Qed.

(* the entry 0x8b094: the prologue, the shadow base through the GOT (0x8b0d4), g_rec.ncalls, and record()'s branch
   (0x8b0f4): the table arm stores g_rec.ncalls := n + 1 and reaches JOIN with c = g_rec.calls[n]; the spill arm calls
   rec_calls_free(&record.spill, 1) and comes back at RCF *)
Lemma hs_seg_entry : forall x, hs_cx B MT x -> ST_JOIN B MT x -> ST_RCF B MT x ->
SRr SEGS (i_W x) (cfg_at SEGS (BASE + AF_sup_host_setting) (i_regs x) (i_mem x) (i_md x)) (hs_postF B MT x).
Proof.
intros x HCX HJOIN HRCF.
pose proof HCX as (HPRE & HROD & _ & _ & _ & H10 & H11 & H12 & HNT & HLINE & _ & _ & _ & _ & _ & _ & _ & HREP0 & _ &
  HEV & HLIVE & HMOK & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof (hh_MTL _ _ HH) as ML.
pose proof (hh_TL _ _ HH) as TL.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (hh_vobjs _ _ HH) as VOBJS.
assert (WS : SUP_HOST_SETTING_STK = 16640) by reflexivity.
set (sp0 := spZ (i_regs x)) in *.
assert (Hsp : alloc_ceiling + 16640 <= sp0 <= 2 ^ 47) by (rewrite WS in Hslo; lia).
assert (Hsp46 : 2 ^ 46 <= sp0 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328 in *. lia. }
destruct (hs_rec_ncalls B _ _ _ _ _ HREP0) as [Hle16 HNC].
set (n := Z.of_nat (length (r_calls (i_R x)))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
pose proof (ajournal_init SEGS B SUP_HOST_SETTING_STK (hs_FP (i_O x)) _ _ _ _ _ _ _ HPRE) as HJ.
assert (EV44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV51 : VAL (A_OBJ 51) = A_REC_SPILL) by (rewrite (VOBJS 51%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
(* the environment: the entry's registers, the shadow base (32) and the call count (33) *)
set (E := Eimg (Ereg (i_regs x) [Z_to_bv 64 HS_SB; Z_to_bv 64 n])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (i_regs x) [Z_to_bv 64 HS_SB; Z_to_bv 64 n]) E) by (unfold E; apply hs3_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr (i_regs x) r)
  by (intros k r Hk; unfold E; exact (hs3_E_reg _ _ k r Hk)).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (rewrite (EE 2%nat 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (E32 : ew E 32 = Z_to_bv 64 HS_SB)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (i_regs x) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (i_regs x) _ 1)).
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), EV44; reflexivity).
assert (ESP : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL)
  by (rewrite (img_env_atomP E (A_OBJ 51) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), EV51; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
(* the seed *)
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_sup_host_setting sr_atoms hs3_rsE None hs3_fE)
  (restrict (w_H (i_W x)) (mkst (i_regs x) (Z_to_bv 64 (BASE + AF_sup_host_setting)) (i_mem x) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
    rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
    unfold hs3_rsE, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 2%nat sp0 E2) by lia. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia. }
      constructor.
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); cbv [SHADOW_OFF]; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    + rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
      split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
      split.
      { intros o Ho. apply (hh_prog_writable _ _ HH (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)); [exact HAR|].
        apply hs3_in_PG. left. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
      exact (RecBLemmas.val_mem_view SEGS _ _ _ _ _ HNC).
  - apply pairwise_disjoint_of_extents.
    unfold hs3_rsE, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    rewrite (VB 2%nat sp0 E2) by lia.
    rewrite EV0, EV12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, OFF_NCALLS in *. repeat split; lia.
  - unfold hs3_fE. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [apply (hs3_afact E 2 sp0); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia]|].
    split; [apply (hs3_afact E 32 HS_SB); [exact E32 | unfold HS_SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (hs3_afact E 33 n); [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (hs3_afact E (A_OBJ 44) A_G_REC); [exact EG | unfold A_G_REC; lia | lia
      | change (2 ^ 3) with 8; reflexivity | lia]|].
    split; [apply (hs3_afact E (A_OBJ 51) A_REC_SPILL); [exact ESP | unfold A_REC_SPILL; lia | lia
      | change (2 ^ 3) with 8; reflexivity | lia]|].
    exact I. }
(* the bytes a run of this segment does not write: off the frame and off g_rec.ncalls *)
assert (NW : forall rs a, windows rs = windows hs3_rsE -> 0 <= a < alloc_ceiling ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ in_wrange E rs a).
{ intros rs a Hw Ha Hn' Hin. apply in_wrange_windows in Hin as (b & wlo & whi & Hb & Hr). rewrite Hw in Hb.
  unfold hs3_rsE, stack_region, got_regionP, bcell_regionP, windows in Hb.
  cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hb.
  destruct Hb as [Hb | [Hb | [Hb | [Hb | []]]]]; injection Hb as <- <- <-.
  - rewrite (VB 2%nat sp0 E2) in Hr by lia. lia.
  - lia.
  - lia.
  - rewrite (VB (A_OBJ 44) A_G_REC EG) in Hr by (unfold A_G_REC; lia). unfold OFF_NCALLS in *. lia. }
assert (HOin : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
pose proof (hs3_xm_nonneg x) as (M0 & M1 & M2 & M3 & M4 & M5).
assert (HBA0 : hs_ba B x (i_ly x) (i_S x) (i_O x) [] (ablocks B (i_ly x) (i_S x))).
{ split; [apply Permutation_refl|]. split; [intros pn Hpn; exact Hpn|]. split; [intros pn Hpn _; exact Hpn|].
  split; [intros pn _ Hpn; exact Hpn|]. split; [intros pn Hpn; exact Hpn|]. split; [intros pn []|]. exact HOin. }
assert (EER : forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr (i_regs x) (Z_to_bv 5 r)).
{ intros r Hr. apply EE. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H (i_W x)) (i_mem x))) by (unfold sh_ok; apply Forall_nil).
clearbody E.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat).
  - reflexivity.
  - rewrite E2. apply unsigned_lit_small. lia.
  - cbn [YP09.r_wlo]. rewrite WS. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := A_OBJ 44).
    + reflexivity.
    + rewrite EG. apply unsigned_lit_small. unfold A_G_REC; lia.
    + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply hs3_awr_rec. left. unfold OFF_NCALLS, A_G_REC, REC_SIZE in *. lia.
    + apply awr_ok_nil. }
lazymatch goal with |- context [with_vm_backing ?l ?m ?d] => set (mdv1 := with_vm_backing l m d) in *; clearbody mdv1 end.
psrr_branch_tok RUN BR HS SHOK hs3_Bspan.
- (* the table has room: 0x8b110 .. JOIN *)
  assert (Hne : n <> 16).
  { intros E16. rewrite branch_ne_U in Hc. rewrite (hs3_U_atom E 33 n E33 ltac:(lia)), E16 in Hc.
    vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK hs3_Bspan HS_JOIN.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack with (n := 2%nat).
    - reflexivity.
    - rewrite E2. apply unsigned_lit_small. lia.
    - cbn [YP09.r_wlo]. rewrite WS. lia.
    - cbn [YP09.r_whi]. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply awr_ok_cons_gen with (n := A_OBJ 44).
      + reflexivity.
      + rewrite EG. apply unsigned_lit_small. unfold A_G_REC; lia.
      + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply hs3_awr_rec. left. unfold OFF_NCALLS, A_G_REC, REC_SIZE in *. lia.
      + apply awr_ok_nil. }
  lazymatch goal with |- context [with_vm_backing ?l ?m ?d] => set (mdv2 := with_vm_backing l m d) in *; clearbody mdv2 end.
  rename ms0 into ms2, HFr0 into HFr2.
  assert (Hlt : (length (r_calls (i_R x)) < 16)%nat) by (unfold n in Hne; lia).
  assert (Hslot : hs_slot (i_R x) = A_G_REC + OFF_CALLS + CALL_SIZE * n).
  { unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls (i_R x))) 16); [reflexivity | lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  pose proof (st_ok_pi_restrict_reg (w_H (i_W x)) E _ _ (8%bv : bv 5) HS) as P8.
  lazymatch type of P8 with context [sr_get (ss_regs ?ss) ?r] =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P8 end.
  rewrite (hs3_denot_slot E n E33 Hn EG) in P8.
  assert (HR0j : hs_regs0 x (ms_regs ms2)).
  { split; [rewrite P2, E2, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [rewrite P3; exact (EE 3%nat 3%bv eq_refl)|].
    split; [rewrite P4; exact (EE 4%nat 4%bv eq_refl)|].
    split; [rewrite P8, Hslot; reflexivity|].
    split; [rewrite P9, (EE 12%nat 12%bv eq_refl); exact H12|].
    split; [rewrite P22; exact EG|].
    rewrite P23; exact E32. }
  pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRG0. cbn [ms_mem restrict] in HRG0.
  pose proof (st_ok_region_nth E _ _ 3 _ HS eq_refl) as HRG3. cbn [ms_mem restrict] in HRG3.
  assert (HFRj : hs_frame (rdW (i_W x) (ms_mem ms2)) sp0 (i_regs x)).
  { apply (hs3_frame_of_region E (ms_mem ms2) (w_H (i_W x)) sp0 (i_regs x) _ HRG0).
    - rewrite E2. apply unsigned_lit_small. lia.
    - intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; hs3_in|]).
      destruct j; cbn in Hj; discriminate Hj.
    - exact EER. }
  assert (HNC2 : aval_mem (rdW (i_W x) (ms_mem ms2)) (A_G_REC + OFF_NCALLS) 4 (n + 1)).
  { apply (RecBLemmas.aval_mem_view SEGS).
    exact (field_of_region E _ (A_OBJ 44) A_G_REC _ 8 12 8 12 8 4%N (SOff 33 1) (n + 1) HRG3
      ltac:(rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia) ltac:(cbn [In]; hs3_in)
      ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (KJ : forall a, hs_in_rec a \/ hs_in_own (i_O x) a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
    rdW (i_W x) (ms_mem ms2) a = rdW (i_W x) (i_mem x) a).
  { intros a Ha Hn'. pose proof (hs3_own_bounds _ _ _ _ _ (i_O x) a HAR HOin Ha) as Hab.
    rewrite (RecBLemmas.recb_run_keeps_m E _ _ _ _ a HFr2); [| lia | apply NW; [reflexivity | exact Hab | exact Hn']];
    apply (RecBLemmas.recb_run_keeps_m E _ _ _ _ a HFr); [lia | apply NW; [reflexivity | exact Hab | exact Hn']]. }
  refine (HJOIN (i_ly x) (i_S x) (i_W x) (ms_mem ms2) mdv2 (ms_regs ms2) 0 (i_O x) (ablocks B (i_ly x) (i_S x))
    HCX _ _ HR0j _ _).
  + split; [exact HJ|]. split; [unfold hs_k0, rec_spill_frees; destruct (Nat.ltb _ _); lia|].
    split; [exact (mle_weaken MT _ _ 0 _ ML (mle_start MT _ ML) M0)|].
    split; [change (bsum []) with 0; lia|]. split; [exact HFRj | exact HBA0].
  + exact (hs_rec_join_slot B (i_ly x) (i_S x) (rdW (i_W x) (i_mem x)) (rdW (i_W x) (ms_mem ms2)) (i_R x) (i_O x)
      HREP0 Hlt HNC2 KJ).
  + rewrite P18, (EE 11%nat 11%bv eq_refl). exact H11.
  + rewrite P20, (EE 10%nat 10%bv eq_refl). exact H10.
- (* the table is full: 0x8b0f8 .. the call of rec_calls_free *)
  assert (H16 : n = 16).
  { rewrite branch_ne_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
    rewrite (hs3_U_atom E 33 n E33 ltac:(lia)) in Hc. rewrite Hc. reflexivity. }
  paj_run_tok RUN HS HJ SHOK hs3_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack with (n := 2%nat).
    - reflexivity.
    - rewrite E2. apply unsigned_lit_small. lia.
    - cbn [YP09.r_wlo]. rewrite WS. lia.
    - cbn [YP09.r_whi]. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply awr_ok_cons_gen with (n := A_OBJ 44).
      + reflexivity.
      + rewrite EG. apply unsigned_lit_small. unfold A_G_REC; lia.
      + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply hs3_awr_rec. left. unfold OFF_NCALLS, A_G_REC, REC_SIZE in *. lia.
      + apply awr_ok_nil. }
  lazymatch goal with |- context [with_vm_backing ?l ?m ?d] => set (mdv2 := with_vm_backing l m d) in *; clearbody mdv2 end.
  rename ms0 into ms2, HFr0 into HFr2.
  assert (Hge16 : (16 <= length (r_calls (i_R x)))%nat) by (unfold n in H16; lia).
  assert (Hslot2 : hs_slot (i_R x) = A_REC_SPILL).
  { unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls (i_R x))) 16); [lia | reflexivity]. }
  assert (SIGRCF : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
  { rewrite (hh_sigp _ _ HH CS_rec_calls_free ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))).
    reflexivity. }
  pmkst HS. rewrite SIGRCF.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  assert (Qsp : spZ (ms_regs ms2) = sp0 + -112).
  { unfold spZ at 1. rewrite P2, E2. rewrite (unsigned_lit_small sp0) by lia. rewrite unsigned_lit_small by lia. lia. }
  assert (HR0c : hs_regs0 x (ms_regs ms2)).
  { split; [rewrite P2, E2, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [rewrite P3; exact (EE 3%nat 3%bv eq_refl)|].
    split; [rewrite P4; exact (EE 4%nat 4%bv eq_refl)|].
    split; [rewrite P8, Hslot2; exact ESP|].
    split; [rewrite P9, (EE 12%nat 12%bv eq_refl); exact H12|].
    split; [rewrite P22; exact EG|].
    rewrite P23; exact E32. }
  pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRG0. cbn [ms_mem restrict] in HRG0.
  pose proof (st_ok_region_nth E _ _ 3 _ HS eq_refl) as HRG3. cbn [ms_mem restrict] in HRG3.
  assert (HFRk : hs_frame (rdW (i_W x) (ms_mem ms2)) sp0 (i_regs x)).
  { apply (hs3_frame_of_region E (ms_mem ms2) (w_H (i_W x)) sp0 (i_regs x) _ HRG0).
    - rewrite E2. apply unsigned_lit_small. lia.
    - intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; hs3_in|]).
      destruct j; cbn in Hj; discriminate Hj.
    - exact EER. }
  assert (HNCk : aval_mem (rdW (i_W x) (ms_mem ms2)) (A_G_REC + OFF_NCALLS) 4 n).
  { apply (RecBLemmas.aval_mem_view SEGS).
    exact (field_of_region E _ (A_OBJ 44) A_G_REC _ 8 12 8 12 8 4%N (SOff 33 0) n HRG3
      ltac:(rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia) ltac:(cbn [In]; hs3_in)
      ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (KS : forall a, hs_in_rec a \/ hs_in_own (i_O x) a -> rdW (i_W x) (ms_mem ms2) a = rdW (i_W x) (i_mem x) a).
  { intros a Ha. pose proof (hs3_own_bounds _ _ _ _ _ (i_O x) a HAR HOin Ha) as Hab.
    destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh|Hh]].
    2: { exact (hs3_aval_eq _ _ _ 4 n HNC HNCk a ltac:(cbn; lia)). }
    all: rewrite (RecBLemmas.recb_run_keeps_m E _ _ _ _ a HFr2); [| lia | apply NW; [reflexivity | exact Hab | lia]];
      apply (RecBLemmas.recb_run_keeps_m E _ _ _ _ a HFr); [lia | apply NW; [reflexivity | exact Hab | lia]]. }
  pose proof (hs_rec_kept B _ _ _ _ _ _ (i_R x) (i_O x) HREP0 KS HOin) as HREPk.
  destruct (hs_rec_spill_args B _ _ _ _ _ HREPk) as (Q & HQA & HQiff & HQlen6 & HQlen & HQnargs & HQargs & HQnd & HQsub & HQsup).
  assert (HRSF : rec_spill_frees (i_R x) = Z.of_nat (length (l_spill Q))).
  { unfold rec_spill_frees. destruct (Nat.ltb_spec (length (r_calls (i_R x))) 16) as [Hl|_]; [lia|].
    rewrite HQlen. reflexivity. }
  pose proof (hs3_aro x (i_ly x) (i_S x) (i_W x) (ms_mem ms2) _ 0 HCX HJ) as HROD1.
  assert (HEV1 : st_nev (i_S x) + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
  { unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, <- HRSF.
    clear - HEV. unfold EV_SUP_HOST_SETTING, EV_ARG_LINE, EV_ARG_I, EV_XSTRDUP, EV_REC_CANONICAL in HEV. lia. }
  assert (HMOK1 : mo_ok MT (i_S x) (XM_REC_CALLS_FREE MT [l_spill Q])).
  { apply (mo_ok_le MT ML _ _ _ HMOK). unfold XM_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, <- HRSF.
    clear - M1 M2 M3 M4 M5. unfold XM_SUP_HOST_SETTING. lia. }
  assert (Hents : forall i P, nth_error [l_spill Q] i = Some P ->
    (length P <= 6)%nat /\
    aval_mem (rdW (i_W x) (ms_mem ms2)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
    forall a pn, nth_error P a = Some pn ->
      aval_mem (rdW (i_W x) (ms_mem ms2)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
      In pn (ablocks B (i_ly x) (i_S x))).
  { intros i P Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn in Hi. injection Hi as <-.
    split; [exact HQlen6|]. split.
    - replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by (cbn [Z.of_nat]; lia).
      exact HQnargs.
    - intros a pn Ha. destruct (HQargs a pn Ha) as [V Hin]. split; [|exact Hin].
      replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
        with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn [Z.of_nat]; lia).
      exact V. }
  assert (Hnd : NoDup (map fst (concat [l_spill Q]))) by (cbn [concat]; rewrite app_nil_r; exact HQnd).
  assert (Hhome : rcf_home B (i_ly x) (i_S x) (i_W x) (ms_mem ms2) A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q])))
    by (right; left; split; [lia | cbn [length Z.of_nat]; unfold CALL_SIZE, SC_SIZE; lia]).
  assert (WRCF : REC_CALLS_FREE_STK = 16496) by reflexivity.
  (* the call of rec_calls_free(&record.spill, 1) *)
  eapply SRr_bind.
  { eapply (hh_CL _ _ HH fx (i_W x) (ms_regs ms2) (ms_mem ms2) (Z_to_bv 64 (BASE + AF_rec_calls_free))
      SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] (i_ly x) (i_S x) _ 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-112) (getr (ms_regs ms2) 1) []
      _ HJ Qsp).
    - reflexivity.
    - lia.
    - rewrite WRCF; lia.
    - rewrite WRCF, WS; lia.
    - rewrite P3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite P4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - reflexivity.
    - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite P1, unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. rewrite P8. change (ew E 292) with (ew E (A_OBJ 51)).
      rewrite ESP, unsigned_lit_small by (unfold A_REC_SPILL; lia). unfold A_REC_SPILL. lia.
    - intros HPRE1.
      exact (hh_rcf _ _ HH fx (i_ly x) (i_S x) (i_W x) (ms_regs ms2) (ms_mem ms2) _ [] A_REC_SPILL [l_spill Q] HPRE1 HROD1
        (eq_trans P10 ESP) ltac:(rewrite P11; reflexivity) ltac:(cbn; lia) Hhome
        ltac:(unfold A_REC_SPILL; reflexivity) Hents Hnd HEV1 HMOK1).
    - intros a (r & Hr & Hrq). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
      + right; right. apply hs3_rec_prog. right. cbn [length seq map In] in Hr. destruct Hr as [<- | []].
        cbn [fst snd Z.of_nat] in Hrq. cbv [A_REC_SPILL CALL_SIZE CALL_OFF_NARGS SC_SIZE] in Hrq |- *. lia.
      + left. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k0] & <- & Hpk). cbn [fst snd] in Hrq.
        cbn [concat] in Hpk. rewrite app_nil_r in Hpk.
        assert (HpO : In (p, k0) (i_O x)) by (apply HQiff; apply hs_lay_spill; exact Hpk).
        split.
        * exists (p, p + req_size k0). split; [|cbn [fst snd]; lia].
          right; right. unfold ablocks_fp. exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ _ HpO).
        * exists p, k0. split; [exact (HOin _ HpO) | lia]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK2).
  destruct HK2 as (Hperm & _ & _ & _ & _ & HSP & _ & _ & HML).
  pose proof (HSP (i_R x) Q HQA eq_refl eq_refl) as HREP2.
  rewrite P1.
  assert (HPin : forall pn, In pn (concat [l_spill Q]) -> In pn (ablocks B (i_ly x) (i_S x)))
    by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hpn).
  assert (HFR2 : hs_frame (rdW W2 mem2) sp0 (i_regs x)).
  { apply (hs3_frame_kept (rdW (i_W x) (ms_mem ms2))); [exact HFRk|]. intros a Ha.
    pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
    apply K1; [lia | rewrite WRCF; lia |].
    intros (r & Hr & Hrq). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
    - cbn [length seq map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd Z.of_nat] in Hrq.
      cbv [A_REC_SPILL CALL_SIZE CALL_OFF_NARGS] in Hrq. lia.
    - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k0] & <- & Hpk). cbn [fst snd] in Hrq.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k0 HAR (HPin _ Hpk)) as (_ & _ & Hpc & _). lia. }
  assert (HBB2 : blocks_bytes S2 <= blocks_bytes (i_S x) + bsum []).
  { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (i_ly x) (i_S x)), (bsum_perm _ _ Hperm), bsum_app.
    assert (0 <= bsum (concat [l_spill Q])).
    { apply hs3_bsum_nonneg. intros [p k0] Hpn. cbn [snd].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k0 HAR (HPin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk). lia. }
    change (bsum []) with 0. lia. }
  refine (HRCF ly2 S2 W2 mem2 md2 regs2 (0 + EV_REC_CALLS_FREE [l_spill Q])
    (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) (ablocks B ly2 S2) Hge16 HCX _ HREP2 _ _ _).
  + split; [exact HJ2|].
    split; [unfold EV_REC_CALLS_FREE, hs_k0; cbn [concat]; rewrite app_nil_r, HRSF; lia|].
    split; [apply (mle_weaken MT _ _ _ _ ML HML); unfold XM_REC_CALLS_FREE, hs_m0; cbn [concat]; rewrite app_nil_r, HRSF; lia|].
    split; [exact HBB2|]. split; [exact HFR2|].
    split; [apply Permutation_refl|].
    split; [intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hpn|].
    split.
    { intros pn Hpn Hno. apply (Permutation_in _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact Hpn|].
      exfalso. apply Hno. apply HQiff. apply hs_lay_spill. cbn [concat] in Hpn. rewrite app_nil_r in Hpn. exact Hpn. }
    split.
    { intros pn Hpn HpO. destruct (HQsup pn HpO) as [Hs | Hs]; [|exact Hs]. exfalso.
      pose proof (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR) as ND. apply (Permutation_NoDup Hperm) in ND.
      apply (RecBLemmas.list_nodup_app_disj _ _ pn ND Hpn). cbn [concat]. rewrite app_nil_r. exact Hs. }
    split; [exact HQsub|]. split; [intros pn []|].
    intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREP2 pn Hpn)).
  + exact (hs3_regs0_pres x (ms_regs ms2) regs2 HR0c HP2).
  + rewrite (hs3_pres_reg _ regs2 18 HP2 ltac:(hs3_cs)), P18, (EE 11%nat 11%bv eq_refl). exact H11.
  + rewrite (hs3_pres_reg _ regs2 20 HP2 ltac:(hs3_cs)), P20, (EE 10%nat 10%bv eq_refl). exact H10.
Qed.

End e.
End f.
End d.
