(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths changed; 400 of its 473 lines of code are new or changed and 1587 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan), segment I2: the stretch after the first atoi,
   from 0x87e00 (listing 0x18d0), with the kind byte b in s4 and the word number k in a0. The B twin of the A walk's
   lib/A/Prog/check_words_sI2x.v (an earlier version).
     0x87e00 .. 0x87e04  `blt a0, read` (read = the scratch slot sp1 + 160).
     0x87e08 .. 0x87e2c  k >= read: s5 := (b = '?') ? 0 : "" (0x212c0), by the and/seqz/xori/addi/and sequence; ICMP
                         (0x87ee4) with want_at's None ('?') or Some [] ('#', a word).
     0x87e30 .. 0x87e74  k < read: the instrumented check of w at Wd + 16 (error path 0x881ac), w->w, &w->w[k] and the
                         UBSan precompute of its overflow; `bne s4, '#'`.
     0x87e78 .. 0x87e9c  '#': the trap sites 0x87e78 (w->w + k null or wraps), 0x87e7c (w->w null), 0x87e84
                         (misaligned), the instrumented check of &w->w[k] (error path 0x881b4), atoi(w->w[k]); back at
                         0x87ea0 (listing 0x1970, i2_H_spec).
     0x87ec0 .. 0x87ee0  a word or '?': the trap sites 0x87ec0, 0x87ec4, 0x87ecc, the instrumented check of &w->w[k]
                         (error path 0x881b8), s5 := w->w[k]; ICMP with Some (nth k ws []).
   The seed (i2x_ss) holds the scratch slots 136 = (Wd + 16) / 8, 144 = Wd + 16, 160 = read and, for k < read, the
   words w->w at Wd + 16 and w->w[k] at &w->w[k], with the alias that resolves the engine's arr + (k << 3) to the atom
   of &w->w[k]; its shadow entries remove the two instrumented checks. The engine decides the trap sites 0x87e7c,
   0x87e84, 0x87ec4, 0x87ecc and the two error paths from the atoms' ranges, alignment and the shadow entries; the
   trap sites 0x87e78 / 0x87ec0 (`beqz` of the overflow precompute) are refuted by i2x_ovf_U (&w->w[k] >= w->w). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d check_words_ki check_words_sI2a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed at 0x87e00 (listing 0x18d0): atoms 9 sp1, 10 k, 20 b, 22 the shadow base; extra 32 = Wd + 16, 33 = read,
   34 = arr = w->w, 35 = &w->w[k] = arr + 8 k, 36 = w->w[k] (for k >= read, 34 .. 36 are placeholders) *)
Definition i2x_scr : YP09.region :=
YP09.mkRegion (Some 9%nat) 136 168 0 0
[YP09.mkChunk 136 (CVal 8 (SAlu ALU_SRL (SOff 32 0) (SLit 3))); YP09.mkChunk 144 (CVal 8 (SOff 32 0));
 YP09.mkChunk 160 (CVal 8 (SOff 33 0))].
Definition i2x_ww : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition i2x_ws : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition i2x_regions (hi : bool) : smem := if hi then [i2x_scr; i2x_ww; i2x_ws] else [i2x_scr].
Definition i2x_atoms : list (nat * afact) :=
[ (9%nat, mkAF (2^46) (2^47) 5); (10%nat, mkAF 0 3 0); (20%nat, mkAF 0 255 0); (22%nat, mkAF CW_SB CW_SB 0);
  (32%nat, mkAF (2^46) (2^47 - 16) 0); (33%nat, mkAF 0 64 0);
  (34%nat, mkAF 4096 PCEIL 3); (35%nat, mkAF 4096 PCEIL 3); (36%nat, mkAF 4096 PCEIL 0) ].
Definition i2x_ali : sv := SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 10 0) (SLit 3)).
Definition i2x_facts (hi : bool) : facts := mkFacts i2x_atoms [] (if hi then [(i2x_ali, SOff 35 0)] else []).
Definition i2x_ss (hi : bool) : sstate := mkSS 0x18d0 sr_atoms (i2x_regions hi) None (i2x_facts hi).
Definition i2x_SH (hi : bool) : list shent := if hi then [mkSHE 32 0 8; mkSHE 35 0 8] else [].

(* the UBSan precompute of 0x87e54 .. 0x87e6c, in the engine's form: 1 when &w->w[k] >= w->w, so the trap sites
   0x87e78 and 0x87ec0 (`beqz a2`) are not reached *)
Lemma i2x_ovf_U : forall E arr q, ew E 34 = Z_to_bv 64 arr -> ew E 35 = Z_to_bv 64 q -> 0 <= arr <= q -> q < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 35 0) (SOff 34 0)) (SLit 0)) (SLit 1)) (SLit 1))
  = 1.
Proof.
intros E arr q H34 H35 R1 R2. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 35 q H35) by lia. rewrite (U_atom E 34 arr H34) by lia. rewrite !U_SLit.
replace (q <? arr) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* s5 of 0x87e08 .. 0x87e28 with k >= read, in the engine's form: 0 for '?', the literal "" (atom 265 = A_OBJ 24,
   0x212c0) otherwise *)
Lemma i2x_s5_ge : forall E b k rd, ew E 20 = Z_to_bv 64 b -> ew E 10 = Z_to_bv 64 k -> ew E 33 = Z_to_bv 64 rd ->
  U E (SOff 265 0) = 0x212c0 -> 0 <= b <= 255 -> 0 <= rd <= k -> k < 2 ^ 63 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SLTU (SOff 20 (-63)) (SLit 1))
    (SAlu ALU_XOR (SAlu ALU_SLT (SOff 10 0) (SOff 33 0)) (SLit 1))) (SLit (-1))) (SOff 265 0))
  = if b =? 63 then 0 else 0x212c0.
Proof.
intros E b k rd Hb Hk Hr Ho Rb Rk Rk2.
pose proof (i2_U_seq63 E 20 b Hb Rb) as A1.
assert (A2 : U E (SAlu ALU_SLT (SOff 10 0) (SOff 33 0)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 k Hk) by lia. rewrite (U_atom E 33 rd Hr) by lia.
  rewrite !swrap64_id by (unfold half64; lia). replace (k <? rd) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ho.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite U_SAlu. cbn [zalu_raw]. rewrite A1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite A2, U_SLit.
destruct (b =? 63); reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:124-141) this file uses, word for word *)
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RRO : RRO_P.
(* the record facts of check_words_d.v (check_words_rf.v proves them from lib/B/Prog/CmdRecFacts.v) *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac i2x_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed's validity *)
Lemma i2x_seed : forall (hi : bool) (W : world SEGS) (regsc : bvmap 5 word) memc sp1 b k W16 rdv arr q wq,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 22 = w64 CW_SB ->
  getr regsc 10 = w64 k -> 0 <= k <= 3 -> getr regsc 20 = w64 b -> 0 <= b <= 255 ->
  2 ^ 46 <= W16 <= 2 ^ 47 - 16 -> sp1 + 168 <= W16 -> 0 <= rdv <= 64 ->
  4096 <= arr <= PCEIL -> arr mod 8 = 0 -> 4096 <= q <= PCEIL -> q mod 8 = 0 -> q + 8 <= sp1 ->
  4096 <= wq <= PCEIL ->
  aval_mem (rdW W memc) (sp1 + 136) 8 (W16 / 8) -> aval_mem (rdW W memc) (sp1 + 144) 8 W16 ->
  aval_mem (rdW W memc) (sp1 + 160) 8 rdv ->
  (hi = true -> q = arr + 8 * k /\ aval_mem (rdW W memc) W16 8 arr /\ aval_mem (rdW W memc) q 8 wq) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))) (i2x_ss hi)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x18d0)) memc (seg_rom SEGS))).
Proof.
intros hi W regsc memc sp1 b k W16 rdv arr q wq H9 Hsp Hsp32 H22 H10 Hk H20 Hb HW HWs Hrd Harr Harr8 Hq Hq8 Hqs Hwq
  V136 V144 V160 Vhi.
set (E := Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (subst E; rewrite (i2_EE regsc _ 10%nat 10%bv eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; rewrite (i2_EE regsc _ 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 W16) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 rdv) by (subst E; exact (i2_EX regsc _ 1 ltac:(unfold A_TEXT; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 arr) by (subst E; exact (i2_EX regsc _ 2 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 q) by (subst E; exact (i2_EX regsc _ 3 ltac:(unfold A_TEXT; lia))).
assert (E36 : ew E 36 = Z_to_bv 64 wq) by (subst E; exact (i2_EX regsc _ 4 ltac:(unfold A_TEXT; lia))).
unfold CW_SB in *.
assert (RSCR : region_ok SEGS E (mrestrict (w_H W) memc) i2x_scr).
{ unfold region_ok, i2x_scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (D8 : 0 <= W16 / 8 <= W16).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ sp1 136 8 _ (W16 / 8)); [| lia | lia |].
    + apply i2_den_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 32 W16 E32) by lia. rewrite U_SLit.
      change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      apply zcanon_small. lia.
    + exact (i2_val_of_aval _ _ _ _ _ V136).
  - apply (chunk_ok_val SEGS E _ sp1 144 8 (SOff 32 0) W16);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V144).
  - apply (chunk_ok_val SEGS E _ sp1 160 8 (SOff 33 0) rdv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V160). }
assert (FACTS : atoms_ok E i2x_atoms).
{ unfold i2x_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E10, E20, E22, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold PCEIL in *; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8. unfold CW_SB.
  repeat split; lia. }
unfold i2x_ss. rewrite restrict_mkst_fx. destruct hi.
- destruct (Vhi eq_refl) as (Hqd & Vww & Vws). apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold i2x_regions. apply Forall_cons; [exact RSCR|]. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [i2x_ww i2x_ws YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ W16 0 8 (SOff 34 0) arr);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PCEIL in *; lia | lia |].
      rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vww).
    * rewrite E35, unsigned_lit_small by (unfold PCEIL in *; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 36 0) wq);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PCEIL in *; lia | lia |].
      rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vws).
  + apply pairwise_disjoint_of_extents. unfold i2x_regions, i2x_scr, i2x_ww, i2x_ws, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32, E35, !unsigned_lit_small by (unfold PCEIL in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [exact FACTS|]. split; [exact I|]. cbn [f_alias i2x_facts alias_ok]. split; [|exact I].
    apply U_inj. rewrite (U_atom E 35 q E35) by (unfold PCEIL in *; lia). unfold i2x_ali.
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 34 arr E34) by (unfold PCEIL in *; lia).
    rewrite (U_atom E 10 k E10) by lia.
    rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (zcanon_small (k * 8)) by lia. rewrite zcanon_small by (unfold PCEIL in *; lia). lia.
- apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold i2x_regions. apply Forall_cons; [exact RSCR | apply Forall_nil].
  + apply pairwise_disjoint_of_extents. cbn [i2x_regions map zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [exact FACTS|]. split; exact I.
Qed.

(* the seed's shadow entries: the bytes Wd + 16 .. + 8 (on the caller's stack) and &w->w[k] .. + 8 (in the word
   array's block) are addressable, so the token executor removes the two instrumented checks *)
Lemma i2x_shok : forall (hi : bool) (W : world SEGS) (regsc : bvmap 5 word) memc W16 rdv arr q wq,
  getr regsc 22 = w64 CW_SB -> 2 ^ 46 <= W16 <= 2 ^ 47 - 16 -> 4096 <= q <= PCEIL ->
  (hi = true -> range_addressable (rdW W memc) SHADOW_OFF W16 8 /\ range_addressable (rdW W memc) SHADOW_OFF q 8 /\
     in_app q 8) ->
  sh_ok SEGS IBx (i2x_SH hi) (Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))) (mrestrict (w_H W) memc).
Proof.
intros hi W regsc memc W16 rdv arr q wq H22 HW Hq HRA.
set (E := Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))).
assert (E22 : ew E 22 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 W16) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 q) by (subst E; exact (i2_EX regsc _ 3 ltac:(unfold A_TEXT; lia))).
destruct hi; [|unfold sh_ok, i2x_SH; apply Forall_nil].
destruct (HRA eq_refl) as (RA1 & RA2 & Happ). unfold sh_ok, i2x_SH. repeat apply Forall_cons; try apply Forall_nil.
- apply (shent_ok_of_range SEGS (w_H W) memc E IBx 32 W16 8 W16 0 8 RA1).
  + unfold IBx. rewrite (U_atom E 22 _ E22) by (unfold CW_SB; lia). reflexivity.
  + apply (U_atom E 32 _ E32). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) memc E IBx 35 q 8 q 0 8 RA2).
  + unfold IBx. rewrite (U_atom E 22 _ E22) by (unfold CW_SB; lia). reflexivity.
  + apply (U_atom E 35 _ E35). unfold PCEIL in *; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, PCEIL in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the frozen statement of the stretch (check_words_sI2a.v's i2_A_spec), from that of its '#' continuation *)
Lemma i2_at_A : i2_H_spec B MT -> i2_A_spec B MT.
Proof.
intros HH. unfold i2_A_spec.
intros c a HICMP e lyc Sc Wc regs mem md pos sp1 line fn args j1 b k HE HST Hbhd H42 H76 Hit H20 H10.
pose proof HST as (HC & Hj1 & H23 & H19 & Heq).
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & H168 & Hiregs & Hcr & Hnth & Ha).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _ & H9 & H22 & _).
pose proof HE as ((_ & _ & _ & Hgp & Htp & _) & _ & _ & _ & _ & HOBJ & HspW & HWhi & _ & Harr64 & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Harr8).
assert (HspW' : cw_sp0 e <= e_Wd e + 16) by exact HspW.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PC : PCEIL = 0x7fffff800000) by reflexivity.
assert (V24 : VAL (A_OBJ 24) = 0x212c0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
pose proof Hlscr as (_ & _ & _ & _ & L144 & _ & _ & _ & _ & _ & L160 & _).
pose proof Hcscr as (_ & _ & _ & _ & C136).
pose proof Hline as (Hperm & _).
assert (Hsub : forall bk, In bk (ablocks B (e_ly e) (e_S e)) -> In bk (ablocks B lyc Sc))
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hbk).
pose proof (i2_parse_nth fn a j1 _ Heq) as Hnit. rewrite Hit in Hnit.
pose proof (i2_kitem_k b k (i2_item_k fn (Z.to_nat a) _ Hnit)) as Hk3.
assert (Rb : 0 <= b < 256).
{ rewrite Hbhd. pose proof (bv_unsigned_in_range 8 (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn)))) as R.
  change (bv_modulus 8) with 256 in R. exact R. }
assert (Hrd : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hrdn : cw_read e <= Z.of_nat (length (e_ws e))) by (unfold cw_read, cw_n; lia).
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (HW16 : 2 ^ 46 <= e_Wd e + 16 <= 2 ^ 47 - 16) by lia.
assert (HW16s : sp1 + 168 <= e_Wd e + 16) by lia.
assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite G3; exact Hgp).
assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite G4; exact Htp).
destruct (Z_lt_ge_dec k (cw_read e)) as [Hkr | Hkr].
- (* k < read: the word w->w[k] is read *)
  assert (Hkn : (Z.to_nat k < length (e_ws e))%nat) by (unfold cw_read, cw_n in Hkr; lia).
  destruct (cw_word_at B MT LAWS e lyc Sc Wc mem md pos EV_JOINED (Z.to_nat k) HE HJ Hsub Hkn)
    as (VW & _ & (pA & mA & HinA & HpA & HmA) & Vq & Hwq64 & (pW & mW & HinW & HpW & HmW) & _).
  rewrite Z2Nat.id in Vq by lia.
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem md pA mA HAR HinA) as (_ & HpA4 & HpAc & HappA & _ & _ & HmA0).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem md pW mW HAR HinW) as (_ & HpW4 & HpWc & _ & _ & _ & HmW0).
  pose proof (req_size_pos mA ltac:(lia)) as [_ HrqA].
  pose proof (req_size_pos mW ltac:(lia)) as [_ HrqW].
  set (wq := nth (Z.to_nat k) (e_wp e) 0) in *.
  set (y := nth (Z.to_nat k) (e_ws e) []) in *.
  assert (Hq : 4096 <= e_arr e + 8 * k /\ e_arr e + 8 * k + 8 <= alloc_ceiling) by lia.
  assert (Hwq : 4096 <= wq /\ wq + Z.of_nat (length y) + 1 <= alloc_ceiling) by lia.
  assert (Hq8 : (e_arr e + 8 * k) mod 8 = 0).
  { replace (e_arr e + 8 * k) with (e_arr e + k * 8) by lia. rewrite Z_mod_plus_full. exact Harr8. }
  pose proof (i2x_seed true Wc regs mem sp1 b k (e_Wd e + 16) (cw_read e) (e_arr e) (e_arr e + 8 * k) wq
    H9 Hsp1 Hsp32 H22 H10 Hk3 H20 ltac:(lia) HW16 HW16s Hrd ltac:(rewrite PC; lia) Harr8 ltac:(rewrite PC; lia) Hq8
    ltac:(lia) ltac:(rewrite PC; lia) C136 L144 L160 (fun _ => conj eq_refl (conj VW Vq))) as HS.
  assert (HRA : true = true -> range_addressable (rdW Wc mem) SHADOW_OFF (e_Wd e + 16) 8 /\
    range_addressable (rdW Wc mem) SHADOW_OFF (e_arr e + 8 * k) 8 /\ in_app (e_arr e + 8 * k) 8).
  { intros _. split; [|split].
    - apply (i2_stk_addressable B lyc Sc Wc mem md (e_Wd e + 16) 8 HAR); [rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem md pA mA); [exact HAR | exact HinA | lia | lia].
    - apply (in_app_sub pA (req_size mA)); [exact HappA | lia | lia | lia]. }
  pose proof (i2x_shok true Wc regs mem (e_Wd e + 16) (cw_read e) (e_arr e) (e_arr e + 8 * k) wq H22 HW16
    ltac:(rewrite PC; lia) HRA) as SHOK.
  pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) as HEI.
  pose proof (i2_EE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq])) as EV.
  pose proof (i2_HAE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq])) as HAE.
  assert (E33 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 33 =
    Z_to_bv 64 (cw_read e)) by exact (i2_EX regs _ 1 ltac:(unfold A_TEXT; lia)).
  assert (E34 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 34 =
    Z_to_bv 64 (e_arr e)) by exact (i2_EX regs _ 2 ltac:(unfold A_TEXT; lia)).
  assert (E35 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 35 =
    Z_to_bv 64 (e_arr e + 8 * k)) by exact (i2_EX regs _ 3 ltac:(unfold A_TEXT; lia)).
  assert (E36 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 36 =
    Z_to_bv 64 wq) by exact (i2_EX regs _ 4 ltac:(unfold A_TEXT; lia)).
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) as E0 eqn:HE0.
  clear HE0.
  pose proof (eq_trans (EV 10%nat 10%bv eq_refl) H10) as E10.
  pose proof (eq_trans (EV 20%nat 20%bv eq_refl) H20) as E20.
  (* 0x87e00 .. 0x87e04: `blt a0, read` *)
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* k < read: 0x87e30 .. 0x87e74, the instrumented check of w (removed by the shadow entry of Wd + 16), w->w,
       &w->w[k] and its UBSan precompute, `bne s4, '#'` *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* a word or '?': 0x87ec0, the trap site `beqz a2` *)
      rename Hc into Hc35. rewrite (i2_ne_lit E0 20 b 35 E20 ltac:(lia) ltac:(lia)) in Hc35.
      apply negb_true_iff, Z.eqb_neq in Hc35.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      psrr_branch_tok RUN BR HS SHOK IBspan.
      -- (* the trap site 0x87ec0 (w->w + k null or wraps): &w->w[k] >= w->w *)
         rename Hc into Htr.
         rewrite branch_eq_U, (i2x_ovf_U E0 (e_arr e) (e_arr e + 8 * k) E34 E35 ltac:(lia) ltac:(lia)), U_SLit in Htr.
         vm_compute in Htr. discriminate Htr.
      -- (* 0x87ec4 .. 0x87ee0: the trap sites 0x87ec4 / 0x87ecc and the instrumented check of &w->w[k] (decided
            by the engine), s5 := w->w[k], on to ICMP *)
         clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
         { awr_ok_tac. }
         set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
         i2x_preg HS (21%bv : bv 5) R21. apply (i2_reg_off _ _ 36 21%bv _ 0 E36) in R21. rewrite Z.add_0_r in R21.
         pose proof (i2_rk_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
         cbn [ms_regs restrict] in HRK.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
           by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
         change (BASE + 6580) with (BASE + CW_PC_ICMP).
         pose proof (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md _ _ mdv4 pos sp1 line c a fn args j1 HE HST HJ HRK
           ltac:(intros x Hx _ _ _; exact (KT x Hx))) as HST4.
         destruct (cw_word_at B MT LAWS e lyc Sc Wc (ms_mem ms4) mdv4 pos EV_JOINED (Z.to_nat k) HE HJ Hsub Hkn)
           as (_ & _ & _ & _ & _ & HblkW4 & HSTR4).
         apply (HICMP fx e lyc Sc Wc _ _ mdv4 pos sp1 line j1 wq (Some y) HE).
         apply (i2_icmp B MT e lyc Sc Wc _ _ mdv4 pos sp1 line c a fn args j1 wq (Some y) HST4 R21).
         ++ cbn [cw_wq]. split; [exact HSTR4|]. split; [lia|]. right; right; right.
            exists (Z.to_nat k). split; [exact Hkn|]. split; [reflexivity|]. split; [reflexivity | exact HblkW4].
         ++ rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 35) Hc35).
            destruct (b =? 63); cbn [want_at]; rewrite (proj2 (Z.ltb_lt k (cw_read e)) Hkr); reflexivity.
    * (* '#': 0x87e78, the trap site `beqz a2` *)
      rename Hc into Hc35. rewrite (i2_ne_lit E0 20 b 35 E20 ltac:(lia) ltac:(lia)) in Hc35.
      apply negb_false_iff, Z.eqb_eq in Hc35.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      psrr_branch_tok RUN BR HS SHOK IBspan.
      -- (* the trap site 0x87e78 (w->w + k null or wraps): &w->w[k] >= w->w *)
         rename Hc into Htr.
         rewrite branch_eq_U, (i2x_ovf_U E0 (e_arr e) (e_arr e + 8 * k) E34 E35 ltac:(lia) ltac:(lia)), U_SLit in Htr.
         vm_compute in Htr. discriminate Htr.
      -- (* 0x87e7c .. 0x87e9c: the trap sites 0x87e7c / 0x87e84 and the instrumented check of &w->w[k] (decided by
            the engine), a0 := w->w[k], atoi(w->w[k]), back at 0x1970 *)
         clear Hc.
         paj_run_tok RUN HS HJ SHOK IBspan.
         { awr_ok_tac. }
         set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
         i2x_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 36 10%bv _ 0 E36) in Ra0. rewrite Z.add_0_r in Ra0.
         i2x_preg HS (1%bv : bv 5) Rra. change (SOff 240 6512) with (SOff A_TEXT 6512) in Rra.
         rewrite (codeptr_val E0 6512 HEI) in Rra.
         pose proof (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
         cbn [ms_regs restrict] in HRK.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
           by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
         pose proof HRK as ((R2 & R3 & R4 & _) & _).
         apply (i2_call_atoi_w B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on cmd_heap_tail_vis
           e lyc Sc Wc (ms_regs ms4) (ms_mem ms4) mdv4 pos sp1 (Z.to_nat k) 6512 (cw_post B MT e) HE HJ Hsub Hkn).
         ++ unfold spZ. rewrite R2. exact Hsp.
         ++ lia.
         ++ exact Hsp32.
         ++ rewrite R3. exact Hgp'.
         ++ rewrite R4. exact Htp'.
         ++ exact Rra.
         ++ lia.
         ++ reflexivity.
         ++ exact Ra0.
         ++ intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
            apply (HH c a HICMP e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 k HE).
            ** apply (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md regs2 mem2 md2 pos sp1 line c a fn args j1 HE HST HJ2).
               --- exact (i2_rk_trans _ _ _ HRK (i2_rk_of_pres _ _ HP2)).
               --- intros x Hx Hs Herr Hf. rewrite (HMK2 x Hx Hs Herr Hf). exact (KT x Hx).
            ** rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_eq b 35) Hc35). reflexivity.
            ** lia.
            ** exact Hk2.
  + (* k >= read: not this case *)
    rename Hc into Hcl. rewrite (i2_lt E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcl.
    apply Z.ltb_ge in Hcl. lia.
- (* k >= read: no word is read; the seed's high regions and shadow entries are absent *)
  pose proof (i2x_seed false Wc regs mem sp1 b k (e_Wd e + 16) (cw_read e) 4096 4096 4096
    H9 Hsp1 Hsp32 H22 H10 Hk3 H20 ltac:(lia) HW16 HW16s Hrd ltac:(rewrite PC; lia) eq_refl ltac:(rewrite PC; lia) eq_refl
    ltac:(lia) ltac:(rewrite PC; lia) C136 L144 L160 ltac:(intros Hft; discriminate Hft)) as HS.
  pose proof (i2x_shok false Wc regs mem (e_Wd e + 16) (cw_read e) 4096 4096 4096 H22 HW16
    ltac:(rewrite PC; lia) ltac:(intros Hft; discriminate Hft)) as SHOK.
  pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; 4096; 4096; 4096]))) as HEI.
  pose proof (i2_EE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; 4096; 4096; 4096])) as EV.
  pose proof (i2_HAE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; 4096; 4096; 4096])) as HAE.
  assert (E33 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; 4096; 4096; 4096]))) 33 =
    Z_to_bv 64 (cw_read e)) by exact (i2_EX regs _ 1 ltac:(unfold A_TEXT; lia)).
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; 4096; 4096; 4096]))) as E0 eqn:HE0.
  clear HE0.
  pose proof (eq_trans (EV 10%nat 10%bv eq_refl) H10) as E10.
  pose proof (eq_trans (EV 20%nat 20%bv eq_refl) H20) as E20.
  assert (U265 : U E0 (SOff 265 0) = 0x212c0).
  { rewrite (U_img_atom E0 HEI 265%nat ltac:(cbv; lia)). change (VAL 265%nat) with (VAL (A_OBJ 24)). exact V24. }
  (* 0x87e00 .. 0x87e04: `blt a0, read` *)
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* k < read: not this case *)
    rename Hc into Hcl. rewrite (i2_lt E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcl.
    apply Z.ltb_lt in Hcl. lia.
  + (* 0x87e08 .. 0x87e2c: s5 := (b = '?') ? 0 : "", on to ICMP *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    i2x_preg HS (21%bv : bv 5) R21.
    rewrite (i2_den_U E0 _ _ (i2x_s5_ge E0 b k (cw_read e) E20 E10 E33 U265 ltac:(lia) ltac:(lia) ltac:(lia))) in R21.
    pose proof (i2_rk_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
    cbn [ms_regs restrict] in HRK.
    pmkst HS.
    assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms2) x = rdW Wc mem x)
      by (intros x Hx; rewrite K2, K1 by exact Hx; reflexivity).
    change (BASE + 6580) with (BASE + CW_PC_ICMP).
    pose proof (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md _ _ mdv2 pos sp1 line c a fn args j1 HE HST HJ HRK
      ltac:(intros x Hx _ _ _; exact (KT x Hx))) as HST2.
    destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc (ms_mem ms2) mdv2 pos EV_JOINED 3 HE HJ)
      as (T3 & _).
    destruct (Z.eqb_spec b 63) as [Hb63 | Hb63].
    * (* '?': want_at's None, s5 = 0 *)
      first [rewrite (proj2 (Z.eqb_eq b 63) Hb63) in R21 | idtac]. cbv beta iota in R21.
      apply (HICMP fx e lyc Sc Wc _ _ mdv2 pos sp1 line j1 0 None HE).
      apply (i2_icmp B MT e lyc Sc Wc _ _ mdv2 pos sp1 line c a fn args j1 0 None HST2 R21).
      -- reflexivity.
      -- rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 35) ltac:(lia)), (proj2 (Z.eqb_eq b 63) Hb63).
         cbn [want_at]. rewrite (proj2 (Z.ltb_ge k (cw_read e)) ltac:(lia)). reflexivity.
    * (* '#' or a word: want_at's Some [], s5 = "" 0x212c0 *)
      first [rewrite (proj2 (Z.eqb_neq b 63) Hb63) in R21 | idtac]. cbv beta iota in R21.
      apply (HICMP fx e lyc Sc Wc _ _ mdv2 pos sp1 line j1 0x212c0 (Some []) HE).
      apply (i2_icmp B MT e lyc Sc Wc _ _ mdv2 pos sp1 line c a fn args j1 0x212c0 (Some []) HST2 R21).
      -- cbn [cw_wq]. split; [exact T3|]. split; [lia|]. right; left. split; reflexivity.
      -- rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 63) Hb63).
         destruct (b =? 35); cbn [want_at]; rewrite (proj2 (Z.ltb_ge k (cw_read e)) ltac:(lia)); reflexivity.
Qed.

End e.
End f.
End d.
