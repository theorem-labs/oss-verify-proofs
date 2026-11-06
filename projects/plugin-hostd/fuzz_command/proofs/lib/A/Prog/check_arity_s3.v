(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBTemplate.v, with its module names changed; 100 of its 131 lines of code are new or changed and 157 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1 check_arity_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma ca_ss_wf : forall k mn mx, (k < 22)%nat -> regions_wf (ss_mem (ca_ss k mn mx)) = true.
Proof. intros k mn mx Hk. do 22 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Lemma ca_syn_sh_range : forall k, Forall (fun v => 0 <= v < 256) (ca_syn_sh k).
Proof.
intros k. do 22 (destruct k as [|k]; [cbn [ca_syn_sh nth]; repeat apply Forall_cons; try apply Forall_nil; lia|]).
cbn [ca_syn_sh nth]. destruct k; constructor.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_seed : forall (k : nat) (mn mx s3v sp : Z) ly S (W : world SEGS) (regs0 regs : bvmap 5 word) mem md,
(k < 22)%nat -> 0 <= mn -> mn <= s3v <= mx -> s3v <= 63 ->
AR SEGS B ly S W mem md ->
cmd_ro_ok (aview SEGS (w_H W) mem) ->
spZ regs = sp -> 2 ^ 46 <= sp -> sp + 112 <= 2 ^ 47 -> sp mod 16 = 0 ->
(forall a, sp <= a < sp + 8 -> apresent (w_H W) mem a) ->
ca_frame_at W mem sp regs0 ->
getr regs 9 = w64 (CA_GP + 24 * Z.of_nat k) ->
getr regs 18 = w64 SHADOW_OFF ->
getr regs 19 = w64 s3v ->
getr regs 21 = w64 (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)) ->
getr regs 22 = w64 CA_GP ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) (ca_ss k mn mx)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CA_SEG)) mem (seg_rom SEGS))).
Proof.
intros k mn mx s3v sp ly S W regs0 regs mem md Hk Hmn Hs3 Hs63 HAR HRO Hsp Hlo Hhi Hal Hpres HFR R9 R18 R19 R21 R22.
destruct HRO as [HROB _].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ca_extra s3v regs0))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ca_extra s3v regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 s3v) by exact (EX 0%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U32 : bv_unsigned (ew E 32) = s3v) by (rewrite E32; apply unsigned_lit_small; lia).
destruct (ca_syn_bound k Hk) as (Hsa & Hsa8 & Hsb & Hsh).
unfold ca_ss. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
   [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?a ?rr) =>
       let v := eval cbv -[Z.mul Z.add Z.sub Z.opp zcanon Z.of_nat CA_GP SHADOW_OFF] in (sr_get a rr) in
       change (sr_get a rr) with v end;
     cbn [sv_denot];
     first [ exact R9 | exact R18 | exact R21 | exact R22 | apply getr_zero
           | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
             first [ rewrite E32; exact R19 | symmetry; apply EE; reflexivity ] ]
   | ]); try (destruct Hr; fail).
- exact (ca_ss_wf k mn mx Hk).
- repeat apply Forall_cons; [ | | | | | apply Forall_nil ]; unfold region_ok.
  + unfold ca_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
    apply (YI04.chunk_ok_val SEGS E _ sp (104 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0)
      (bv_unsigned (nth j (ca_sv regs0) (Z_to_bv 64 0)))).
    * cbn [sv_denot]. replace (33 + j)%nat with (32 + (1 + j))%nat by lia. rewrite (EX (1 + j)%nat ltac:(lia)).
      cbn [ca_extra nth Nat.add]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (nth j (ca_sv regs0) (Z_to_bv 64 0))) as HR.
      change (bv_modulus 64) with (2 ^ 64) in HR. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * replace (sp + (104 - 8 * Z.of_nat j)) with (sp + 104 - 8 * Z.of_nat j) by lia. apply HFR. lia.
  + unfold ca_gparsed. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold CA_GP; lia|]. split; [unfold CA_GP; lia|]. split; [intros o Ho; lia|].
    apply ca_wchunks_ok. apply (ca_bytes_mbyte W mem CA_GP RO_g_parsed (ca_ro_gp _ HROB)).
  + unfold ca_gpsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply YI04.chunk_ok_zero. intros i Hi.
    rewrite Z.add_0_l. exact (ca_gpsh_mbyte B HB ly S W mem md HAR i Hi).
  + unfold ca_synsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    assert (Hq : ca_syn_addr k = 8 * (ca_syn_addr k / 8)) by (apply Z_div_exact_2; [lia | exact Hsa8]).
    set (q := ca_syn_addr k / 8) in *. set (nb := Z.of_nat (length (ca_syn_bytes k))) in *.
    set (ns := Z.of_nat (length (ca_syn_sh k))) in *.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply ca_zchunks_ok; [apply ca_syn_sh_range|].
    intros i Hi. exact (ca_synsh_mbyte B HB k ly S W mem md Hk HAR i Hi).
  + unfold ca_syn. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply ca_bchunks_ok. apply (ca_bytes_mbyte W mem _ _ (ca_ro_syn _ HROB k Hk)).
- apply pairwise_disjoint_of_extents. unfold ca_frame, ca_gparsed, ca_gpsh, ca_synsh, ca_syn, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  assert (Hq : ca_syn_addr k = 8 * (ca_syn_addr k / 8)) by (apply Z_div_exact_2; [lia | exact Hsa8]).
  set (q := ca_syn_addr k / 8) in *.
  set (nb := Z.of_nat (length (ca_syn_bytes k))) in *.
  set (ns := Z.of_nat (length (ca_syn_sh k))) in *.
  unfold CA_GP, SHADOW_OFF. repeat split; lia.
- split; [|split; exact I]. cbn [ca_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U32.
  refine (conj (conj _ (conj _ _)) (conj (conj _ (conj _ _)) I)).
  + lia.
  + change (2 ^ 4) with 16. exact Hal.
  + lia.
  + lia.
  + rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  + lia.
Qed.

End e.
End f.
End d.
