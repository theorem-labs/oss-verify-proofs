(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the last two steps of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86958 .. the jal to check_round_trip at 0x86970), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the symbolic state at a point inside the function) and lib/A/Prog/check_refusal_s1.v (cr_entry): the symbolic state at 0x86958 and 0x86964 with the one frame word the step loads, and the transport of the cut's facts to a state that keeps the frame, the live blocks and the program's statics. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_Krefusal_s1.v, with its module paths and module names changed; 204 of its 238 lines of code are new or changed and 177 lines of the source are left out. *)
(* B twin of lib/A/Prog/check_arity_s3.v (a working branch 9c6410fb32e): ca_seed, the symbolic
   state of check_arity_s1.v at the matched-row entry CA_SEG (0x87478) from the facts of the run, and the row
   interface every row walk of image B takes: ca_post, ca_row_pre, ca_row_open, ca_final_ok, ca_regs_back. A had the
   row interface at the head of its check_arity_s4.v; B keeps it here so that s5 .. s7 and the bcmp rows need only
   s1 .. s3, and check_arity_s4.v holds the 18 non-bcmp rows only.
   B changes (measured on the B twin 658cefbe, arityB-prep.md section 3b):
   - frame 144 bytes (A 112): spZ regs = spZ regs0 - 144 at CA_SEG, saved words at sp + 136 - 8 j, write window
     [sp, sp + 40) (B stores to 0(sp) .. 0x20(sp) at 0x87824 .. 0x87870), sp restored to SOff 2 144 at the ret.
   - s3 holds read = min(w->n, 64), in [1, 64] (A: read - 1, in [0, 63]): B's `addiw a0,s3,-1` is at the arity test
     0x87950, so the row's arity pair (mn, mx) bounds s3v - 1, and atom 32 = s3v has the fact [mn + 1, min(mx, 63) + 1].
     The UBSan site 0x87954 (`bge a0,s3`, read - 1 overflow) is decided inside each row run from that atom fact (the
     same atom, offsets -1 < 0); it is refuted in the row files, not here.
   No code is walked in this file, so no UBSan trap site is in its range. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_s1 check_arity_s2.
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

Definition ca_final_ok (sr : list sv) : bool :=
sv_eqb (sr_get sr 1) (SOff 33 0) && sv_eqb (sr_get sr 2) (SOff 2 144) &&
sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
sv_eqb (sr_get sr 8) (SOff 34 0) && sv_eqb (sr_get sr 9) (SOff 35 0) &&
sv_eqb (sr_get sr 18) (SOff 36 0) && sv_eqb (sr_get sr 19) (SOff 37 0) &&
sv_eqb (sr_get sr 20) (SOff 38 0) && sv_eqb (sr_get sr 21) (SOff 39 0) &&
sv_eqb (sr_get sr 22) (SOff 40 0) && sv_eqb (sr_get sr 23) (SOff 41 0) &&
sv_eqb (sr_get sr 24) (SOff 42 0) && sv_eqb (sr_get sr 25) (SOff 43 0) &&
sv_eqb (sr_get sr 26) (SOff 44 0) && sv_eqb (sr_get sr 27) (SOff 45 0).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Ltac ca_rb z lit j :=
  replace (Z_to_bv 5 z) with (lit : bv 5) by (apply bv_eq; reflexivity);
  match goal with GR : forall r, getr _ r = sv_denot _ (sr_get _ r) |- _ => rewrite GR end;
  match goal with Hq : sr_get (ss_regs _) lit = SOff ?n 0 |- _ => rewrite Hq;
    match goal with D0 : forall n, sv_denot _ (SOff n 0) = ew _ n |- _ => rewrite D0 end;
    change n with (32 + j)%nat end;
  match goal with EX : forall j, (j < 14)%nat -> ew _ (32 + j) = _ |- _ => rewrite (EX j ltac:(lia)) end;
  reflexivity.

Lemma ca_regs_back : forall (H : word -> bool) ss ms (regs regs0 : bvmap 5 word) s3v,
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) ss (restrict H ms) ->
ca_final_ok (ss_regs ss) = true ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
spZ regs + 144 = spZ regs0 ->
aregs_preserved regs0 (ms_regs ms) /\ getr (ms_regs ms) 1 = getr regs0 1.
Proof.
intros H ss ms regs regs0 s3v HS Hf R3 R4 Hsp.
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ca_extra s3v regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. exact (st_ok_pi_restrict_reg H E ss ms r HS). }
unfold ca_final_ok in Hf. repeat rewrite andb_true_iff in Hf.
repeat match type of Hf with
| _ /\ _ => let A := fresh "Hq" in destruct Hf as [Hf A]; apply sv_eqb_eq in A
end.
apply sv_eqb_eq in Hf.
assert (D0 : forall n, sv_denot E (SOff n 0) = ew E n).
{ intros n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 2%bv = _ |- _ => rewrite Hq end.
    cbn [sv_denot]. rewrite (EE 2%nat 2%bv eq_refl). unfold spZ in Hsp. rewrite Hsp. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 3%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 3%nat 3%bv eq_refl). exact R3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 4%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 4%nat 4%bv eq_refl). exact R4.
  + ca_rb 8 (8%bv : bv 5) 2%nat.
  + ca_rb 9 (9%bv : bv 5) 3%nat.
  + ca_rb 18 (18%bv : bv 5) 4%nat.
  + ca_rb 19 (19%bv : bv 5) 5%nat.
  + ca_rb 20 (20%bv : bv 5) 6%nat.
  + ca_rb 21 (21%bv : bv 5) 7%nat.
  + ca_rb 22 (22%bv : bv 5) 8%nat.
  + ca_rb 23 (23%bv : bv 5) 9%nat.
  + ca_rb 24 (24%bv : bv 5) 10%nat.
  + ca_rb 25 (25%bv : bv 5) 11%nat.
  + ca_rb 26 (26%bv : bv 5) 12%nat.
  + ca_rb 27 (27%bv : bv 5) 13%nat.
- rewrite GR. match goal with Hq : sr_get (ss_regs _) 1%bv = _ |- _ => rewrite Hq end.
  rewrite D0. change 33%nat with (32 + 1)%nat. rewrite (EX 1%nat ltac:(lia)). reflexivity.
Qed.

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_seed : forall (k : nat) (mn mx s3v sp : Z) ly S (W : world SEGS) (regs0 regs : bvmap 5 word) mem md,
(k < 22)%nat -> 0 <= mn -> mn <= s3v - 1 <= mx -> 1 <= s3v <= 64 ->
AR SEGS B ly S W mem md ->
cmd_ro_ok (aview SEGS (w_H W) mem) ->
spZ regs = sp -> 2 ^ 46 <= sp -> sp + 144 <= 2 ^ 47 -> sp mod 16 = 0 ->
(forall a, sp <= a < sp + 40 -> apresent (w_H W) mem a) ->
ca_frame_at W mem sp regs0 ->
getr regs 9 = w64 (CA_GP + 24 * Z.of_nat k) ->
getr regs 18 = w64 SHADOW_OFF ->
getr regs 19 = w64 s3v ->
getr regs 21 = w64 (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)) ->
getr regs 22 = w64 CA_GP ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) (ca_ss k mn mx)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CA_SEG)) mem (seg_rom SEGS))).
Proof.
intros k mn mx s3v sp ly S W regs0 regs mem md Hk Hmn Hs3 Hs64 HAR HRO Hsp Hlo Hhi Hal Hpres HFR R9 R18 R19 R21 R22.
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
    apply (YI04.chunk_ok_val SEGS E _ sp (136 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0)
      (bv_unsigned (nth j (ca_sv regs0) (Z_to_bv 64 0)))).
    * cbn [sv_denot]. replace (33 + j)%nat with (32 + (1 + j))%nat by lia. rewrite (EX (1 + j)%nat ltac:(lia)).
      cbn [ca_extra nth Nat.add]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (nth j (ca_sv regs0) (Z_to_bv 64 0))) as HR.
      change (bv_modulus 64) with (2 ^ 64) in HR. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * replace (sp + (136 - 8 * Z.of_nat j)) with (sp + 136 - 8 * Z.of_nat j) by lia. apply HFR. lia.
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

Definition ca_post (regs0 : bvmap 5 word) ly S (W0 : world SEGS) mem0 md0 : world SEGS -> config -> Prop :=
apost_base SEGS B CHECK_ARITY_STK [] regs0 ly S W0 mem0 md0 EV_CHECK_ARITY
(fun ly' S' _ _ _ _ => ly' = ly /\ S' = S).

Definition ca_row_pre (k : nat) (mn mx : Z) ly S (W0 : world SEGS) (regs0 : bvmap 5 word) mem0 md0
(W : world SEGS) (regs : bvmap 5 word) memc mdc s3v : Prop :=
ajournal SEGS B CHECK_ARITY_STK (spZ regs0) [] ly S W0 mem0 md0 [] ly S W memc mdc 0 /\
YK0s.ret_ok (getr regs0 1) /\
cmd_ro_ok (aview SEGS (w_H W) memc) /\
spZ regs = spZ regs0 - 144 /\
ca_frame_at W memc (spZ regs) regs0 /\
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 9 = w64 (CA_GP + 24 * Z.of_nat k) /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 19 = w64 s3v /\
getr regs 21 = w64 (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)) /\ getr regs 22 = w64 CA_GP /\
mn <= s3v - 1 <= mx /\ 1 <= s3v <= 64.

Lemma ca_row_open : forall k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
(k < 22)%nat -> 0 <= mn ->
ca_row_pre k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) (ca_ss k mn mx)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CA_SEG)) memc (seg_rom SEGS))).
Proof.
intros k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v Hk Hmn
(HJ & Hra & HRO & Hsp & HFR & R3 & R4 & R9 & R18 & R19 & R21 & R22 & Hs3 & Hs64).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
unfold CHECK_ARITY_STK, ESTACK in *.
apply (ca_seed k mn mx s3v (spZ regs) ly S W regs0 regs memc mdc Hk Hmn ltac:(lia) ltac:(lia) HAR HRO eq_refl);
try lia.
- rewrite Hsp. replace (spZ regs0 - 144) with (spZ regs0 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- intros a Ha. apply Hpres. lia.
- exact HFR.
- exact R9.
- exact R18.
- exact R19.
- exact R21.
- exact R22.
Qed.

End e.
End f.
End d.
