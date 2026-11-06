(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths and module names changed; 628 of its 672 lines of code are new or changed and 385 lines of the source are left out. *)
(* The walk of check_words_chain on the ASan build of plugin-hostd/fuzz_command, stage 4: the tail, from 0x88ed4 to
   the teardown 0x88f6c (27 instructions and three calls), stated as CWC_TAIL_stmt of check_words_chain_iv.v.

   The stage builds its symbolic state again from the concrete registers and memory the statement gives
   (cwt_entry): the spill slots at sp1 as a read-only region based on s1 (atom 9), the three fields of the
   recorded call that the code reads as a read-only region based on atom 33 (cp), and one shadow entry for
   the recorded call's bytes, which cr_grec_ra marks usable. Atoms 32..37 are the shadow base, cp, its
   arguments 1 and 2, the frame and read. No region is writable and the code stores nothing, so the token
   executor runs it (paj_run_tok over sh_ok).

   - 0x88ed4 .. 0x88ef4: s3 := the frame, s8 := count, a3 := read - 2 (addiw), a2 := "%d", a1 := 16, then the
     snprintf wrapper (PaRt's cwc_aj_snprintf_atSF under ASNPRINTF at the stage's FP state fx). The text
     pf_dec (read - 2) is at most 11 bytes, so it is not cut and count holds it with its terminator. Count lies
     in the class-4 frame the journal owns; its shadow bytes are the ones cwc_fshadow says are 0. The wrapper
     returns at some FP state fx1 (statement pass 4): the stage's post at fx1 is lifted to fx (PaFx.v's
     srr_apost_baseF_lift), the symbolic state moves to fx1 (PaFx.v's st_ok_pi_restrict_xfx), and the rest of the tail
     runs at fx1, with the strcmp entries and the teardown TD at fx1.
   - 0x88ef8 .. 0x88f44: the instrumented checks of call->nargs and call->args[1] (the executor removes them
     from the shadow entry, so the error paths 0x89000 .. 0x8901c are not reached), nargs = 3 so the branch
     to the abort pair 0x88ff8 is not taken, then the strcmp wrapper on args[1] and count (aj_art_at under
     ASTRCMP). Both strings are the statement's x1, so the answer is 0 and the branch to 0x88ff8 is not taken.
   - 0x88f48 .. 0x88f68: the same for call->args[2] against list, which holds x2.
   - 0x88f6c: the teardown, TD at fx1, with the journal after the three calls (the frame still owned); its post
     (apost_base at fx1) is apost_baseF at fx1 (PaFx.v's apost_baseF_of_base).

   Between the calls the walk carries its facts by what each wrapper keeps: snprintf writes only count and
   its window below sp1, strcmp only its window. The strings of the recorded call lie wholly outside the frame
   (cwt_str_apart: they lie in blocks of the entry), so count's text does not reach them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YK1g.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArt PaRt PaWalk CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_chain_c check_words_chain_s0 check_words_chain_iv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFCmd RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* atoms 32..37: the shadow base, the recorded call, its arguments 1 and 2, the frame, read *)
Definition cwt_extra (cp p1 p2 F r : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; cp; p1; p2; F; r].
Definition cwt_spillR : YP09.region :=
YP09.mkRegion (Some 9%nat) 8 64 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0));
YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 32 0));
YP09.mkChunk 48 (CVal 8 (SOff 36 32)); YP09.mkChunk 56 (CVal 8 (SOff 37 0))].
Definition cwt_grecR : YP09.region :=
YP09.mkRegion (Some 33%nat) 4 56 0 0
[YP09.mkChunk 4 (CVal 4 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))].
Definition cwt_regions : smem := [cwt_spillR; cwt_grecR].
Definition cwt_facts : facts :=
mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF (A_G_REC + OFF_CALLS) (A_G_REC + REC_SIZE - CALL_SIZE) 0);
(32%nat, mkAF SB SB 0)] [] [].
Definition cwt_SH : list shent := [mkSHE 33 4 56].
Definition cwt_ss : sstate := mkSS CWC_TAIL sr_atoms cwt_regions None cwt_facts.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition cwt_E (regsc : bvmap 5 word) (cp p1 p2 F r : Z) : env := Eimg (Ereg regsc (cwt_extra cp p1 p2 F r)).

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HR : CwcRec B RLO RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis TD : forall fx0 : YK11.FPState, CWC_TD_stmt (fx := fx0) B RLO RHI.

(* the symbolic state at 0x88ed4 from the concrete registers and memory *)
Lemma cwt_entry : forall ly S2 (W : world SEGS) memc mdc (regsc : bvmap 5 word) (cp p1 p2 F r sp1 : Z),
AR SEGS B ly S2 W memc mdc ->
getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
cwc_spill (mrestrict (w_H W) memc) sp1 cp F r ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW W memc) (cp + CALL_OFF_NARGS) 4 3 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 8) 8 p1 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 16) 8 p2 ->
0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> 0 <= F -> F + 32 < 2 ^ 64 -> 0 <= r <= 64 ->
st_ok_pi SEGS VAL (cwt_E regsc cp p1 p2 F r) cwt_ss
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_TAIL)) memc (seg_rom SEGS)))
/\ sh_ok SEGS CWC_Bx cwt_SH (cwt_E regsc cp p1 p2 F r) (mrestrict (w_H W) memc).
Proof.
intros ly S2 W memc mdc regsc cp p1 p2 F r sp1 HAR R9 Hs1lo Hs1hi Hs1al HSP Hcp1 Hcp2 HN HQ1 HQ2 Rp1 Rp2 HF0 HF1 Hr.
destruct HSP as (_ & S8 & S16 & S24 & S32 & S48 & S56).
unfold OFF_LIST in S48.
unfold CALL_OFF_NARGS, CALL_OFF_ARGS in HN, HQ1, HQ2.
replace (cp + 8 + 8) with (cp + 16) in HQ1 by lia.
replace (cp + 8 + 16) with (cp + 24) in HQ2 by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := cwt_E regsc cp p1 p2 F r).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsc (cwt_extra cp p1 p2 F r)) n)
by (intros n Hn; subst E; unfold cwt_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact R9).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (cwt_extra cp p1 p2 F r) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth cwt_extra map] in E32, E33, E34, E35, E36, E37.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = cp)
by (rewrite E33; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (BS : base_val E (Some 9%nat) = sp1) by (cbn [base_val]; exact U9).
assert (BC : base_val E (Some 33%nat) = cp) by (cbn [base_val]; exact U33).
split.
- unfold cwt_ss. apply pa_entry_st_ok_full.
  + unfold E, cwt_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cwt_regions, cwt_spillR, cwt_grecR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite BS. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
      -- apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 33 0) cp);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; zside | zside | exact S8].
      -- apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 36 0) F);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact S16].
      -- apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 36 0) F);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact S24].
      -- apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 32 0) SHADOW_OFF);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | unfold SHADOW_OFF; zside | zside | exact S32].
      -- apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 36 32) (F + 32));
         [cbn [sv_denot]; rewrite E36, unsigned_lit_small by lia; reflexivity | zside | zside | exact S48].
      -- apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 37 0) r);
         [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact S56].
    * rewrite BC. split; [unfold A_G_REC, OFF_CALLS in *; lia|].
      split; [unfold A_G_REC, REC_SIZE, CALL_SIZE in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ cp 4 4 (SLit 3) 3); [reflexivity | zside | zside |].
         exact (cwc_val_mem_of_aval W memc (cp + 4) 4%nat 3 HN).
      -- apply (chunk_ok_val SEGS E _ cp 16 8 (SOff 34 0) p1);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cwc_val_mem_of_aval W memc (cp + 16) 8%nat p1 HQ1).
      -- apply (chunk_ok_val SEGS E _ cp 24 8 (SOff 35 0) p2);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cwc_val_mem_of_aval W memc (cp + 24) 8%nat p2 HQ2).
  + apply pairwise_disjoint_of_extents.
    unfold cwt_regions, cwt_spillR, cwt_grecR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BS, BC.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hs1lo Hcp1 Hcp2. clear. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. intros. repeat split; lia.
  + split; [|split; exact I].
    cbn [cwt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U33, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hs1lo Hs1hi Hs1al Hcp1 Hcp2. clear. unfold SB, SHADOW_OFF, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, cwt_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E CWC_Bx 33 (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS) cp 4 56).
  + exact (cr_grec_ra B RLO RHI HR ly S2 W memc mdc HAR).
  + unfold U, CWC_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U33.
  + unfold A_G_REC, OFF_CALLS in *. lia.
  + unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE in *. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    revert Hx Hcp1 Hcp2. clear. unfold SHADOW_OFF, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. lia.
Qed.

(* --- small facts the tail reads --- *)

Lemma cwt_val_mem_kept : forall (W : world SEGS) m m' a n v,
(forall k, (k < n)%nat -> rdW W m' (a + Z.of_nat k) = rdW W m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' _ (HK k Hk)). exact (Hv k Hk).
Qed.

Lemma cwt_region_kept : forall E (W : world SEGS) m m' (r : YP09.region) (X : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> rdW W m' a = rdW W m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
  0 <= a < 2 ^ 64 /\ ~ X a) ->
YP09.r_whi r <= YP09.r_wlo r ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m') r.
Proof.
intros E W m m' r X HK HX Hro. split; intros a Ha.
- destruct (HX a Ha) as [Ha64 HnX]. apply (mbyte_of_aview SEGS). exact (HK a Ha64 HnX).
- exfalso. lia.
Qed.

Lemma cwt_ra_sub : forall (rd : reader) a n m, range_addressable rd SHADOW_OFF a n -> 0 <= m <= n ->
range_addressable rd SHADOW_OFF a m.
Proof. intros rd a n m H Hm x Hx. apply H. lia. Qed.

Lemma cwt_nz : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (pf_bytes l).
Proof.
intros l Hnz Hin. unfold pf_bytes in Hin. apply in_map_iff in Hin as (c & Hc & Hin).
rewrite Forall_forall in Hnz. pose proof (Hnz c Hin) as Hc0.
apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc.
change (bv_modulus 8) with 256 in Hc. rewrite Z.mod_small in Hc by lia. cbv in Hc. lia.
Qed.

(* count [944, 960) and list [32, 800) of the frame are marked usable by the shadow bytes cwc_fshadow names *)
Lemma cwt_ra_count : forall (rd : reader) F, F mod 8 = 0 -> cwc_fshadow rd F ->
range_addressable rd SHADOW_OFF (F + 944) 16.
Proof.
intros rd F HF (_ & _ & S118 & S119).
apply zero_shadow_of_bytes.
- replace (F + 944) with (F + 118 * 8) by lia. rewrite Z_mod_plus_full. exact HF.
- reflexivity.
- lia.
- intros i Hi. change (16 / 8) with 2 in Hi.
  replace ((F + 944) / 8) with (F / 8 + 118) by (replace (F + 944) with (118 * 8 + F) by lia; rewrite Z.div_add_l by lia; lia).
  assert (i = 0 \/ i = 1) as [-> | ->] by lia.
  + replace (SHADOW_OFF + (F / 8 + 118) + 0) with (SHADOW_OFF + F / 8 + 118) by lia. exact S118.
  + replace (SHADOW_OFF + (F / 8 + 118) + 1) with (SHADOW_OFF + F / 8 + 119) by lia. exact S119.
Qed.

Lemma cwt_ra_list : forall (rd : reader) F, F mod 8 = 0 -> cwc_fshadow rd F ->
range_addressable rd SHADOW_OFF (F + 32) 768.
Proof.
intros rd F HF (S4 & _ & _ & _).
apply zero_shadow_of_bytes.
- replace (F + 32) with (F + 4 * 8) by lia. rewrite Z_mod_plus_full. exact HF.
- reflexivity.
- lia.
- intros i Hi. change (768 / 8) with 96 in Hi.
  replace ((F + 32) / 8) with (F / 8 + 4) by (replace (F + 32) with (4 * 8 + F) by lia; rewrite Z.div_add_l by lia; lia).
  replace (SHADOW_OFF + (F / 8 + 4) + i) with (SHADOW_OFF + F / 8 + (4 + i)) by lia. apply S4. lia.
Qed.

Lemma cwt_fshadow_kept : forall (rd rd' : reader) F,
(forall i, 0 <= i < 128 -> rd' (SHADOW_OFF + F / 8 + i) = rd (SHADOW_OFF + F / 8 + i)) ->
cwc_fshadow rd F -> cwc_fshadow rd' F.
Proof.
intros rd rd' F HK (S1 & S2 & S3 & S4). split; [|split; [|split]].
- intros i Hi. rewrite HK by lia. apply S1. exact Hi.
- rewrite HK by lia. exact S2.
- rewrite HK by lia. exact S3.
- rewrite HK by lia. exact S4.
Qed.

(* the one shadow entry of the three checks: the recorded call's bytes are marked usable *)
Lemma cwt_shok : forall E ly S2 (W : world SEGS) m md cp,
AR SEGS B ly S2 W m md -> bv_unsigned (ew E 32) = SHADOW_OFF -> bv_unsigned (ew E 33) = cp ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
sh_ok SEGS CWC_Bx cwt_SH E (mrestrict (w_H W) m).
Proof.
intros E ly S2 W m md cp HAR U32 U33 Hcp1 Hcp2.
unfold sh_ok, cwt_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E CWC_Bx 33 (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS) cp 4 56).
- exact (cr_grec_ra B RLO RHI HR ly S2 W m md HAR).
- unfold U, CWC_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U32.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U33.
- unfold A_G_REC, OFF_CALLS in *. lia.
- unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE in *. lia.
- intros x Hx. cbn [Z.min Z.max] in Hx.
  revert Hx Hcp1 Hcp2. clear. unfold SHADOW_OFF, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. lia.
Qed.

(* a string argument of the recorded call lies wholly below or wholly above the side-stack frame: it is in a block
   of the entry, and blocks and frames are apart *)
Lemma cwt_str_apart : forall ly S S2 (W : world SEGS) m md fpos p x (rd : reader),
AR SEGS B ly S2 W m md -> In (CWC_CID, fpos) (frames S2) -> ablocks B ly S2 = ablocks B ly S ->
cwc_sblk B ly S rd p x ->
p + astr_len x + 1 <= frame_addr ly CWC_CID fpos \/ frame_addr ly CWC_CID fpos + 1024 <= p.
Proof.
intros ly S S2 W m md fpos p x rd HAR Hfin Hab HA.
destruct HA as (_ & (b & k & Hin & Hb1 & Hb2) & _). rewrite <- Hab in Hin.
pose proof (sep_block_frame SEGS B LAWS ly S2 W m md b k CWC_CID fpos HAR Hin Hfin) as Hd.
destruct (al_blocks _ _ LAWS ly S2 W m md b k HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes CWC_CID) with 1024 in Hd.
unfold astr_len. lia.
Qed.

(* a C string inside the side-stack frame, in the form the wrapper contracts take it *)
Lemma cwt_frame_strk : forall ly S2 (W : world SEGS) m md fpos p x,
AR SEGS B ly S2 W m md -> In (CWC_CID, fpos) (frames S2) ->
frame_addr ly CWC_CID fpos <= p -> p + astr_len x + 8 <= frame_addr ly CWC_CID fpos + 1024 ->
astr_at SEGS W m p x -> range_addressable (rdW W m) SHADOW_OFF p (astr_len x + 1) ->
cwc_strk W m p x.
Proof.
intros ly S2 W m md fpos p x HAR Hfin Hlo Hhi Hs Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & HFpres & _).
change (fs_frame_bytes CWC_CID) with 1024 in HFceil, HFapp, HFpres.
assert (Hl : 0 <= astr_len x) by (unfold astr_len; lia).
assert (HP : forall a, frame_addr ly CWC_CID fpos <= a < frame_addr ly CWC_CID fpos + 1024 -> rdW W m a <> None)
by (intros a Ha; apply (aview_some_of_apresent SEGS); exact (proj1 (HFpres a Ha))).
split; [lia|]. split; [exact Hs|]. split.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply HP; lia|].
  split.
  + unfold amem_range. destruct HFapp as (_ & [HA | (HA1 & HA2)]); [left | right];
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
  + split; [exact Hra|]. intros _.
    apply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W m md CWC_CID fpos p (astr_len x + 1) HAR Hfin);
    try change (fs_frame_bytes CWC_CID) with 1024; lia.
- intros a Ha. pose proof (Z.mod_pos_bound (p + astr_len x) 8 ltac:(lia)). apply HP. lia.
Qed.

Lemma cwt_swrap32 : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. change (bv_swrap 32 z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* 0x88ed4 .. 0x88f6c: the count text, the three checks of the recorded call, the two strcmp calls, then the
   teardown (TD) *)
Lemma cwc_tail_ok : CWC_TAIL_stmt B RLO RHI.
Proof.
unfold CWC_TAIL_stmt.
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 memc mdc fpos sp1 regsc
HPRE HMID HFRM HRM0 R2 R3 R4 R8 R9 R20 HLIST SK1 SK2.
pose proof (cr_tl B RLO RHI HR) as TL. pose proof (cr_tlf B RLO RHI HR) as TLF.
pose proof HPRE as (Hafn & HRO & H10 & H11 & H12 & Hr & HCRO & HOBJ & Hguard0 & HFLAG & HERR & Hcp1 & Hcp2
& HNA & Hnargs & HA1 & HA2 & HWS & Hn3 & Hx1 & Hx2 & Hroom & Hnev).
pose proof HMID as (HJ & Hab & Hsp1e0 & HFR & HSP & HFW & HFS).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (HTS : CHECK_WORDS_CHAIN_STK = 12496) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
subst nargs.
destruct (HA1 eq_refl) as [V1 A1]. destruct (HA2 eq_refl) as [V2 A2].
assert (Hsp0lo : 0 <= spZ regs + -192) by lia.
assert (Hsp0m : (spZ regs + -192) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, Hsp0al; reflexivity).
destruct (sp1_facts (spZ regs + -192) Hsp0lo Hsp0m) as (Hsp1r & Hsp1al & Hsp1al16).
assert (Hsp1e : sp1 = 32 * ((spZ regs + -192) / 32))
by (rewrite Hsp1e0; replace (spZ regs - 192) with (spZ regs + -192) by lia; reflexivity).
rewrite <- Hsp1e in Hsp1r, Hsp1al, Hsp1al16. clear Hsp1e.
assert (Hom : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity).
assert (Hs1lo : 2 ^ 46 <= sp1) by lia. assert (Hs1hi : sp1 + 64 <= 2 ^ 47) by lia.
assert (Hwin : alloc_ceiling <= sp1 - 3 * ESTACK) by lia.
assert (HO0 : sp1 - spZ regs <= 0) by lia.
assert (HBUD : 3 * ESTACK - (sp1 - spZ regs) <= CHECK_WORDS_CHAIN_STK) by lia.
assert (HBUD2 : 2 * ESTACK - (sp1 - spZ regs) <= CHECK_WORDS_CHAIN_STK) by lia.
assert (HE2 : ESTACK <= 2 * ESTACK) by lia. assert (HST0 : 0 <= 2 * ESTACK) by lia.
subst x1 x2.
(* the frame *)
set (F := frame_addr ly CWC_CID fpos) in *.
pose proof (proj1 HJ) as HARc.
assert (Hfin : In (CWC_CID, fpos) (frames S2)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HARc Hfin) as (HFal & _ & _ & _).
change (fs_frame_bytes CWC_CID) with 1024 in HFceil, HFapp. fold F in HF4096, HFceil, HFapp, HFal.
assert (F8 : F mod 8 = 0)
by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HF0 : 0 <= F) by lia. assert (HF1 : F + 32 < 2 ^ 64) by lia.
assert (HFhi : F / 8 < 17592186044416 - 127) by (apply Z.div_lt_upper_bound; lia).
assert (FAPP : F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F)
by (destruct HFapp as (_ & [HA | (HA & _)]); [left | right]; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (GF : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> F <= a < F + 1024 -> False).
{ intros a Ha Hb. destruct (cr_grec_not_rt B RLO RHI HR a Ha) as (Himg & _ & _).
  assert (Haf : frame_addr ly CWC_CID fpos <= a < frame_addr ly CWC_CID fpos + fs_frame_bytes CWC_CID)
  by (change (fs_frame_bytes CWC_CID) with 1024; fold F; lia).
  exact (frm_img SEGS B LAWS ly S2 W memc mdc CWC_CID fpos a HARc Hfin Haf Himg). }
(* the lengths of the two texts *)
assert (HL1 : astr_len (pf_bytes (pf_dec (r - 2))) <= 11).
{ unfold astr_len. rewrite pf_bytes_len. pose proof (pf_dec_len (r - 2) ltac:(lia)). lia. }
assert (HL2 : astr_len (pf_bytes (chain_list_at atoi_a r ws)) <= 744).
{ unfold astr_len. rewrite pf_bytes_len.
  assert (Hd : forall j, (length (pf_dec (atoi_a (nth j ws []))) <= 11)%nat)
  by (intros j; apply pf_dec_len; unfold atoi_a; apply cwt_swrap32).
  pose proof (chain_list_at_len atoi_a r ws Hd Hr) as HLen. lia. }
(* the recorded call's fields at memc *)
assert (GA : forall a n v, A_G_REC <= a -> a + Z.of_nat n <= A_G_REC + REC_SIZE ->
  aval_mem (rdW W mem) a n v -> aval_mem (rdW W memc) a n v).
{ intros a n v Ha1 Ha2 Hv i Hi. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  destruct (cr_grec_not_rt B RLO RHI HR (a + Z.of_nat i) ltac:(lia)) as (Himg & Ho & He).
  rewrite (F3 _ Himg Ho He); [exact (Hv i Hi)|].
  apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil _ X)]. }
pose proof SK1 as (Hp1 & _ & (Hp1a & Hp1b & _) & _).
pose proof SK2 as (Hp2 & _ & (Hp2a & Hp2b & _) & _).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (unfold astr_len in *; lia).
assert (Rp2 : 0 <= p2 < 2 ^ 64) by (unfold astr_len in *; lia).
pose proof (cwt_str_apart ly S S2 W memc mdc fpos p1 _ _ HARc Hfin Hab A1) as AP1. fold F in AP1.
pose proof (cwt_str_apart ly S S2 W memc mdc fpos p2 _ _ HARc Hfin Hab A2) as AP2. fold F in AP2.
(* list's text at memc *)
assert (SLc : cwc_strk W memc (F + 32) (pf_bytes (chain_list_at atoi_a r ws))).
{ apply (cwt_frame_strk ly S2 W memc mdc fpos); [exact HARc | exact Hfin | fold F; lia | fold F; lia | |].
  - split; [rewrite <- pf_bytes_nul; unfold OFF_LIST in HLIST; exact HLIST | apply cwt_nz, chain_list_at_nz].
  - apply (cwt_ra_sub _ _ 768); [exact (cwt_ra_list _ F F8 HFS) | unfold astr_len in *; lia]. }
destruct (cwt_entry ly S2 W memc mdc regsc cp p1 p2 F r sp1 HARc R9 Hs1lo Hs1hi Hsp1al HSP Hcp1 Hcp2
(GA (cp + CALL_OFF_NARGS) 4%nat 3 ltac:(unfold A_G_REC, OFF_CALLS, CALL_OFF_NARGS in *; lia) ltac:(unfold A_G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *; lia) HNA)
(GA (cp + CALL_OFF_ARGS + 8) 8%nat p1 ltac:(unfold A_G_REC, OFF_CALLS, CALL_OFF_ARGS in *; lia) ltac:(unfold A_G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *; lia) V1)
(GA (cp + CALL_OFF_ARGS + 16) 8%nat p2 ltac:(unfold A_G_REC, OFF_CALLS, CALL_OFF_ARGS in *; lia) ltac:(unfold A_G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *; lia) V2)
Rp1 Rp2 HF0 HF1 Hr) as [HS SHOK].
(* the atoms of the walk's environment *)
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
  ew (cwt_E regsc cp p1 p2 F r) n = getr regsc rr)
by (intros n rr Hn Hrr; unfold cwt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 6)%nat -> ew (cwt_E regsc cp p1 p2 F r) (32 + j) = nth j (cwt_extra cp p1 p2 F r) (Z_to_bv 64 0))
by (intros j Hj; unfold cwt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as Ea32. pose proof (EX 1%nat ltac:(lia)) as Ea33.
pose proof (EX 2%nat ltac:(lia)) as Ea34. pose proof (EX 3%nat ltac:(lia)) as Ea35.
pose proof (EX 4%nat ltac:(lia)) as Ea36. pose proof (EX 5%nat ltac:(lia)) as Ea37.
cbn [Nat.add nth cwt_extra map] in Ea32, Ea33, Ea34, Ea35, Ea36, Ea37.
pose proof (EN 2%nat 2%bv ltac:(lia) eq_refl) as Ea2. pose proof (EN 3%nat 3%bv ltac:(lia) eq_refl) as Ea3.
pose proof (EN 4%nat 4%bv ltac:(lia) eq_refl) as Ea4. pose proof (EN 8%nat 8%bv ltac:(lia) eq_refl) as Ea8.
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9. pose proof (EN 20%nat 20%bv ltac:(lia) eq_refl) as Ea20.
clear EN EX.
assert (VO25 : VAL (A_OBJ 25) = 0x218a0) by (rewrite (HOBJ 25%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (U32 : bv_unsigned (ew (cwt_E regsc cp p1 p2 F r) 32) = SHADOW_OFF)
by (rewrite Ea32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (cwt_E regsc cp p1 p2 F r) 33) = cp)
by (rewrite Ea33; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia).
assert (U9 : bv_unsigned (ew (cwt_E regsc cp p1 p2 F r) 9) = sp1)
by (rewrite Ea9, R9; unfold w64; apply unsigned_lit_small; lia).
set (E := cwt_E regsc cp p1 p2 F r) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cwt_E; apply Eimg_env).
assert (Ea266 : ew E 266 = Z_to_bv 64 0x218a0).
{ rewrite (img_env_atomP E 266 HEI ltac:(unfold A_TEXT, A_LIM; lia)). change 266%nat with (A_OBJ 25). rewrite VO25. reflexivity. }
(* --- 0x88ed4 .. the snprintf call: count := the text of read - 2 --- *)
paj_run_tok RUN HS HJ SHOK CWC_Bspan; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
assert (HmemE : ms_mem ms = memc)
by (exact (frame_of_read_only _ (ss_mem cwt_ss) _ _ ltac:(vm_compute; reflexivity) HF)).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
rewrite HmemE in HJ |- *.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs)).
{ unfold spZ at 1. rewrite Q2, Ea2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Ea3; exact R3).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Ea4; exact R4).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 (F + 944))
by (rewrite Q10, Ea36; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 16) by (rewrite Q11; reflexivity).
assert (Qa2 : getr (ms_regs ms) 12 = w64 0x218a0) by (rewrite Q12, Ea266; reflexivity).
assert (Qa3 : bv_unsigned (getr (ms_regs ms) 13) mod 2 ^ 32 = (r - 2) mod 2 ^ 32).
{ rewrite Q13, Ea37, YK1g.aluw_addi_lit. unfold v_addiw. rewrite (unsigned_lit_small r) by lia.
  change (bv_swrap 32 (r + -2)) with (((r + -2) + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  rewrite (Z.mod_small (r + -2 + 2 ^ 31)) by lia.
  destruct (Z_lt_le_dec r 2) as [Hlt|Hge].
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity.
  - rewrite unsigned_lit_small by lia. f_equal. lia. }
assert (DST : forall a, F + 944 <= a < F + 944 + 16 ->
  awr_byte SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] (ablocks B ly S) (ablocks B ly S2) (frames S) ly
    [(CWC_CID, fpos)] a /\
  ~ (spZ regs + (sp1 - spZ regs) - 3 * ESTACK <= a < spZ regs + (sp1 - spZ regs))).
{ intros a Ha. split; [|lia].
  right; right; right; left. exists CWC_CID, fpos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. change (fs_frame_bytes CWC_CID) with 1024. fold F. lia. }
assert (AMR : amem_range (F + 944) (16 + 8))
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; destruct FAPP; [left | right]; lia).
assert (HULL : shadow_hull_vis (rdW W memc) (F + 944) 16).
{ apply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W memc mdv1 CWC_CID fpos (F + 944) 16 (proj1 HJ) Hfin);
  try change (fs_frame_bytes CWC_CID) with 1024; fold F; lia. }
destruct (cr_rt_cells B RLO RHI HR ly S2 W memc mdv1 (proj1 HJ)) as (Hguard1 & _ & _).
destruct (cwc_fmt_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCRO HRO HJ) as [(_ & FS & FR & FT) _].
assert (ROM1 : rt_rom_view SEGS B W memc) by (eapply cwc_rom_now; eassumption).
assert (Hc3 : alloc_ceiling <= spZ (ms_regs ms) - 3 * ESTACK) by (rewrite Qsp; lia).
pose proof (cwc_aread_of_rd (3 * ESTACK) W (ms_regs ms) memc _ _ FR Hc3) as FRD.
assert (HTL : Z.of_nat (length (pf_dec (r - 2))) < 2 ^ 31 - 1) by (pose proof (pf_dec_len (r - 2) ltac:(lia)); lia).
(* the shared contract's argument word a3 (argZ 3) *)
assert (A3 : argZ (ms_regs ms) 3 = bv_unsigned (getr (ms_regs ms) 13))
by (unfold argZ; do 2 f_equal; apply bv_eq; reflexivity).
assert (HARGS : RtPFShared.pf_args_asan (rdW W memc)
  (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms)) (F + 944) (RtPFShared.sn_len (16 - 1) (pf_dec (r - 2))))
  (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7]) (map RtPFCmd.arg_of [AInt (r - 2)])).
{ cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan map RtPFCmd.arg_of]. split; [|exact I].
  split; [lia | rewrite A3; exact Qa3]. }
assert (HN16 : 1 <= 16 < 2 ^ 31) by lia. assert (HD0 : 0 < F + 944) by lia.
assert (Hf0 : 0 < 0x218a0) by lia. assert (HDN : F + 944 + 16 <= 2 ^ 63) by lia.
(* count lies above the image, and so does the call's window *)
assert (HDI : RtPFCmd.CMD_IMG_HI <= F + 944).
{ pose proof (RtPFDog.pa_frame_above_img (PI := PI) B ly S2 W memc mdv1 CWC_CID fpos (proj1 HJ) Hfin) as HA.
  fold F in HA. lia. }
assert (HWI : RtPFCmd.CMD_IMG_HI <= spZ regs + (sp1 - spZ regs) - 3 * ESTACK) by (unfold RtPFCmd.CMD_IMG_HI; lia).
(* the read-only ranges the shared contract reads, as the image has them *)
assert (HROc : arodata_okP SEGS RLO RHI B (rdW W memc))
by exact (cwc_arodata_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRO HJ).
pose proof (CmdRecImg.cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W memc HROc) as HCV. clear HROc.
assert (HTB : Forall (fun c => 0 <= c < 256) (pf_dec (r - 2))).
{ eapply Forall_impl; [|exact (pf_dec_nz (r - 2))]. intros c Hc. cbv beta in *. lia. }
eapply SRr_bind.
{ exact (cwc_aj_snprintf_atSF SEGS B LAWS pa_segs_low _ _ _ (ASNPRINTF fx) W (ms_regs ms) memc CHECK_WORDS_CHAIN_STK
  (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 mdv1 0 (F + 944) 16 0x218a0 [37; 100] [Pd] [AInt (r - 2)]
  (pf_dec (r - 2)) (sp1 - spZ regs) (getr (ms_regs ms) 1)
  HJ Qa0 Qa1 Qa2 HN16 HD0 Hf0 HDN Qsp Hom HO0 HBUD Qgp Qtp eq_refl Qra DST
  (fun a Ha Hf => False_ind _ (inFP_nil a Hf)) AMR (cwt_ra_count _ F F8 HFS) HULL HDI HWI
  Hguard1 ltac:(lia) ltac:(unfold RtPFCmd.CMD_IMG_HI; lia) ltac:(lia) ltac:(unfold RtPFCmd.CMD_IMG_HI; lia)
  FS ltac:(repeat constructor; lia) ltac:(cbn [length]; unfold RtPFCmd.CMD_IMG_HI; lia)
  pf_parse_d (proj2 (pf_text_d (r - 2))) I HTB HTL FRD HARGS HCV ltac:(reflexivity) HRM0). }
cbv beta. intros W2 c2 _ (HW2 & fx1 & regs2 & mem2 & md2 & Hfx & Hc2 & HJ2 & HP2 & HQ2r & HCNT & HK2 & HPR2 & HSM2).
subst W2 c2. rewrite Q1.
(* the rest of the tail runs at the FP state fx1 the wrapper returned; its post at fx1 is the stage's at fx *)
unfold cwc_post. apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
pose proof (paj_run (fx := fx1) B LAWS) as RUN1. pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 944 <= a < F + 960 \/ sp1 - 3 * ESTACK <= a < sp1) ->
  rdW W mem2 a = rdW W memc a).
{ intros a Ha Hn. apply HK2; [exact Ha | intros Hx; apply Hn; left; lia | intros Hx; apply Hn; right; lia]. }
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HmemE.
  constructor; [|constructor; [|constructor]].
  - apply (cwt_region_kept _ W memc mem2 _ (fun a => F + 944 <= a < F + 960 \/ sp1 - 3 * ESTACK <= a < sp1) HK2');
    [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9. intros a Ha. cbv beta. split; [lia|]. lia.
  - apply (cwt_region_kept _ W memc mem2 _ (fun a => F + 944 <= a < F + 960 \/ sp1 - 3 * ESTACK <= a < sp1) HK2');
    [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U33. intros a Ha. cbv beta.
    unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *.
    split; [lia|]. intros [Hx|Hx]; [apply (GF a); lia | lia]. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx)) in HS2. apply (st_ok_pi_restrict_xfx fx fx1) in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
assert (HEIx2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEI | cbv; lia]) end.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
assert (SHOK2 : sh_ok SEGS CWC_Bx cwt_SH E2 (mrestrict (w_H W) mem2))
by (apply (cwt_shok E2 ly S2 W mem2 md2 cp (proj1 HJ2));
  [rewrite ew_havoc_old by lia; exact U32 | rewrite ew_havoc_old by lia; exact U33 | exact Hcp1 | exact Hcp2]) end.
(* the strings the first strcmp call reads, at mem2 *)
assert (KB2 : cwc_kept_below W memc mem2 (fun a => F + 944 <= a < F + 960)).
{ intros a Ha Hn. apply HK2'; [lia|]. intros [Hx|Hx]; [exact (Hn Hx) | lia]. }
assert (HXs : forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ (F + 944 <= s < F + 960)).
{ intros s Hs. unfold SHADOW_OFF in Hs. rewrite C2 in Hs. lia. }
assert (SK1b : cwc_strk W mem2 p1 (pf_bytes (pf_dec (r - 2)))).
{ apply (cwc_strk_kept W memc mem2 _ p1 _ KB2); [intros a Ha; cbv beta; lia | exact HXs | exact SK1]. }
assert (SK2b : cwc_strk W mem2 p2 (pf_bytes (chain_list_at atoi_a r ws))).
{ apply (cwc_strk_kept W memc mem2 _ p2 _ KB2); [intros a Ha; cbv beta; lia | exact HXs | exact SK2]. }
assert (SLb : cwc_strk W mem2 (F + 32) (pf_bytes (chain_list_at atoi_a r ws))).
{ apply (cwc_strk_kept W memc mem2 _ (F + 32) _ KB2); [intros a Ha; cbv beta; lia | exact HXs | exact SLc]. }
assert (HL16 : Z.of_nat (length (pf_dec (r - 2))) < 16) by (pose proof (pf_dec_len (r - 2) ltac:(lia)); lia).
rewrite (firstn_all_text (pf_dec (r - 2)) 16 HL16) in HCNT.
assert (HFS2 : cwc_fshadow (rdW W mem2) F).
{ apply (cwt_fshadow_kept (rdW W memc)); [|exact HFS]. intros i Hi. apply HK2'; [unfold SHADOW_OFF; lia|].
  unfold SHADOW_OFF. lia. }
assert (SC2 : cwc_strk W mem2 (F + 944) (pf_bytes (pf_dec (r - 2)))).
{ apply (cwt_frame_strk ly S2 W mem2 md2 fpos); [exact (proj1 HJ2) | exact Hfin | fold F; lia | fold F; lia | |].
  - split; [rewrite <- pf_bytes_nul; exact HCNT | apply cwt_nz, pf_dec_nz].
  - apply (cwt_ra_sub _ _ 16); [exact (cwt_ra_count _ F F8 HFS2) | unfold astr_len in *; lia]. }
(* --- 0x88ef8 .. the first strcmp call: the checks of nargs and of argument 1, strcmp(p1, count) --- *)
clear dependent ms. clear dependent mdv1.
paj_run_tok RUN1 HS HJ2 SHOK2 CWC_Bspan; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
assert (HmemF : ms_mem ms = mem2)
by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite HmemF in HJ2 |- *.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs)).
{ unfold spZ at 1. rewrite Q2, Ea2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Ea3; exact R3).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Ea4; exact R4).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 p1) by (rewrite Q10, Ea34; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 (F + 944))
by (rewrite Q11, Ea36; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hc2 : alloc_ceiling <= spZ (ms_regs ms) - 2 * ESTACK) by (rewrite Qsp; lia).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)]
  ly S2 W mem2 mdv2 0 (ms_regs ms) (sp1 - spZ regs) HJ2 Qsp Hom HO0 HE2 HBUD2 Qra Qgp Qtp) as HEP.
assert (ROM2 : rt_rom_view SEGS B W mem2) by (eapply cwc_rom_now; eassumption).
destruct SK1b as (Hp1z & SS1 & SR1 & ST1).
destruct SC2 as (Hcz & SSc & SRc & STc).
assert (HC : SRr SEGS W (cfg_at (fx := fx1) SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms) mem2 mdv2)
  (art_post (fx := fx1) SEGS B (2 * ESTACK) ly S2 W (ms_regs ms) mem2 mdv2 (fun _ => False)
  (fun regs' _ => getr regs' 10 = w64 0 <-> pf_bytes (pf_dec (r - 2)) = pf_bytes (pf_dec (r - 2)))))
by (exact (ASTRCMP fx1 ly S2 W (ms_regs ms) mem2 mdv2 p1 (F + 944) _ _ HEP Qa0 Qa1 Hp1z Hcz SS1 SSc
  (cwc_aread_of_rd _ W (ms_regs ms) mem2 _ _ SR1 Hc2) (cwc_aread_of_rd _ W (ms_regs ms) mem2 _ _ SRc Hc2) ST1 STc ROM2)).
eapply SRr_bind.
{ exact (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms) mem2 CHECK_WORDS_CHAIN_STK (spZ regs) []
  ly S W mem md [(CWC_CID, fpos)] ly S2 mdv2 0 (sp1 - spZ regs) (getr (ms_regs ms) 1)
  (fun regs' _ => getr regs' 10 = w64 0 <-> pf_bytes (pf_dec (r - 2)) = pf_bytes (pf_dec (r - 2)))
  HJ2 Qsp Hom HO0 HST0 HBUD2 eq_refl (fun a H => False_ind _ H) HC). }
cbv beta. intros W3 c3 _ (HW3 & regs3 & mem3 & md3 & Hc3' & HJ3 & HP3 & HQr3 & HKP3). subst W3 c3.
rewrite Q1.
assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) -> rdW W mem3 a = rdW W mem2 a).
{ intros a Ha Hn. apply HKP3; [exact Ha | lia | intros Hf; exact Hf]. }
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HmemF.
  constructor; [|constructor; [|constructor]].
  - apply (cwt_region_kept _ W mem2 mem3 _ (fun a => sp1 - 2 * ESTACK <= a < sp1) HK3); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite ew_havoc_old by lia. rewrite U9.
    intros a Ha. cbv beta. lia.
  - apply (cwt_region_kept _ W mem2 mem3 _ (fun a => sp1 - 2 * ESTACK <= a < sp1) HK3); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite ew_havoc_old by lia. rewrite U33.
    intros a Ha. cbv beta. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS3. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (HEIx3 : img_env VAL A_LIM E3) by (apply img_env_havoc; [exact HEIx2 | cbv; lia]) end.
apply (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0) in HS;
[| cbn [ms_regs restrict mkst]; exact (proj2 HQr3 eq_refl) | reflexivity].
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (SHOK3 : sh_ok SEGS CWC_Bx cwt_SH E3 (mrestrict (w_H W) mem3))
by (apply (cwt_shok E3 ly S2 W mem3 md3 cp (proj1 HJ3));
  [rewrite !ew_havoc_old by lia; exact U32 | rewrite !ew_havoc_old by lia; exact U33 | exact Hcp1 | exact Hcp2]) end.
assert (KB3 : cwc_kept_below W mem2 mem3 (fun _ => False)) by (intros a Ha _; apply HK3; lia).
assert (HXs0 : forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ False) by (intros s _ Hf; exact Hf).
assert (SK2c : cwc_strk W mem3 p2 (pf_bytes (chain_list_at atoi_a r ws)))
by (apply (cwc_strk_kept W mem2 mem3 _ p2 _ KB3); [intros a _ Hf; exact Hf | exact HXs0 | exact SK2b]).
assert (SLd : cwc_strk W mem3 (F + 32) (pf_bytes (chain_list_at atoi_a r ws)))
by (apply (cwc_strk_kept W mem2 mem3 _ (F + 32) _ KB3); [intros a _ Hf; exact Hf | exact HXs0 | exact SLb]).
(* --- 0x88f44 .. the second strcmp call: the check of argument 2, strcmp(p2, list) --- *)
clear dependent ms. clear dependent mdv2.
paj_run_tok RUN1 HS HJ3 SHOK3 CWC_Bspan; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
assert (HmemG : ms_mem ms = mem3)
by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite HmemG in HJ3 |- *.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs)).
{ unfold spZ at 1. rewrite Q2, Ea2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Ea3; exact R3).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Ea4; exact R4).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 p2) by (rewrite Q10, Ea35; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 (F + 32))
by (rewrite Q11, Ea36; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hc2 : alloc_ceiling <= spZ (ms_regs ms) - 2 * ESTACK) by (rewrite Qsp; lia).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)]
  ly S2 W mem3 mdv3 0 (ms_regs ms) (sp1 - spZ regs) HJ3 Qsp Hom HO0 HE2 HBUD2 Qra Qgp Qtp) as HEP.
assert (ROM3 : rt_rom_view SEGS B W mem3) by (eapply cwc_rom_now; eassumption).
destruct SK2c as (Hp2z & SS2 & SR2 & ST2).
destruct SLd as (Hlz & SSl & SRl & STl).
assert (HC : SRr SEGS W (cfg_at (fx := fx1) SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms) mem3 mdv3)
  (art_post (fx := fx1) SEGS B (2 * ESTACK) ly S2 W (ms_regs ms) mem3 mdv3 (fun _ => False)
  (fun regs' _ => getr regs' 10 = w64 0 <->
    pf_bytes (chain_list_at atoi_a r ws) = pf_bytes (chain_list_at atoi_a r ws))))
by (exact (ASTRCMP fx1 ly S2 W (ms_regs ms) mem3 mdv3 p2 (F + 32) _ _ HEP Qa0 Qa1 Hp2z Hlz SS2 SSl
  (cwc_aread_of_rd _ W (ms_regs ms) mem3 _ _ SR2 Hc2) (cwc_aread_of_rd _ W (ms_regs ms) mem3 _ _ SRl Hc2) ST2 STl ROM3)).
eapply SRr_bind.
{ exact (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms) mem3 CHECK_WORDS_CHAIN_STK (spZ regs) []
  ly S W mem md [(CWC_CID, fpos)] ly S2 mdv3 0 (sp1 - spZ regs) (getr (ms_regs ms) 1)
  (fun regs' _ => getr regs' 10 = w64 0 <->
    pf_bytes (chain_list_at atoi_a r ws) = pf_bytes (chain_list_at atoi_a r ws))
  HJ3 Qsp Hom HO0 HST0 HBUD2 eq_refl (fun a H => False_ind _ H) HC). }
cbv beta. intros W4 c4 _ (HW4 & regs4 & mem4 & md4 & Hc4' & HJ4 & HP4 & HQr4 & HKP4). subst W4 c4.
rewrite Q1.
assert (HK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) -> rdW W mem4 a = rdW W mem3 a).
{ intros a Ha Hn. apply HKP4; [exact Ha | lia | intros Hf; exact Hf]. }
jafter_call_keep_pi HS 80%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HmemG.
  constructor; [|constructor; [|constructor]].
  - apply (cwt_region_kept _ W mem3 mem4 _ (fun a => sp1 - 2 * ESTACK <= a < sp1) HK4); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ew_havoc_old by lia. rewrite U9.
    intros a Ha. cbv beta. lia.
  - apply (cwt_region_kept _ W mem3 mem4 _ (fun a => sp1 - 2 * ESTACK <= a < sp1) HK4); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ew_havoc_old by lia. rewrite U33.
    intros a Ha. cbv beta. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS4. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
assert (HEIx4 : img_env VAL A_LIM E4) by (apply img_env_havoc; [exact HEIx3 | cbv; lia]) end.
apply (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0) in HS;
[| cbn [ms_regs restrict mkst]; exact (proj2 HQr4 eq_refl) | reflexivity].
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
assert (SHOK4 : sh_ok SEGS CWC_Bx [] E4 (mrestrict (w_H W) mem4)) by constructor end.
(* --- 0x88f68 (bnez a0, not taken) .. the teardown --- *)
clear dependent ms. clear dependent mdv3.
paj_run_to_tok RUNTO1 HS HJ4 SHOK4 CWC_Bspan CWC_TEARDOWN; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv4 := mdx) in *; clearbody mdv4 end.
assert (HmemH : ms_mem ms = mem4)
by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pmkst HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4. prreg HS (8%bv : bv 5) G8.
prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
rewrite HmemH in HJ4 |- *.
(* what the teardown needs of mem4: the three calls wrote count and their windows below sp1 only *)
assert (Kall : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 944 <= a < F + 960) -> ~ (sp1 - 3 * ESTACK <= a < sp1) ->
  rdW W mem4 a = rdW W memc a).
{ intros a Ha H1 H2. rewrite HK4; [|exact Ha|lia]. rewrite HK3; [|exact Ha|lia]. apply HK2'; [exact Ha|]. tauto. }
assert (HMID4 : cwc_mid B ly S W regs mem md S2 mem4 mdv4 fpos sp1 cp r).
{ unfold cwc_mid. fold F.
  split; [exact HJ4|]. split; [exact Hab|]. split; [exact Hsp1e0|]. split.
  - intros j rr Hj. apply (cwt_val_mem_kept W memc mem4); [|exact (HFR j rr Hj)].
    assert (Hjl : (j < length cwc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cwc_saved] in Hjl.
    intros k Hk. apply Kall; lia.
  - split; [|split].
    + destruct HSP as (S0 & S8 & S16 & S24 & S32 & S48 & S56).
      repeat split; (eapply (cwt_val_mem_kept W memc mem4); [intros k Hk; apply Kall; lia | eassumption]).
    + rewrite <- HFW. apply rdword_ext. intros k Hk. apply Kall; lia.
    + apply (cwt_fshadow_kept (rdW W memc)); [|exact HFS]. intros i Hi. apply Kall; unfold SHADOW_OFF; lia. }
change (Z_to_bv 64 (BASE + 10888)) with (Z_to_bv 64 (BASE + CWC_TEARDOWN)).
(* the teardown at fx1: its post (apost_base at fx1) is apost_baseF at fx1 *)
eapply SRr_mono;
[ apply (TD fx1 ly S W regs mem md ch cp wp r 3 p1 p2 pw ws _ _ S2 mem4 mdv4 fpos sp1 (ms_regs ms) HPRE HMID4 HFRM)
| intros W' c' _ HPB; exact (apost_baseF_of_base (fx := fx1) SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ HPB) ].
- rewrite G2, Ea2. exact R2.
- rewrite G3, Ea3. exact R3.
- rewrite G4, Ea4. exact R4.
- rewrite G8, Ea8. exact R8.
- rewrite G9, Ea9. exact R9.
- rewrite G18, Ea36. reflexivity.
- rewrite G19, Ea36. reflexivity.
- rewrite G20, Ea20. exact R20.
Qed.
End e.
End c.
End b.
