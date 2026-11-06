(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths and module names changed; 883 of its 932 lines of code are new or changed and 380 lines of the source are left out. *)
(* The walk of check_words_chain on the ASan build of plugin-hostd/fuzz_command, stage 3: the word loop,
   0x88e74 .. 0x88ed0 (18 instructions, two calls per turn), by induction on the number of turns left, over every
   FP state (statement pass 4: the snprintf wrapper returns at some FP state fx1, and the next turn, or the tail,
   runs at fx1; cwc_turn is one turn at the section's fx with the next turns at every FP state, cwc_loop_ok the
   induction).

   One turn, with F the frame, list = F + 32 and o the length of the text already in list:
   - 0x88e74-0x88e80  s9 := the format: " %d" when the word number k is above 2, else the word at sp1 + 40
     ("%d").  The executor stops at the compare, and the walk splits it; the two arms differ in one register
     only, so both give that register an atom of its own and then join at 0x88e84.
   - 0x88e84-0x88e8c  the instrumented check of w[k]: s7 + s6 - 2 is the metadata byte of w + 8k, which the
     premise cwc_wordk says is 0, so the error path at 0x89010 is not reached.  The executor's rule for a
     metadata address does not match this form (lib/Reusable/YCbn.v:60-84 takes only (x >> 3) + Bx), so the
     byte gets a read-only region of its own, based on an atom for s7 + s6 that an alias of the state names.
   - 0x88e90-0x88ea4  the call of the atoi wrapper on w[k], through PaArt's aj_art_at under AATOI.
   - 0x88ea8-0x88eb8  the call of the snprintf wrapper that appends the number to list, through PaRt's
     cwc_aj_snprintf_atSF under ASNPRINTF at fx; its text is ci_text (lib/A/Prog/CwcText.v) and is at most 12 bytes,
     and 769 - o is at least 25, so it is not cut. It returns at fx1: the turn's post at fx1 is lifted to fx
     (PaFx.v's srr_apost_baseF_lift) and the symbolic state moves to fx1 (PaFx.v's st_ok_pi_restrict_xfx).
   - 0x88ebc-0x88ed0  k, the word pointer and the length move on; if k + 1 is below read the walk takes the
     induction hypothesis, else it takes the tail stage TAIL.

   The two wrapper calls write only their own window below the stack pointer, the errno cell and (the second)
   the destination inside the frame, so the premises of the next turn carry across them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArt PaRt PaWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
check_words_chain_c check_words_chain_s0 check_words_chain_iv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFCmd RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the pc of the instrumented check in the loop, as an offset from BASE *)
Definition CWC_CHK : Z := AF_check_words_chain + 0x1e4.   (* 0x88e84, the instrumented check *)

(* (w + 16) / 8 + k - 2 is the metadata byte of w + 8k, whatever w is *)
Lemma cwc_sh_index : forall w k, SHADOW_OFF + (w + 16) / 8 + k - 2 = SHADOW_OFF + (w + 8 * k) / 8.
Proof.
intros w k.
replace (w + 16) with (w + 2 * 8) by lia. replace (w + 8 * k) with (w + k * 8) by lia.
rewrite !Z.div_add by lia. lia.
Qed.

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* --- the symbolic state at the head of the loop --- *)

(* atoms above the registers: 32 the shadow base, 33 "%d", 34 list, 35 read, 36 s7 + s6, 37 w[k], 38 the
   format of this turn *)
Definition cwc_lx (F r k wp pk : Z) : list word :=
map (Z_to_bv 64) [SHADOW_OFF; A_FMT_D; F + OFF_LIST; r; SHADOW_OFF + (wp + 16) / 8 + k; pk].

Definition cwc_lE (regsc : bvmap 5 word) (F r k wp pk : Z) : env :=
Eimg (Ereg regsc (cwc_lx F r k wp pk)).

(* the three spill slots the loop reads: "%d", list, read *)
Definition cwc_spillR : YP09.region :=
YP09.mkRegion (Some 9%nat) 40 64 0 0
[YP09.mkChunk 40 (CVal 8 (SOff 33 0));
 YP09.mkChunk 48 (CVal 8 (SOff 34 0));
 YP09.mkChunk 56 (CVal 8 (SOff 35 0))].

(* the metadata byte of w + 8k, read through the atom for s7 + s6 *)
Definition cwc_shR : YP09.region :=
YP09.mkRegion (Some 36%nat) (-2) (-1) 0 0 [YP09.mkChunk (-2) (CVal 1 (SLit 0))].

(* slot k of the word array *)
Definition cwc_wordR : YP09.region :=
YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))].

Definition cwc_lfacts : facts :=
mkFacts [] [] [(SAlu ALU_ADD (SOff 23 0) (SOff 22 0), SOff 36 0)].

Definition ss_cwc_loop : sstate :=
mkSS CWC_LOOP sr_atoms [cwc_spillR; cwc_shR; cwc_wordR] None cwc_lfacts.

(* the state at the instrumented check 0x88e84, where the two arms of the format choice join: a0 = 2 and
   s9 = atom 38, the format of this turn *)
Definition ss_cwc_chk : sstate :=
mkSS CWC_CHK
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SLit 2; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 38 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
  [cwc_spillR; cwc_shR; cwc_wordR] None cwc_lfacts.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HR : CwcRec B RLO RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  @aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis TAIL : forall fx0 : YK11.FPState, CWC_TAIL_stmt (fx := fx0) B RLO RHI.

(* one turn at the FP state fx *)
Section t. Context {fx : YK11.FPState}.


Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a byte read back as a one-byte value *)
Lemma cwc_vm1 : forall (W : world SEGS) mem a,
rdW W mem a = Some 0 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 0.
Proof.
intros W mem a H. apply (cwc_val_mem_of_aval W mem a 1%nat 0).
intros i Hi. destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact H.
Qed.

(* the state the walk starts the turn from *)
Lemma cwc_loop_entry : forall (W : world SEGS) (regsc : bvmap 5 word) memc (sp1 F r k wp pk : Z),
getr regsc 9 = w64 sp1 ->
getr regsc 22 = w64 k -> getr regsc 23 = w64 (SHADOW_OFF + (wp + 16) / 8) ->
getr regsc 24 = w64 (wp + 8 * k) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 40) 8 A_FMT_D ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 48) 8 (F + OFF_LIST) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 56) 8 r ->
val_mem SEGS (mrestrict (w_H W) memc) (wp + 8 * k) 8 pk ->
rdW W memc (SHADOW_OFF + (wp + 8 * k) / 8) = Some 0 ->
alloc_ceiling <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
0 <= wp + 8 * k -> wp + 8 * k + 8 <= alloc_ceiling -> amem_range (wp + 8 * k) 8 ->
0 <= r <= 64 -> 0 <= F -> F + OFF_LIST <= alloc_ceiling -> 0 <= pk < 2 ^ 64 -> 2 <= k <= 64 ->
st_ok_pi SEGS VAL (cwc_lE regsc F r k wp pk) ss_cwc_loop
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 F r k wp pk R9 R22 R23 R24 V40 V48 V56 VW VSH
Hsp1 Hsp1h Hw0 Hwc Hwm Hr HF0 HFc Hpk Hk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (Hdiv : 0 <= (wp + 8 * k) / 8) by (apply Z.div_pos; lia).
assert (Hdiv2 : (wp + 8 * k) / 8 <= 17592185000000) by (apply Z.div_le_upper_bound; lia).
assert (Hd16 : (wp + 16) / 8 = (wp + 8 * k) / 8 + 2 - k)
by (pose proof (cwc_sh_index wp k); lia).
set (S36 := SHADOW_OFF + (wp + 16) / 8 + k) in *.
assert (HS36 : S36 = SHADOW_OFF + (wp + 8 * k) / 8 + 2) by (unfold S36; lia).
assert (HS36r : SHADOW_OFF <= S36 /\ S36 + 8 <= 2 ^ 47) by (unfold SHADOW_OFF in *; lia).
rewrite restrict_mkst_fx.
set (E := cwc_lE regsc F r k wp pk) in *.
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew E n = getr regsc rr)
by (intros n rr Hn Hrr; unfold E, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (cwc_lx F r k wp pk) (Z_to_bv 64 0))
by (intros j Hj; unfold E, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth cwc_lx map] in E33, E34, E35, E36, E37.
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 22%nat 22%bv ltac:(lia) eq_refl) as Ea22.
pose proof (EN 23%nat 23%bv ltac:(lia) eq_refl) as Ea23.
pose proof (EN 24%nat 24%bv ltac:(lia) eq_refl) as Ea24.
assert (U9 : bv_unsigned (ew E 9) = sp1)
by (rewrite Ea9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = wp + 8 * k)
by (rewrite Ea24, R24; unfold w64; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = S36)
by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
unfold ss_cwc_loop. apply pa_entry_st_ok_full.
- unfold E, cwc_lE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cwc_spillR, cwc_shR, cwc_wordR.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 33 0) A_FMT_D);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold A_FMT_D; lia | cbn; lia | exact V40].
    * apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 34 0) (F + OFF_LIST));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFF_LIST in *; lia | cbn; lia | exact V48].
    * apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 35 0) r);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V56].
  + cbn [base_val]. rewrite U36. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ S36 (-2) 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    replace (S36 + -2) with (SHADOW_OFF + (wp + 8 * k) / 8) by lia.
    exact (cwc_vm1 W memc _ VSH).
  + cbn [base_val]. rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (wp + 8 * k) 0 8 (SOff 37 0) pk);
    [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact VW.
- apply pairwise_disjoint_of_extents.
  unfold cwc_spillR, cwc_shR, cwc_wordR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold amem_range in Hwm. unfold SHADOW_OFF in *.
  repeat split; lia.
- split; [exact I|]. split; [exact I|].
  cbn [cwc_lfacts f_alias alias_ok]. split; [|exact I].
  assert (A23 : U E (SOff 23 0) = SHADOW_OFF + (wp + 16) / 8)
  by (apply (U_atom E 23); [rewrite Ea23; exact R23 | unfold SHADOW_OFF in *; lia]).
  assert (A22 : U E (SOff 22 0) = k) by (apply (U_atom E 22); [rewrite Ea22; exact R22 | lia]).
  assert (A36 : U E (SOff 36 0) = S36)
  by (apply (U_atom E 36); [exact E36 | unfold SHADOW_OFF in *; lia]).
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite A23, A22, A36.
  apply zcanon_id. unfold M64. unfold SHADOW_OFF in *. lia.
Qed.

(* --- what a call keeps --- *)

Lemma cwc_mb_kept : forall (W : world SEGS) (m m' : word -> option byte) a,
rdW W m' a = rdW W m a -> mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
intros W m m' a E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W) m') a) as [b'|], (mbyte SEGS (mrestrict (w_H W) m) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma cwc_vm_kept : forall (W : world SEGS) (m m' : word -> option byte) a (n : nat) v,
(forall b, a <= b < a + Z.of_nat n -> rdW W m' b = rdW W m b) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv i Hi.
rewrite (cwc_mb_kept W m m' (a + Z.of_nat i) (HK (a + Z.of_nat i) ltac:(lia))). exact (Hv i Hi).
Qed.

Lemma cwc_region_kept : forall E (W : world SEGS) m m' (rg : YP09.region),
(forall a, base_val E (YP09.r_base rg) + YP09.r_lo rg <= a < base_val E (YP09.r_base rg) + YP09.r_hi rg ->
   rdW W m' a = rdW W m a) ->
YP09.r_whi rg <= YP09.r_wlo rg ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m') rg.
Proof.
intros E W m m' rg HK Hro. split; intros a Ha; [|lia].
exact (cwc_mb_kept W m m' a (HK a Ha)).
Qed.

(* a C string across a call: the bytes of the string proper must be outside the call's written set, and
   the bytes after it, which musl's word-at-a-time loops touch, need only stay readable *)
Lemma cwc_strk_keptX : forall (W : world SEGS) m m' (X : Z -> Prop) p x,
(forall a, 0 <= a < alloc_ceiling -> ~ X a -> rdW W m' a = rdW W m a) ->
(forall a, 0 <= a < alloc_ceiling -> rdW W m a <> None -> rdW W m' a <> None) ->
(forall a, p <= a < p + astr_len x + 1 -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
cwc_strk W m p x -> cwc_strk W m' p x.
Proof.
intros W m m' X p x HK HP HX HXs (Hp & Hs & Hrd & Ht).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
pose proof Hrd as (R0 & R1 & R2 & R3 & R4 & R5 & R6).
assert (Hl : 0 <= astr_len x) by (unfold astr_len; lia).
split; [exact Hp|]. split; [|split].
- destruct Hs as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi. unfold astr_len in *.
  rewrite (HK (p + Z.of_nat i) ltac:(lia) ltac:(apply HX; lia)).
  exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
- split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split.
  { intros a Ha. rewrite (HK a ltac:(lia) ltac:(apply HX; lia)). exact (R3 a Ha). }
  split; [exact R4|]. split.
  + intros y Hy. destruct (R5 y Hy) as (s & Hs' & Hok). exists s. split; [|exact Hok].
    assert (Hy2 : 0 <= y < alloc_ceiling) by lia.
    unfold shadow_of_addr in *. pose proof (cwc_shadow_band y Hy2) as (B1 & B2 & _).
    rewrite (HK (SHADOW_OFF + y / 8) ltac:(unfold SHADOW_OFF in *; lia) ltac:(apply HXs; lia)). exact Hs'.
  + intros Hn s Hs'. pose proof (R6 Hn s Hs') as Hv. unfold shadow_addr in Hs'.
    assert (Hp2 : 0 <= p < alloc_ceiling) by lia.
    assert (Hp3 : 0 <= p + (astr_len x + 1) - 1 < alloc_ceiling) by lia.
    pose proof (cwc_shadow_band p Hp2) as (B1 & B2 & B3 & B4).
    pose proof (cwc_shadow_band (p + (astr_len x + 1) - 1) Hp3) as (D1 & D2 & D3 & D4).
    assert (Hs0 : SHADOW_OFF <= s < kHighShadowEnd) by lia.
    rewrite (HK s ltac:(unfold SHADOW_OFF in *; lia) (HXs s Hs0)). exact Hv.
- intros a Ha. pose proof (Z.mod_pos_bound (p + astr_len x) 8 ltac:(lia)).
  assert (Htb : 0 <= p + astr_len x < alloc_ceiling) by lia.
  pose proof (tail_below (p + astr_len x) _ Htb CE2).
  apply (HP a ltac:(lia)). exact (Ht a Ha).
Qed.

Lemma cwc_abytes_app : forall (W : world SEGS) m a l1 l2,
abytes_at SEGS W m a l1 -> abytes_at SEGS W m (a + Z.of_nat (length l1)) l2 ->
abytes_at SEGS W m a (l1 ++ l2).
Proof.
intros W m a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 i Hlt).
- rewrite app_nth2 by exact Hge.
  pose proof (H2 (i - length l1)%nat ltac:(lia)) as H2'.
  replace (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) with (a + Z.of_nat i) in H2' by lia.
  exact H2'.
Qed.

(* the stage boundary across a call *)
Lemma cwc_mid_keptX : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md S2 memc mdc memc' mdc'
  (fpos sp1 cp r : Z) (X : Z -> Prop),
cwc_mid B ly S W regs mem md S2 memc mdc fpos sp1 cp r ->
ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X a -> rdW W memc' a = rdW W memc a) ->
(forall a, spZ regs - 104 <= a < spZ regs -> ~ X a) ->
(forall a, sp1 <= a < sp1 + 64 -> ~ X a) ->
(forall a, frame_addr ly CWC_CID fpos + 1016 <= a < frame_addr ly CWC_CID fpos + 1024 -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
0 <= spZ regs - 104 -> spZ regs < 2 ^ 64 -> 0 <= sp1 -> sp1 + 64 < 2 ^ 64 ->
0 <= frame_addr ly CWC_CID fpos -> frame_addr ly CWC_CID fpos + 1024 <= alloc_ceiling ->
cwc_mid B ly S W regs mem md S2 memc' mdc' fpos sp1 cp r.
Proof.
intros ly S W regs mem md S2 memc mdc memc' mdc' fpos sp1 cp r X
(HJ0 & HAB & HSP & HFR & HSP2 & HFW & HFSH) HJ HK Hsv Hsl Hfl Hb Hs0 Hs1 Hs2 Hs3 Hf0 Hf1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (HFd : 0 <= frame_addr ly CWC_CID fpos / 8 <= 17592185000000).
{ split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
split; [exact HJ|]. split; [exact HAB|]. split; [exact HSP|]. split.
{ intros j rr Hj. assert (Hjl : (j < length cwc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbv [cwc_saved length] in Hjl.
  apply (cwc_vm_kept W memc memc'); [|exact (HFR j rr Hj)].
  intros b Hb2. apply HK; [lia | apply Hsv; lia]. }
split.
{ destruct HSP2 as (P0 & P1 & P2 & P3 & P4 & P5 & P6).
  repeat split;
  (apply (cwc_vm_kept W memc memc'); [intros b Hb2; apply HK; [lia | apply Hsl; lia] |]);
  first [exact P0 | exact P1 | exact P2 | exact P3 | exact P4 | exact P5 | exact P6]. }
split.
{ rewrite (rdword_ext (rdW W memc) (rdW W memc') (frame_addr ly CWC_CID fpos + 1016)); [exact HFW|].
  intros i Hi. apply HK; [lia | apply Hfl; lia]. }
{ destruct HFSH as (Z1 & Z2 & Z3 & Z4).
  assert (HKs : forall i, 0 <= i <= 119 ->
    rdW W memc' (SHADOW_OFF + frame_addr ly CWC_CID fpos / 8 + i)
    = rdW W memc (SHADOW_OFF + frame_addr ly CWC_CID fpos / 8 + i)).
  { intros i Hi. apply HK; [unfold SHADOW_OFF in *; lia|].
    apply Hb. unfold SHADOW_OFF in *. lia. }
  split; [|split; [|split]].
  - intros i Hi. rewrite (HKs i ltac:(lia)). exact (Z1 i Hi).
  - rewrite (HKs 100 ltac:(lia)). exact Z2.
  - rewrite (HKs 118 ltac:(lia)). exact Z3.
  - rewrite (HKs 119 ltac:(lia)). exact Z4. }
Qed.


(* a string in a live block lies outside the errno cell and outside the frame *)
Lemma cwc_arg_apart : forall ly S (W : world SEGS) mem S2 (W' : world SEGS) memc mdc fpos p x a,
AR SEGS B ly S2 W' memc mdc -> ablocks B ly S2 = ablocks B ly S -> In (CWC_CID, fpos) (frames S2) ->
cwc_sblk B ly S (rdW W mem) p x ->
p <= a < p + astr_len x + 1 ->
~ (as_errno B <= a < as_errno B + 4) /\
~ (frame_addr ly CWC_CID fpos <= a < frame_addr ly CWC_CID fpos + 1024).
Proof.
intros ly S W mem S2 W' memc mdc fpos p x a HAR HAB HIN (Hp0 & Hblk & Hstr) Ha.
pose proof (pal_env B (cr_tl B RLO RHI HR)) as (_ & HEimg & _).
assert (HFB : fs_frame_bytes CWC_CID = 1024) by (vm_compute; reflexivity).
unfold astr_len in Ha.
destruct Hblk as (bb & bn & Hin & Hb1 & Hb2). rewrite <- HAB in Hin.
assert (Hrs : bn <= req_size bn) by (unfold req_size; destruct (Z.eqb_spec bn 0); lia).
split.
- intros He. apply (blk_img _ _ LAWS ly S2 W' memc mdc bb bn a HAR Hin ltac:(lia)). exact (HEimg a He).
- pose proof (sep_block_frame _ _ LAWS ly S2 W' memc mdc bb bn CWC_CID fpos HAR Hin HIN) as Hd.
  rewrite HFB in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma cwc_abytes_prefix : forall (W : world SEGS) m a l1 l2,
abytes_at SEGS W m a (l1 ++ l2) -> abytes_at SEGS W m a l1.
Proof.
intros W m a l1 l2 H i Hi. pose proof (H i ltac:(rewrite length_app; lia)) as Hh.
rewrite app_nth1 in Hh by exact Hi. exact Hh.
Qed.

Lemma cwc_abytes_kept : forall (W : world SEGS) m m' a l,
(forall i, (i < length l)%nat -> rdW W m' (a + Z.of_nat i) = rdW W m (a + Z.of_nat i)) ->
abytes_at SEGS W m a l -> abytes_at SEGS W m' a l.
Proof. intros W m m' a l HK H i Hi. rewrite (HK i Hi). exact (H i Hi). Qed.

(* the metadata bytes that make list usable from its byte o on *)
Lemma cwc_list_ra : forall (rd : reader) F o,
F mod 8 = 0 -> 0 <= F -> 0 <= o <= 768 ->
cwc_fshadow rd F -> range_addressable rd SHADOW_OFF (F + OFF_LIST + o) (LEN_LIST - o).
Proof.
intros rd F o HF8 HF0 Ho (Z1 & Z2 & _ & _) x Hx.
unfold OFF_LIST, LEN_LIST in Hx.
assert (HFe : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (Hxd : x / 8 = F / 8 + (x - F) / 8).
{ replace x with (F / 8 * 8 + (x - F)) at 1 by lia. rewrite Z.div_add_l by lia. reflexivity. }
unfold shadow_of_addr. rewrite Hxd.
destruct (Z_lt_le_dec (x - F) 800) as [Hlt | Hge].
- exists 0. split; [|left; reflexivity].
  assert (Hi : 4 <= (x - F) / 8 < 100)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.add_assoc. exact (Z1 _ Hi).
- assert (Hx8 : x - F = 800) by lia.
  exists 1. rewrite Hx8. change (800 / 8) with 100. split; [rewrite Z.add_assoc; exact Z2|].
  right. split; [|lia]. replace x with ((F / 8 + 100) * 8) by lia. rewrite Z_mod_mult. lia.
Qed.

Lemma cwc_soff0 : forall E n v, ew E n = w64 v -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma cwc_soff : forall E n c v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n c v H H1 H2. rewrite denot_lit_U. try unfold w64. f_equal.
apply (U_atom_off E n v c); [exact H | lia | lia].
Qed.

(* --- the loop --- *)

(* one turn at fx: the next turns (and the tail) run at whatever FP state the snprintf wrapper returns *)
Lemma cwc_turn : forall n : nat, (forall fx0 : YK11.FPState, CWC_LOOP_n (fx := fx0) B RLO RHI n) ->
  CWC_LOOP_n B RLO RHI (Datatypes.S n).
Proof.
intros n IH. unfold CWC_LOOP_n.
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 memc mdc fpos sp1 regsc k
HPRE HMID HFRM HRM0 Hn Hk R2 R3 R4 R8 R9 R18 R20 R22 R23 R24 R26 HSP40 HLIST HWORDS HQ1 HQ2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
pose proof (cr_tl B RLO RHI HR) as TLv.
pose proof (pal_env B TLv) as HAPI.
pose proof HAPI as (HERRr & HERRimg & _).
pose proof HPRE as (HFN & HRO & Ea0 & Ea1 & Ea2 & Hr & HROOK & HOBJ & HGU & HFLB & HERRv &
Hcp1 & Hcp2 & HNAv & HNAr & HPQ1 & HPQ2 & HWSp & HNA3 & HX1 & HX2 & HCNT & HNEV).
pose proof HMID as (HJ & HAB & HSP1 & HFRAME & HSPILL & HFLAGW & HFSH).
pose proof (proj1 HJ) as HAR.
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12496) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HSPz : alloc_ceiling + 12496 <= spZ regs <= 2 ^ 47) by lia.
assert (HINF : In (CWC_CID, fpos) (frames S2))
by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
assert (HFB : fs_frame_bytes CWC_CID = 1024) by (vm_compute; reflexivity).
pose proof (frames_bounds _ _ LAWS ly S2 W memc mdc CWC_CID fpos HAR HINF) as (HF1 & HF2 & HF3).
rewrite HFB in HF2, HF3.
pose proof (frame_al64 _ _ ly S2 W memc mdc CWC_CID fpos HAR HINF) as (HF64 & _ & _).
assert (HF8 : frame_addr ly CWC_CID fpos mod 8 = 0).
{ pose proof (Z.div_mod (frame_addr ly CWC_CID fpos) 64 ltac:(lia)) as D. rewrite HF64 in D.
  rewrite D, Z.add_0_r. replace (64 * (frame_addr ly CWC_CID fpos / 64)) with ((8 * (frame_addr ly CWC_CID fpos / 64)) * 8) by lia.
  apply Z_mod_mult. }
assert (Hsp1m : (spZ regs - 192) mod 16 = 0)
by (replace (spZ regs - 192) with (spZ regs + (-12) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
pose proof (sp1_facts (spZ regs - 192) ltac:(lia) Hsp1m) as (Hs1a & Hs1b & Hs1c).
rewrite <- HSP1 in Hs1a, Hs1b, Hs1c.
assert (Ho16 : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hs1c, Hal16; reflexivity).
set (F := frame_addr ly CWC_CID fpos) in *.
assert (HFdef : F = frame_addr ly CWC_CID fpos) by reflexivity.
set (o := Z.of_nat (length (cwc_T ws k))) in *.
assert (HSW : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31).
{ intros z. unfold bv_swrap. pose proof (bv_wrap_in_range 32 (z + bv_half_modulus 32)) as HW.
  assert (Hm : bv_modulus 32 = 4294967296) by reflexivity.
  assert (Hh : bv_half_modulus 32 = 2147483648) by reflexivity. lia. }
assert (HDEC : forall j, (length (pf_dec (atoi_a (nth j ws []))) <= 11)%nat)
by (intros j; apply pf_dec_len; unfold atoi_a; apply HSW).
assert (HOlen : (length (cwc_T ws k) <= 12 * Z.to_nat (k - 2))%nat)
by (unfold cwc_T; apply chain_items_at_len; exact HDEC).
assert (HO : 0 <= o <= 744) by (unfold o; lia).
(* the word of this turn *)
pose proof (HWORDS k ltac:(lia)) as (HWK & HSK).
pose proof (HWSp k ltac:(lia)) as (HBLK & _ & HARGk).
pose proof HSK as (HPK0 & HSTRk & HRDk & HTLk).
pose proof HRDk as (RD0 & RD1 & RD2 & RD3 & RD4 & RD5 & RD6).
pose proof HWK as (HWK0 & HWK1 & HWK2 & HWK3).
assert (HWAMR : amem_range (wp + 8 * k) 8).
{ destruct HBLK as (bb & bn & Hbin & Hb1 & Hb2).
  rewrite <- HAB in Hbin.
  apply (amem_range_of_block _ _ LAWS ly S2 W memc mdc bb bn (wp + 8 * k) 8 HAR Hbin Hb1).
  unfold req_size. destruct (Z.eqb_spec bn 0); lia. }
(* the state at the head of the loop *)
assert (HS : st_ok_pi SEGS VAL (cwc_lE regsc F r k wp (nth (Z.to_nat k) pw 0)) ss_cwc_loop
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_LOOP)) memc (seg_rom SEGS)))).
{ apply (cwc_loop_entry W regsc memc sp1 F r k wp (nth (Z.to_nat k) pw 0));
  [ exact R9 | exact R22 | exact R23 | exact R24 | exact HSP40
  | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HSPILL))))))
  | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HSPILL))))))
  | exact (cwc_val_mem_of_aval W memc _ _ _ HWK2) | exact HWK3
  | lia | lia | exact HWK0 | exact HWK1 | exact HWAMR | lia | lia | unfold OFF_LIST; lia
  | unfold astr_len in RD1; lia | lia ]. }
set (E0 := cwc_lE regsc F r k wp (nth (Z.to_nat k) pw 0)) in *.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, cwc_lE; apply Eimg_env).
assert (EN0 : forall (m : nat) (rr : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned rr ->
ew E0 m = getr regsc rr)
by (intros m rr Hm Hrr; unfold E0, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX0 : forall j, (j < 6)%nat -> ew E0 (32 + j) = nth j (cwc_lx F r k wp (nth (Z.to_nat k) pw 0)) (Z_to_bv 64 0))
by (intros j Hj; unfold E0, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (G2 : ew E0 2 = w64 sp1) by (rewrite (EN0 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
assert (G3 : ew E0 3 = w64 (as_gp B)) by (rewrite (EN0 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
assert (G4 : ew E0 4 = w64 (as_tp B)) by (rewrite (EN0 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
assert (G8 : ew E0 8 = w64 (spZ regs)) by (rewrite (EN0 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
assert (G9 : ew E0 9 = w64 sp1) by (rewrite (EN0 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
assert (G18 : ew E0 18 = w64 A_FMT_SPD) by (rewrite (EN0 18%nat 18%bv ltac:(lia) eq_refl); exact R18).
assert (G20 : ew E0 20 = w64 (SHADOW_OFF + F / 8)) by (rewrite (EN0 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
assert (G22 : ew E0 22 = w64 k) by (rewrite (EN0 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
assert (G23 : ew E0 23 = w64 (SHADOW_OFF + (wp + 16) / 8)) by (rewrite (EN0 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
assert (G24 : ew E0 24 = w64 (wp + 8 * k)) by (rewrite (EN0 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
assert (G26 : ew E0 26 = w64 o) by (rewrite (EN0 26%nat 26%bv ltac:(lia) eq_refl); exact R26).
assert (G33 : ew E0 33 = w64 A_FMT_D) by exact (EX0 1%nat ltac:(lia)).
assert (G34 : ew E0 34 = w64 (F + OFF_LIST)) by exact (EX0 2%nat ltac:(lia)).
assert (G35 : ew E0 35 = w64 r) by exact (EX0 3%nat ltac:(lia)).
assert (G37 : ew E0 37 = w64 (nth (Z.to_nat k) pw 0)) by exact (EX0 5%nat ltac:(lia)).
assert (SHOK : sh_ok SEGS CWC_Bx (@nil shent) E0 (mrestrict (w_H W) memc)) by constructor.
lazymatch goal with |- SRr _ _ _ ?Qg => set (Qgoal := Qg) end.
(* the rest of the turn, which the two arms of the format choice share *)
assert (BODY : forall (E1 : env) (msb : machine_state) (mdx : Model) (fmtp : Z) (fl : list Z),
  img_env VAL A_LIM E1 ->
  st_ok_pi SEGS VAL E1 ss_cwc_chk (restrict (w_H W) msb) ->
  ms_mem msb = memc ->
  ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W (ms_mem msb) mdx 0 ->
  ew E1 2 = w64 sp1 -> ew E1 3 = w64 (as_gp B) -> ew E1 4 = w64 (as_tp B) ->
  ew E1 8 = w64 (spZ regs) -> ew E1 9 = w64 sp1 -> ew E1 18 = w64 A_FMT_SPD ->
  ew E1 20 = w64 (SHADOW_OFF + F / 8) -> ew E1 22 = w64 k ->
  ew E1 23 = w64 (SHADOW_OFF + (wp + 16) / 8) -> ew E1 24 = w64 (wp + 8 * k) ->
  ew E1 26 = w64 o -> ew E1 33 = w64 A_FMT_D -> ew E1 34 = w64 (F + OFF_LIST) -> ew E1 35 = w64 r ->
  ew E1 37 = w64 (nth (Z.to_nat k) pw 0) -> ew E1 38 = w64 fmtp ->
  (forall mem' md', ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W mem' md' 0 ->
     cwc_strk W mem' fmtp (pf_bytes fl)) ->
  pf_parse fl = Some (ci_ps (Z.to_nat k)) -> (length fl <= 3)%nat ->
  Forall (fun c => 0 <= c < 256) fl -> fmtp + 4 <= RtPFCmd.CMD_IMG_HI ->
  (* the shared snprintf family's literal check (RtPFCmd.fr_lit_ok), computed at each format *)
  (forall v, RtPFCmd.fr_lit_ok fmtp fl (map RtPFCmd.arg_of [AInt v]) = true) ->
  SRr SEGS W (mkCfg msb mdx) Qgoal).
{ intros E1 msb mdx fmtp fl HEI1 HS1 HMb HJ1 N2 N3 N4 N8 N9 N18 N20 N22 N23 N24 N26 N33 N34 N35 N37 N38
    HFMT HPARSE HFLEN HFLBY HFMTI HLIT.
  set (pk := nth (Z.to_nat k) pw 0) in *.
  set (xk := nth (Z.to_nat k) ws []) in *.
  assert (FRNE : forall a, F <= a < F + 1024 -> ~ (as_errno B <= a < as_errno B + 4)).
  { intros a Ha He. apply (frm_img _ _ LAWS ly S2 W memc mdc CWC_CID fpos a HAR HINF);
    [rewrite HFB; rewrite <- HFdef; lia | exact (HERRimg a He)]. }
  assert (SHOK1 : sh_ok SEGS CWC_Bx (@nil shent) E1 (mrestrict (w_H W) (ms_mem msb))) by constructor.
  (* 0x88e84 .. the call of the atoi wrapper; the check of w[k] reads 0 from the region of its metadata byte *)
  paj_run_tok RUN HS1 HJ1 SHOK1 CWC_Bspan; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw1 := mdq) in *; clearbody mdw1 end.
  lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HMc : ms_mem msx = memc)
  by (rewrite <- HMb; exact (frame_of_read_only _ [cwc_spillR; cwc_shR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF));
  rename msx into ms1 end.
  clear_frames.
  pmkst HS1.
  prreg HS1 (1%bv : bv 5) P1.
  rreg_by HS1 (2%bv : bv 5) (w64 sp1) (cwc_soff0 E1 2 sp1 N2) P2.
  rreg_by HS1 (3%bv : bv 5) (w64 (as_gp B)) (cwc_soff0 E1 3 _ N3) Qgp.
  rreg_by HS1 (4%bv : bv 5) (w64 (as_tp B)) (cwc_soff0 E1 4 _ N4) Qtp.
  rreg_by HS1 (10%bv : bv 5) (w64 pk) (cwc_soff0 E1 37 _ N37) Qa0.
  assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)).
  { replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia. unfold spZ. rewrite P2. try unfold w64.
    apply unsigned_lit_small. lia. }
  assert (Qra : YK0s.ret_ok (getr (ms_regs ms1) 1))
  by (rewrite P1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
  rewrite HMc in HJ1 |- *.
  pose proof (cr_rt_cells B RLO RHI HR ly S2 W memc mdw1 (proj1 HJ1)) as (HGU1 & HFLB1 & (ev1 & HERR1)).
  assert (HEP : ecall_pre_stk SEGS B (3 * ESTACK) ly S2 W (ms_regs ms1) memc mdw1).
  { eapply (ecall_pre_stk_at SEGS B (3 * ESTACK) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md
      [(CWC_CID, fpos)] ly S2 W memc mdw1 0 (ms_regs ms1) (sp1 - spZ regs) HJ1 Qsp);
    [ exact Ho16 | lia | lia | lia | exact Qra | exact Qgp | exact Qtp ]. }
  pose proof (cwc_rom_now B RLO RHI CHECK_WORDS_CHAIN_STK (spZ regs) ly S W mem md
    [(CWC_CID, fpos)] ly S2 W memc mdw1 0 HRO HJ1) as ROM1.
  assert (HLIM1 : alloc_ceiling <= spZ (ms_regs ms1) - 3 * ESTACK) by (rewrite Qsp; lia).
  pose proof (cwc_aread_of_rd (3 * ESTACK) W (ms_regs ms1) memc pk (astr_len xk + 1) HRDk HLIM1) as RDk.
  (* the atoi contract's band premise: 8 bytes past the word, which lies in a live block of the entry (PaLibH's
     amem8_of_blockA) *)
  pose proof HARGk as (_ & HBLKk & _).
  pose proof (amem8_of_blockA SEGS B LAWS ly S W mem md pk (astr_len xk) HAR0 HBLKk ltac:(unfold astr_len; lia))
    as HAM8k.
  (* the atoi contract's separation premise: the word lies in a live block of the entry, whose bytes are not image
     bytes (RecBLemmas.v's recb_heap_noimg_m), and the errno cell is (PALib's pal_env, HERRimg) *)
  assert (HSEPk : pk + astr_len xk + 1 <= as_errno B \/ as_errno B + 4 <= pk).
  { destruct (Z_le_gt_dec (pk + astr_len xk + 1) (as_errno B)) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (as_errno B + 4) pk) as [H2|H2]; [right; exact H2|]. exfalso.
    pose proof HBLKk as Hb. unfold in_blockA in Hb. destruct Hb as (b0 & k0 & Hb0 & Hb1 & Hb2).
    assert (Hrq : k0 <= req_size k0)
    by (unfold req_size; destruct (k0 =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia).
    unfold astr_len in *.
    apply (RecBLemmas.recb_heap_noimg_m B ly S W mem md b0 k0 (Z.max pk (as_errno B)) HAR0 Hb0); [lia|].
    apply HERRimg. lia. }
  pose proof (AATOI fx ly S2 W (ms_regs ms1) memc mdw1 pk xk ev1 HFLB1 HGU1 HEP Qa0 HPK0 HSTRk RDk HAM8k HTLk HERR1
    HSEPk ROM1) as HC.
  eapply SRr_bind.
  { exact (aj_art_at SEGS B LAWS Hsegs HAPI (3 * ESTACK) (aerrno_cell B)
      (SIGMA CS___interceptor_trampoline_atoi) W (ms_regs ms1) memc CHECK_WORDS_CHAIN_STK (spZ regs) []
      ly S W mem md [(CWC_CID, fpos)] ly S2 mdw1 0 (sp1 - spZ regs) (getr (ms_regs ms1) 1) _
      HJ1 Qsp Ho16 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl (fun a Ha => Ha) HC). }
  cbv beta. intros W2 c2 _ (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & (HA0 & HERR2) & HKP2).
  subst W2 c2.
  assert (HA0' : getr regs2 10 = w64 (atoi_a xk)) by (unfold atoi_a; exact HA0).
  rewrite P1.
  jafter_call_keep_pi HS1 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. rewrite HMc. repeat apply Forall_cons; try apply Forall_nil.
    apply (cwc_region_kept _ W memc mem2 _); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite N9. try unfold w64. rewrite unsigned_lit_small by lia.
    intros a Ha. apply HKP2; [lia | lia | unfold aerrno_cell; lia]. }
  clear HS1. rewrite <- restrict_mkst_fx in HS2.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ev _ _ => remember Ev as E2 eqn:HE2 in HS2 end.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
  assert (OLD2 : forall m, (m < 40)%nat -> ew E2 m = ew E1 m)
  by (intros m Hm; rewrite HE2; apply ew_havoc_old; lia).
  assert (M44 : ew E2 44 = getr regs2 10)
  by (rewrite HE2; exact (ew_havoc_new E1 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia))).
  assert (SHOK2 : sh_ok SEGS CWC_Bx (@nil shent) E2 (mrestrict (w_H W) mem2)) by constructor.
  (* 0x88ea8 .. the call of the snprintf wrapper *)
  paj_run_tok RUN HS2 HJ2 SHOK2 CWC_Bspan; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw2 := mdq) in *; clearbody mdw2 end.
  lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HMd : ms_mem msx = mem2)
  by (exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
  rename msx into ms2 end.
  clear_frames.
  pmkst HS2.
  assert (PF10 : sv_denot E2 (SAlu ALU_ADD (SOff 26 0) (SOff 34 0)) = w64 (F + OFF_LIST + o)).
  { rewrite denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E2 26 o) by (first [rewrite OLD2 by lia; exact N26 | lia]).
    rewrite (U_atom E2 34 (F + OFF_LIST)) by (first [rewrite OLD2 by lia; exact N34 | unfold OFF_LIST; lia]).
    rewrite zcanon_id by (unfold M64, OFF_LIST; lia). lia. }
  assert (PF11 : sv_denot E2 (SAlu ALU_SUB (SLit 0) (SOff 26 (-769))) = w64 (769 - o)).
  { rewrite denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SLit, U_SOff, OLD2 by lia. rewrite N26. try unfold w64. rewrite unsigned_lit_small by lia.
    unfold zcanon, M64.
    rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
    rewrite <- (Z.mod_add (o + -769) 1 (2 ^ 64)) by lia.
    rewrite (Z.mod_small (o + -769 + 1 * 2 ^ 64) (2 ^ 64)) by lia.
    rewrite <- (Z.mod_add (0 - (o + -769 + 1 * 2 ^ 64)) 1 (2 ^ 64)) by lia.
    rewrite Z.mod_small by lia. lia. }
  prreg HS2 (1%bv : bv 5) P1b.
  rreg_by HS2 (2%bv : bv 5) (w64 sp1) (cwc_soff0 E2 2 sp1 (eq_trans (OLD2 2%nat ltac:(lia)) N2)) P2b.
  rreg_by HS2 (3%bv : bv 5) (w64 (as_gp B)) (cwc_soff0 E2 3 _ (eq_trans (OLD2 3%nat ltac:(lia)) N3)) Qgp2.
  rreg_by HS2 (4%bv : bv 5) (w64 (as_tp B)) (cwc_soff0 E2 4 _ (eq_trans (OLD2 4%nat ltac:(lia)) N4)) Qtp2.
  rreg_by HS2 (10%bv : bv 5) (w64 (F + OFF_LIST + o)) PF10 QD.
  rreg_by HS2 (11%bv : bv 5) (w64 (769 - o)) PF11 QN.
  rreg_by HS2 (12%bv : bv 5) (w64 fmtp) (cwc_soff0 E2 38 _ (eq_trans (OLD2 38%nat ltac:(lia)) N38)) QF.
  rreg_by HS2 (13%bv : bv 5) (w64 (atoi_a xk)) (cwc_soff0 E2 44 _ (eq_trans M44 HA0')) Pa3.
  assert (Qsp2 : spZ (ms_regs ms2) = spZ regs + (sp1 - spZ regs)).
  { replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia. unfold spZ. rewrite P2b. try unfold w64.
    apply unsigned_lit_small. lia. }
  assert (Qra2 : YK0s.ret_ok (getr (ms_regs ms2) 1))
  by (rewrite P1b; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
  rewrite HMd in HJ2 |- *.
  pose proof (cr_rt_cells B RLO RHI HR ly S2 W mem2 mdw2 (proj1 HJ2)) as (HGU2 & _ & _).
  pose proof (HFMT mem2 mdw2 HJ2) as (HFP0 & HFSTR & HFRD & HFTL).
  unfold astr_len in HFRD, HFTL. rewrite pf_bytes_len in HFRD, HFTL.
  assert (HLIM2 : alloc_ceiling <= spZ (ms_regs ms2) - 3 * ESTACK) by (rewrite Qsp2; lia).
  pose proof (cwc_aread_of_rd (3 * ESTACK) W (ms_regs ms2) mem2 fmtp _ HFRD HLIM2) as HFRD2.
  pose proof (cwc_rom_now B RLO RHI CHECK_WORDS_CHAIN_STK (spZ regs) ly S W mem md
    [(CWC_CID, fpos)] ly S2 W mem2 mdw2 0 HRO HJ2) as ROM2.
  (* the metadata of list, kept across the atoi wrapper *)
  assert (HFd : 0 <= F / 8 <= 17592185000000)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FSH2 : cwc_fshadow (rdW W mem2) F).
  { assert (HKs : forall i, 0 <= i <= 119 ->
      rdW W mem2 (SHADOW_OFF + F / 8 + i) = rdW W memc (SHADOW_OFF + F / 8 + i)).
    { intros i Hi. apply HKP2; [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | unfold aerrno_cell, SHADOW_OFF in *; lia]. }
    pose proof HFSH as (Z1 & Z2 & Z3 & Z4). split; [|split; [|split]].
    - intros i Hi. rewrite (HKs i ltac:(lia)). exact (Z1 i Hi).
    - rewrite (HKs 100 ltac:(lia)). exact Z2.
    - rewrite (HKs 118 ltac:(lia)). exact Z3.
    - rewrite (HKs 119 ltac:(lia)). exact Z4. }
  pose proof (pf_text_ci atoi_a (Z.to_nat k) ws) as (_ & HTXT). fold xk in HTXT.
  pose proof (ci_text_len atoi_a (Z.to_nat k) ws (HDEC (Z.to_nat k))) as HTlen.
  assert (HDEST : forall a, F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o) ->
    awr_byte SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] (ablocks B ly S) (ablocks B ly S2) (frames S) ly
      [(CWC_CID, fpos)] a /\ ~ (spZ regs + (sp1 - spZ regs) - 3 * ESTACK <= a < spZ regs + (sp1 - spZ regs))).
  { intros a Ha. unfold OFF_LIST in Ha. split; [|lia].
    unfold awr_byte. right; right; right; left. unfold in_frames. exists CWC_CID, fpos.
    split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HFB, <- HFdef. lia. }
  assert (HPC : forall a, F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o) -> inFP [] a ->
    (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ spZ regs <= a < ly_top ly ->
    writable_at SEGS (mrestrict (w_H W) mem2) a)
  by (intros a _ Hfp; exfalso; exact (inFP_nil a Hfp)).
  assert (HAMR : amem_range (F + OFF_LIST + o) (769 - o + 8))
  by (unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, OFF_LIST in *; lia).
  assert (HRAD : range_addressable (rdW W mem2) SHADOW_OFF (F + OFF_LIST + o) (769 - o)).
  { pose proof (cwc_list_ra (rdW W mem2) F o ltac:(rewrite HFdef; exact HF8) ltac:(lia) ltac:(lia) FSH2) as HL.
    unfold LEN_LIST in HL. exact HL. }
  assert (HHULL : shadow_hull_vis (rdW W mem2) (F + OFF_LIST + o) (769 - o)).
  { apply (shadow_hull_vis_of_frame _ _ LAWS ly S2 W mem2 mdw2 CWC_CID fpos _ _ (proj1 HJ2) HINF);
    rewrite ?HFB, <- ?HFdef; unfold OFF_LIST; lia. }
  (* the shared contract's argument word a3 (argZ 3) *)
  assert (A3 : argZ (ms_regs ms2) 3 = bv_unsigned (getr (ms_regs ms2) 13))
  by (unfold argZ; do 2 f_equal; apply bv_eq; reflexivity).
  assert (HARGS : RtPFShared.pf_args_asan (rdW W mem2)
    (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms2)) (F + OFF_LIST + o)
       (RtPFShared.sn_len (769 - o - 1) (ci_text atoi_a (Z.to_nat k) ws)))
    (map (argZ (ms_regs ms2)) [3; 4; 5; 6; 7]) (map RtPFCmd.arg_of [AInt (atoi_a xk)])).
  { cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan map RtPFCmd.arg_of]. split; [|exact I].
    split; [unfold atoi_a; apply HSW|].
    rewrite A3, Pa3. try unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_eq (atoi_a xk) (2 ^ 64)) by lia.
    replace (atoi_a xk - 2 ^ 64 * (atoi_a xk / 2 ^ 64))
      with (atoi_a xk + (- (2 ^ 32 * (atoi_a xk / 2 ^ 64))) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  (* list lies above the image, and so does the call's window *)
  assert (HDI : RtPFCmd.CMD_IMG_HI <= F + OFF_LIST + o).
  { pose proof (RtPFDog.pa_frame_above_img (PI := PI) B ly S2 W mem2 mdw2 CWC_CID fpos (proj1 HJ2) HINF) as HA.
    unfold OFF_LIST. lia. }
  assert (HWI : RtPFCmd.CMD_IMG_HI <= spZ regs + (sp1 - spZ regs) - 3 * ESTACK) by (unfold RtPFCmd.CMD_IMG_HI; lia).
  (* the read-only ranges the shared contract reads, as the image has them *)
  assert (HROc : arodata_okP SEGS RLO RHI B (rdW W mem2))
  by exact (cwc_arodata_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRO HJ2).
  pose proof (CmdRecImg.cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W mem2 HROc) as HCV. clear HROc.
  pose proof (nz_bytes _ (ci_text_nz atoi_a (Z.to_nat k) ws)) as HTB.
  assert (HPREC : RtPFShared.pf_prec_pos (map RtPFCmd.piece_of (ci_ps (Z.to_nat k)))
    (map RtPFCmd.arg_of [AInt (atoi_a xk)])) by (unfold ci_ps; destruct (Nat.eqb (Z.to_nat k) 2); exact I).
  eapply SRr_bind.
  { exact (cwc_aj_snprintf_atSF SEGS B LAWS Hsegs (SIGMA CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8
      (ASNPRINTF fx)
      W (ms_regs ms2) mem2 CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 mdw2 0
      (F + OFF_LIST + o) (769 - o) fmtp fl (ci_ps (Z.to_nat k)) [AInt (atoi_a xk)] (ci_text atoi_a (Z.to_nat k) ws)
      (sp1 - spZ regs) (getr (ms_regs ms2) 1)
      HJ2 QD QN QF ltac:(lia) ltac:(unfold OFF_LIST; lia) HFP0 ltac:(unfold OFF_LIST; lia) Qsp2 Ho16
      ltac:(lia) ltac:(lia) Qgp2 Qtp2 eq_refl Qra2
      HDEST HPC HAMR HRAD HHULL HDI HWI HGU2 ltac:(lia) ltac:(unfold RtPFCmd.CMD_IMG_HI; lia) ltac:(lia)
      ltac:(unfold RtPFCmd.CMD_IMG_HI; lia) HFSTR HFLBY ltac:(lia) HPARSE HTXT HPREC HTB ltac:(lia) HFRD2 HARGS HCV
      (HLIT (atoi_a xk)) HRM0). }
  cbv beta. intros W3 c3 _ (HW3 & fx1 & regs3 & mem3 & md3 & Hfx & Hc3 & HJ3 & HP3 & HR3 & HB3 & HKP3 & HPR3 & _).
  subst W3 c3.
  rewrite P1b.
  (* the rest of the turn runs at the FP state fx1 the wrapper returned; its post at fx1 is the turn's at fx *)
  unfold Qgoal, cwc_post. apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
  pose proof (fxrel_frm0 fx fx1 HRM0 Hfx) as HRM1.
  pose proof (paj_run (fx := fx1) B LAWS) as RUN1. pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
  pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
  jafter_call_keep_pi HS2 60%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. rewrite HMd. repeat apply Forall_cons; try apply Forall_nil.
    apply (cwc_region_kept _ W mem2 mem3 _); [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite OLD2 by lia. rewrite N9. try unfold w64.
    rewrite unsigned_lit_small by lia.
    intros a Ha. apply HKP3; [lia | unfold OFF_LIST; lia | lia]. }
  clear HS2. rewrite <- (restrict_mkst_fx (fx := fx)) in HS3. apply (st_ok_pi_restrict_xfx fx fx1) in HS3.
  lazymatch type of HS3 with st_ok_pi _ _ ?Ev _ _ => remember Ev as E3 eqn:HE3 in HS3 end.
  assert (HEIx3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
  assert (OLD3 : forall m, (m < 40)%nat -> ew E3 m = ew E1 m)
  by (intros m Hm; rewrite HE3, ew_havoc_old by lia; apply OLD2; lia).
  assert (M64a : ew E3 64 = getr regs3 10)
  by (rewrite HE3; exact (ew_havoc_new E2 60 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia))).
  assert (SHOK3 : sh_ok SEGS CWC_Bx (@nil shent) E3 (mrestrict (w_H W) mem3)) by constructor.
  (* 0x88ebc .. the back edge *)
  paj_run_tok RUN1 HS3 HJ3 SHOK3 CWC_Bspan; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw3 := mdq) in *; clearbody mdw3 end.
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HMe : ms_mem msx = mem3)
  by (exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  (* what the two calls kept *)
  set (XA := fun a => (sp1 - 3 * ESTACK <= a < sp1) \/ (as_errno B <= a < as_errno B + 4) \/
    (F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o))).
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ XA a -> rdW W mem3 a = rdW W memc a).
  { intros a Ha Hx. unfold XA in Hx.
    rewrite (HKP3 a Ha ltac:(intros H; apply Hx; right; right; exact H) ltac:(intros H; apply Hx; left; lia)).
    apply (HKP2 a Ha); [intros H; apply Hx; left; lia | intros H; apply Hx; right; left; exact H]. }
  assert (KBEL : forall a, 0 <= a < alloc_ceiling -> ~ XA a -> rdW W mem3 a = rdW W memc a)
  by (intros a Ha Hx; apply KALL; [lia | exact Hx]).
  assert (PALL : forall a, 0 <= a < alloc_ceiling -> rdW W memc a <> None -> rdW W mem3 a <> None).
  { intros a Ha Hv.
    assert (Hd1 : (as_errno B <= a < as_errno B + 4) \/ ~ (as_errno B <= a < as_errno B + 4)) by lia.
    assert (Hd2 : (F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o)) \/
      ~ (F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o))) by lia.
    destruct Hd1 as [He | He].
    - assert (Hnf : ~ (F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o)))
      by (intros Hf; apply (FRNE a ltac:(unfold OFF_LIST in *; lia)); exact He).
      rewrite (HKP3 a ltac:(lia) Hnf ltac:(lia)).
      pose proof (HERR2 (Z.to_nat (a - as_errno B)) ltac:(lia)) as HE2a.
      replace (as_errno B + Z.of_nat (Z.to_nat (a - as_errno B))) with a in HE2a by lia.
      rewrite HE2a. discriminate.
    - destruct Hd2 as [Hf | Hf].
      + assert (Hni : ~ in_img SEGS a)
        by (apply (frm_img _ _ LAWS ly S2 W memc mdc CWC_CID fpos a HAR HINF); rewrite HFB, <- HFdef; unfold OFF_LIST in *; lia).
        assert (Hv2 : rdW W mem2 a <> None) by (rewrite (HKP2 a ltac:(lia) ltac:(lia) He); exact Hv).
        apply (aview_some_of_apresent SEGS). apply HPR3. exact (apresent_of_aview SEGS _ _ a ltac:(lia) Hni Hv2).
      + rewrite (KALL a ltac:(lia) ltac:(unfold XA; intros [H|[H|H]]; [lia | exact (He H) | exact (Hf H)])).
        exact Hv. }
  assert (XBAND : forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ XA s).
  { intros s Hs [H|[H|H]]; [lia | unfold SHADOW_OFF in *; lia |].
    unfold in_app, kLowShadowBeg, ASAN_CEIL, OFF_LIST, SHADOW_OFF in *. lia. }
  (* the strings and the word slots the next turns read *)
  assert (STRK : forall p x, cwc_sblk B ly S (rdW W mem) p x ->
    cwc_strk W memc p x -> cwc_strk W mem3 p x).
  { intros p x HA HSx. apply (cwc_strk_keptX W memc mem3 XA p x KBEL PALL); [|exact XBAND | exact HSx].
    intros a Ha Hx. pose proof HSx as (_ & _ & (_ & HR1 & _) & _).
    destruct (cwc_arg_apart ly S W mem S2 W memc mdc fpos p x a HAR HAB HINF HA Ha) as (Hne & Hnf).
    rewrite <- HFdef in Hnf. unfold XA in Hx. destruct Hx as [H|[H|H]]; [lia | exact (Hne H) | ].
    apply Hnf. unfold OFF_LIST in *. lia. }
  assert (HWORDS' : forall j, k + 1 <= j < r ->
     cwc_wordk W mem3 wp j (nth (Z.to_nat j) pw 0) /\
     cwc_strk W mem3 (nth (Z.to_nat j) pw 0) (nth (Z.to_nat j) ws [])).
  { intros j Hj. destruct (HWORDS j ltac:(lia)) as (HWj & HSj).
    destruct (HWSp j ltac:(lia)) as (HBj & _ & HAj).
    split; [|exact (STRK _ _ HAj HSj)].
    apply (cwc_wordk_kept W memc mem3 XA wp j _ KBEL); [|exact XBAND | exact HWj].
    intros a Ha Hx. destruct HBj as (bb & bn & Hbin & Hb1 & Hb2). rewrite <- HAB in Hbin.
    assert (Hrs : bn <= req_size bn) by (unfold req_size; destruct (Z.eqb_spec bn 0); lia).
    pose proof HWj as (HWj0 & HWj1 & _).
    unfold XA in Hx. destruct Hx as [H|[H|H]]; [lia | |].
    + apply (blk_img _ _ LAWS ly S2 W memc mdc bb bn a HAR Hbin ltac:(lia)). exact (HERRimg a H).
    + pose proof (sep_block_frame _ _ LAWS ly S2 W memc mdc bb bn CWC_CID fpos HAR Hbin HINF) as Hd.
      rewrite HFB, <- HFdef in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold OFF_LIST in *. lia. }
  pose proof (HPQ1 HNA3) as (_ & HA1). pose proof (HPQ2 HNA3) as (_ & HA2).
  pose proof (STRK p1 x1 HA1 HQ1) as HQ1'. pose proof (STRK p2 x2 HA2 HQ2) as HQ2'.
  assert (HSP40' : val_mem SEGS (mrestrict (w_H W) mem3) (sp1 + 40) 8 A_FMT_D).
  { apply (cwc_vm_kept W memc mem3); [|exact HSP40].
    intros b Hb. apply KALL; [lia|]. unfold XA. intros [H|[H|H]]; unfold OFF_LIST in *; lia. }
  assert (HTk1 : cwc_T ws (k + 1) = cwc_T ws k ++ ci_text atoi_a (Z.to_nat k) ws).
  { unfold cwc_T. replace (Z.to_nat (k + 1 - 2)) with (Datatypes.S (Z.to_nat (k - 2))) by lia.
    rewrite chain_items_at_snoc. do 2 f_equal. lia. }
  assert (HLIST' : abytes_at SEGS W mem3 (F + OFF_LIST) (pf_bytes (cwc_T ws (k + 1) ++ [0]))).
  { rewrite HTk1, <- app_assoc, pf_bytes_app.
    apply cwc_abytes_app.
    - apply (cwc_abytes_kept W memc mem3).
      + intros i Hi. rewrite pf_bytes_len in Hi. apply KALL; [unfold o, OFF_LIST in *; lia|]. unfold XA.
        intros [H|[H|H]]; [unfold o, OFF_LIST in *; lia
          | apply (FRNE (F + OFF_LIST + Z.of_nat i)); [unfold o, OFF_LIST in *; lia | exact H]
          | unfold o, OFF_LIST in *; lia].
      + rewrite pf_bytes_nul in HLIST. exact (cwc_abytes_prefix W memc _ _ _ HLIST).
    - rewrite pf_bytes_len. fold o.
      rewrite (firstn_all_text (ci_text atoi_a (Z.to_nat k) ws) (769 - o)) in HB3 by lia.
      exact HB3. }
  assert (HO1 : Z.of_nat (length (cwc_T ws (k + 1))) = o + Z.of_nat (length (ci_text atoi_a (Z.to_nat k) ws)))
  by (rewrite HTk1, length_app; unfold o; lia).
  pose proof HJ3 as HJ3m. rewrite HMe in HJ3m.
  assert (HMID3 : cwc_mid B ly S W regs mem md S2 mem3 mdw3 fpos sp1 cp r).
  { apply (cwc_mid_keptX ly S W regs mem md S2 memc mdc mem3 mdw3 fpos sp1 cp r XA HMID HJ3m KALL);
    rewrite <- ?HFdef; try unfold XA.
    - intros a Ha [H|[H|H]]; unfold OFF_LIST in *; lia.
    - intros a Ha [H|[H|H]]; unfold OFF_LIST in *; lia.
    - intros a Ha [H|[H|H]]; [lia | apply (FRNE a ltac:(lia)); exact H | unfold OFF_LIST in *; lia].
    - exact XBAND.
    - lia. - lia. - lia. - lia. - lia. - lia. }
  psrr_branch_tok RUN1 BR1 HS3 SHOK3 CWC_Bspan.
  + (* r <> k + 1: the next turn *)
    rewrite branch_ne_U, (U_atom E3 35 r ltac:(rewrite OLD3 by lia; exact N35) ltac:(lia)),
      (U_atom_off E3 22 k 1 ltac:(rewrite OLD3 by lia; exact N22) ltac:(lia) ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hk1 : k + 1 < r) by lia.
    paj_run_to_tok RUNTO1 HS3 HJ3 SHOK3 CWC_Bspan CWC_LOOP; [awr_ok_tac|].
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdw4 := mdq) in *; clearbody mdw4 end.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMf : ms_mem msx = mem3)
    by (rewrite <- HMe; exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms4 end.
    clear_frames.
    pmkst HS3.
    rreg_by HS3 (2%bv : bv 5) (w64 sp1) (cwc_soff0 E3 2 _ (eq_trans (OLD3 2%nat ltac:(lia)) N2)) T2.
    rreg_by HS3 (3%bv : bv 5) (w64 (as_gp B)) (cwc_soff0 E3 3 _ (eq_trans (OLD3 3%nat ltac:(lia)) N3)) T3.
    rreg_by HS3 (4%bv : bv 5) (w64 (as_tp B)) (cwc_soff0 E3 4 _ (eq_trans (OLD3 4%nat ltac:(lia)) N4)) T4.
    rreg_by HS3 (8%bv : bv 5) (w64 (spZ regs)) (cwc_soff0 E3 8 _ (eq_trans (OLD3 8%nat ltac:(lia)) N8)) T8.
    rreg_by HS3 (9%bv : bv 5) (w64 sp1) (cwc_soff0 E3 9 _ (eq_trans (OLD3 9%nat ltac:(lia)) N9)) T9.
    rreg_by HS3 (18%bv : bv 5) (w64 A_FMT_SPD) (cwc_soff0 E3 18 _ (eq_trans (OLD3 18%nat ltac:(lia)) N18)) T18.
    rreg_by HS3 (20%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) (cwc_soff0 E3 20 _ (eq_trans (OLD3 20%nat ltac:(lia)) N20)) T20.
    rreg_by HS3 (22%bv : bv 5) (w64 (k + 1))
      (cwc_soff E3 22 1 k (eq_trans (OLD3 22%nat ltac:(lia)) N22) ltac:(lia) ltac:(lia)) T22.
    rreg_by HS3 (23%bv : bv 5) (w64 (SHADOW_OFF + (wp + 16) / 8))
      (cwc_soff0 E3 23 _ (eq_trans (OLD3 23%nat ltac:(lia)) N23)) T23.
    rreg_by HS3 (24%bv : bv 5) (w64 (wp + 8 * k + 8))
      (cwc_soff E3 24 8 (wp + 8 * k) (eq_trans (OLD3 24%nat ltac:(lia)) N24) ltac:(lia) ltac:(lia)) T24.
    assert (PF26 : sv_denot E3 (SAlu ALU_ADD (SOff 26 0) (SOff 64 0))
      = w64 (Z.of_nat (length (cwc_T ws (k + 1))))).
    { rewrite HO1, denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E3 26 o) by (first [rewrite OLD3 by lia; exact N26 | lia]).
      rewrite (U_atom E3 64 (Z.of_nat (length (ci_text atoi_a (Z.to_nat k) ws))))
        by (first [rewrite M64a; exact HR3 | lia]).
      rewrite zcanon_id by (unfold M64; lia). lia. }
    rreg_by HS3 (26%bv : bv 5) (w64 (Z.of_nat (length (cwc_T ws (k + 1))))) PF26 T26.
    rewrite HMf.
    apply (IH fx1 ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 mem3 mdw4 fpos sp1 (ms_regs ms4) (k + 1));
    first [ exact HPRE | exact HFRM | lia | assumption
          | (rewrite T24; f_equal; lia)
          | (rewrite <- HMf; exact HMID3)
          | (rewrite HMf in HJ3; destruct HMID3 as (_ & HM3r); split; [exact HJ3 | exact HM3r])
          | (intros j Hj; exact (HWORDS' j Hj)) ].
  + (* r = k + 1: the tail *)
    rewrite branch_ne_U, (U_atom E3 35 r ltac:(rewrite OLD3 by lia; exact N35) ltac:(lia)),
      (U_atom_off E3 22 k 1 ltac:(rewrite OLD3 by lia; exact N22) ltac:(lia) ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hk1 : r = k + 1) by lia.
    paj_run_to_tok RUNTO1 HS3 HJ3 SHOK3 CWC_Bspan CWC_TAIL; [awr_ok_tac|].
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdw4 := mdq) in *; clearbody mdw4 end.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMf : ms_mem msx = mem3)
    by (rewrite <- HMe; exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms4 end.
    clear_frames.
    pmkst HS3.
    rreg_by HS3 (2%bv : bv 5) (w64 sp1) (cwc_soff0 E3 2 _ (eq_trans (OLD3 2%nat ltac:(lia)) N2)) T2.
    rreg_by HS3 (3%bv : bv 5) (w64 (as_gp B)) (cwc_soff0 E3 3 _ (eq_trans (OLD3 3%nat ltac:(lia)) N3)) T3.
    rreg_by HS3 (4%bv : bv 5) (w64 (as_tp B)) (cwc_soff0 E3 4 _ (eq_trans (OLD3 4%nat ltac:(lia)) N4)) T4.
    rreg_by HS3 (8%bv : bv 5) (w64 (spZ regs)) (cwc_soff0 E3 8 _ (eq_trans (OLD3 8%nat ltac:(lia)) N8)) T8.
    rreg_by HS3 (9%bv : bv 5) (w64 sp1) (cwc_soff0 E3 9 _ (eq_trans (OLD3 9%nat ltac:(lia)) N9)) T9.
    rreg_by HS3 (20%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) (cwc_soff0 E3 20 _ (eq_trans (OLD3 20%nat ltac:(lia)) N20)) T20.
    rewrite HMf.
    assert (HLISTr : abytes_at SEGS W mem3 (F + OFF_LIST) (pf_bytes (chain_list_at atoi_a r ws ++ [0]))).
    { unfold chain_list_at. replace r with (k + 1) by lia. exact HLIST'. }
    apply (TAIL fx1 ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 mem3 mdw4 fpos sp1 (ms_regs ms4));
    first [ exact HPRE | exact HFRM | assumption
          | (rewrite HMf in HJ3; destruct HMID3 as (_ & HM3r); split; [exact HJ3 | exact HM3r]) ]. }
(* 0x88e74 .. the compare of k with 2 *)
paj_run_tok RUN HS HJ SHOK CWC_Bspan; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
set (mdv1 := mdq) in *; clearbody mdv1 end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
assert (HM1 : ms_mem msx = memc)
by (exact (frame_of_read_only _ [cwc_spillR; cwc_shR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
clear_frames.
psrr_branch_tok RUN BR HS SHOK CWC_Bspan.
- (* 2 < k: the format stays " %d" *)
  paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan CWC_CHK; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HM2 : ms_mem msx = memc)
  by (rewrite <- HM1; exact (frame_of_read_only _ [cwc_spillR; cwc_shR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  rewrite branch_ltu_U, (U_lit E0 2 ltac:(lia)),
    (U_atom E0 22 k G22 ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  prreg HS (25%bv : bv 5) Q25.
  add_atom HS 38%nat (w64 A_FMT_SPD) E38.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (25%bv : bv 5) (SOff 38 0) HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact (eq_trans Q25 G18))) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (@nil (nat * afact)) (@nil acond)
      [(SAlu ALU_ADD (SOff 23 0) (SOff 22 0), SOff 36 0)] HS
      ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx) ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = ss_cwc_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
    apply (BODY Ev msx mdv2 A_FMT_SPD [32; 37; 100]) end;
  first [ assumption
        | exact E38
        | (rewrite ew_havoc_old by lia; assumption)
        | (intros mem' md' HJx; exact (proj2 (cwc_fmt_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HROOK HRO HJx)))
        | (unfold ci_ps; destruct (Nat.eqb_spec (Z.to_nat k) 2); [lia | reflexivity])
        | (cbn; lia)
        | (repeat constructor; lia)
        | (unfold RtPFCmd.CMD_IMG_HI, A_FMT_SPD, A_FMT_D; lia)
        | (intros ?; reflexivity) ].
- (* k = 2: the format is the word at sp1 + 40, "%d" *)
  paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan CWC_CHK; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HM2 : ms_mem msx = memc)
  by (rewrite <- HM1; exact (frame_of_read_only _ [cwc_spillR; cwc_shR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  rewrite branch_ltu_U, (U_lit E0 2 ltac:(lia)),
    (U_atom E0 22 k G22 ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  prreg HS (25%bv : bv 5) Q25.
  add_atom HS 38%nat (w64 A_FMT_D) E38.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (25%bv : bv 5) (SOff 38 0) HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact (eq_trans Q25 G33))) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (@nil (nat * afact)) (@nil acond)
      [(SAlu ALU_ADD (SOff 23 0) (SOff 22 0), SOff 36 0)] HS
      ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx) ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = ss_cwc_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  assert (Hk2 : k = 2) by lia.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
    apply (BODY Ev msx mdv2 A_FMT_D [37; 100]) end;
  first [ assumption
        | exact E38
        | (rewrite ew_havoc_old by lia; assumption)
        | (intros mem' md' HJx; exact (proj1 (cwc_fmt_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HROOK HRO HJx)))
        | (rewrite Hk2; reflexivity)
        | (cbn; lia)
        | (repeat constructor; lia)
        | (unfold RtPFCmd.CMD_IMG_HI, A_FMT_SPD, A_FMT_D; lia)
        | (intros ?; reflexivity) ].
Qed.


End t.

(* the loop at every FP state, by induction on the turns left *)
Lemma cwc_loop_ok : forall fx : YK11.FPState, CWC_LOOP_stmt (fx := fx) B RLO RHI.
Proof.
intros fx n. revert fx. induction n as [|n IH]; intros fx.
- unfold CWC_LOOP_n. intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 memc mdc fpos sp1 regsc k
  _ _ _ _ Hn Hk. exfalso. cbn in Hn. lia.
- exact (cwc_turn (fx := fx) n IH).
Qed.

End e.
End c.
End b.
