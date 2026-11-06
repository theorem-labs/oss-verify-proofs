(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s6.v, with its module paths and module names changed; 914 of its 958 lines of code are new or changed and 718 lines of the source are left out. *)
(* The walk of check_words_chain on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan),
   stage 3: the word loop, 0x892b4 .. 0x89330 (32 instructions, two calls per turn), by induction on the number
   of turns left. The B twin of lib/A/Prog/check_words_chain_s3.v, re-derived on B's code. On the `+ 8` band
   contracts (as in A): the atoi call's word w[k] has its 8 bytes of slack in its
   live block (PaLibH's amem8_of_blockA), and the snprintf call's destination list + o has its band
   [F + 32 + o, F + 809) inside the 1024-byte class-4 frame (o <= 744 by CwcText). On the runtime contracts' separation
   premises (as in A): the word is apart from the errno cell, a heap byte against an image
   byte.

   One turn, with F the frame, list = F + 32, w the word array, k the word number and o the length of the text
   already in list:
   - 0x892b4-0x892b8  the trap site 0x892b8 (`bgeu s11,770`): o <= 12 * (k - 2) <= 744 (CwcText's
     chain_items_at_len), so the branch to `unimp` 0x894a8 is not taken.  The executor decides it from the range
     of the atom for s11 that the state's facts carry.
   - 0x892bc-0x892c8  s10 := the format: " %d" (s7) when k is above 2, else the word at sp1 + 64 ("%d").  The
     executor stops at the compare, and the walk splits it; the two arms differ in s10 only, so both give s10 an
     atom of its own and then join at 0x892cc.
   - 0x892cc-0x892d8  the trap sites 0x892cc (w null), 0x892d0 (w + 8k null), 0x892d4 (w + 8k below w) and
     0x892d8 (w & 7 nonzero).  The facts of the state give the executor w >= 1 and w + 8k >= 4096 (the block of
     slot 2 and the block of slot k start at 4096 or above), w + 8k >= w (no wrap: w + 8k < alloc_ceiling) and
     s6 = w & 7 = 0 (cwc_pre's wp mod 8 = 0), so it decides each branch as not taken.
   - 0x892dc-0x892ec  the instrumented check of w[k]: the metadata byte at ((w + 8k) >> 3) + the shadow base
     from the spill slot sp1 + 88.  The state's shadow entry for the atom of s9 (cwc_SHw) says the 8 bytes at
     w + 8k are marked usable (cwc_wordk's shadow byte 0), so the token executor removes the check and the error
     path 0x894bc is not reached.
   - 0x892f0-0x89304  w[k], list + o, 769 - o, then the call of the atoi wrapper on w[k], through PaArt's
     aj_art_at under AATOI at the turn's FP state fx.
   - 0x89308-0x89318  the call of the snprintf wrapper that appends the number to list, through PaRt's
     cwc_aj_snprintf_atSF under ASNPRINTF at fx (rounding mode 0 at fx, the stage's premise); its text is ci_text
     (lib/B/Prog/CwcText.v) and is at most 12 bytes, and 769 - o is at least 25, so it is not cut.  The call
     returns at another FP state fx1 with PaFx's fxrel fx fx1: the walk moves its symbolic state to fx1 (PaFx's
     st_ok_pi_restrict_xfx), lifts the post (PaFx's srr_apost_baseF_lift: the post at fx1 is the post at fx) and runs the
     rest of the turn at fx1, with rounding mode 0 at fx1 by fxrel_frm0.
   - 0x8931c-0x89330  k, the two word pointers and the length move on; if k + 1 is below read the walk takes the
     induction hypothesis at fx1, else it takes the tail stage TAIL at fx1 at 0x89334.  The induction keeps the
     FP state general for this reason, and the runtime hypotheses hold at every FP state.

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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArt PaRt PaWalk PaFx CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
check_words_chain_c check_words_chain_s0 check_words_chain_iv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the pc where the two arms of the format choice join, as an offset from BASE *)
Definition CWC_CHK : Z := AF_check_words_chain + 0x1ec.   (* 0x892cc, the trap site of w null *)

(* the upper bound of alloc_ceiling (asan_consts): the facts of the state bound the word pointers by it *)
Definition CWC_PHI : Z := 0x7fffff800000.

(* --- the symbolic state at the head of the loop --- *)

(* atoms above the registers: 32 the shadow base, 33 "%d", 34 list, 35 read, 36 w[k]; 37 is the format of this
   turn, which the two arms of the format choice add *)
Definition cwc_lx (F r pk : Z) : list word :=
map (Z_to_bv 64) [SB; A_FMT_D; F + OFF_LIST; r; pk].

(* the four spill slots the loop reads: "%d", list, read, the shadow base *)
Definition cwc_spillR : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 96 0 0
[YP09.mkChunk 64 (CVal 8 (SOff 33 0));
 YP09.mkChunk 72 (CVal 8 (SOff 34 0));
 YP09.mkChunk 80 (CVal 8 (SOff 35 0));
 YP09.mkChunk 88 (CVal 8 CWC_Bx)].

(* slot k of the word array, read through s8 *)
Definition cwc_wordR : YP09.region :=
YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].

(* the facts that decide the five trap sites: w = s3 >= 1, w + 8k = s9 >= 4096, o = s11 <= 744, the shadow base,
   s9 >= s3 (unsigned) and s6 = 0 *)
Definition cwc_lfacts : facts :=
mkFacts [(19%nat, mkAF 1 CWC_PHI 3); (25%nat, mkAF 4096 CWC_PHI 3); (27%nat, mkAF 0 744 0);
         (32%nat, mkAF SB SB 0)]
        [mkAC BC_GEU (SOff 25 0) (SOff 19 0); mkAC BC_EQ (SOff 22 0) (SLit 0)] [].

(* the shadow entry of the instrumented check of w[k]: the 8 bytes from s9 are marked usable *)
Definition cwc_SHw : list shent := [mkSHE 25 0 8].

Definition ss_cwc_loop : sstate :=
mkSS CWC_LOOP sr_atoms [cwc_spillR; cwc_wordR] None cwc_lfacts.

(* the state at 0x892cc, where the two arms of the format choice join: a0 = 2 and s10 = atom 37, the format of
   this turn *)
Definition ss_cwc_chk : sstate :=
mkSS CWC_CHK
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SLit 2; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 37 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
  [cwc_spillR; cwc_wordR] None cwc_lfacts.

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition cwc_lE (regsc : bvmap 5 word) (F r pk : Z) : env :=
Eimg (Ereg regsc (cwc_lx F r pk)).

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HR : CwcRec B RLO RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
(* the runtime entries at every FP state: the loop calls the atoi wrapper at the turn's FP state and the snprintf
   wrapper returns at another, at which the next turn and the tail run (lib/B/Prog/check_words_chain_c.v:108-109) *)
Hypothesis AATOI : forall fx0 : YK11.FPState,
  @aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis TAIL : forall fx0 : YK11.FPState, CWC_TAIL_stmt (fx := fx0) B RLO RHI.

(* the lemmas of one turn, at one FP state; the loop below takes them at the FP state of each turn *)
Section fxh.
Context {fx : YK11.FPState}.

(* the state the walk starts the turn from *)
Lemma cwc_loop_entry : forall (W : world SEGS) (regsc : bvmap 5 word) memc (sp1 F r k wp o pk : Z),
getr regsc 9 = w64 sp1 -> getr regsc 19 = w64 wp -> getr regsc 22 = w64 0 ->
getr regsc 24 = w64 (wp + 8 * k) -> getr regsc 25 = w64 (wp + 8 * k) -> getr regsc 27 = w64 o ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 64) 8 A_FMT_D ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 72) 8 (F + OFF_LIST) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 80) 8 r ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 88) 8 SHADOW_OFF ->
val_mem SEGS (mrestrict (w_H W) memc) (wp + 8 * k) 8 pk ->
alloc_ceiling <= sp1 -> sp1 + 96 <= 2 ^ 47 ->
1 <= wp -> wp mod 8 = 0 -> 0 <= k -> 4096 <= wp + 8 * k -> wp + 8 * k + 8 <= alloc_ceiling ->
0 <= o <= 744 -> 0 <= r <= 64 -> 0 <= F -> F + OFF_LIST <= alloc_ceiling -> 0 <= pk < 2 ^ 64 ->
st_ok_pi SEGS VAL (cwc_lE regsc F r pk) ss_cwc_loop
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 F r k wp o pk R9 R19 R22 R24 R25 R27 V64 V72 V80 V88 VW
Hsp1 Hsp1h Hwp1 Hwp8 Hk0 Hw0 Hwc Ho Hr HF0 HFc Hpk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hw8 : (wp + 8 * k) mod 8 = 0)
by (replace (wp + 8 * k) with (wp + k * 8) by lia; rewrite Z_mod_plus_full; exact Hwp8).
rewrite restrict_mkst_fx.
set (E := cwc_lE regsc F r pk) in *.
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew E n = getr regsc rr)
by (intros n rr Hn Hrr; unfold E, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (cwc_lx F r pk) (Z_to_bv 64 0))
by (intros j Hj; unfold E, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth cwc_lx map] in E32, E33, E34, E35, E36.
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 22%nat 22%bv ltac:(lia) eq_refl) as Ea22.
pose proof (EN 24%nat 24%bv ltac:(lia) eq_refl) as Ea24.
pose proof (EN 25%nat 25%bv ltac:(lia) eq_refl) as Ea25.
pose proof (EN 27%nat 27%bv ltac:(lia) eq_refl) as Ea27.
assert (U9 : bv_unsigned (ew E 9) = sp1)
by (rewrite Ea9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = wp)
by (rewrite Ea19, R19; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = wp + 8 * k)
by (rewrite Ea24, R24; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = wp + 8 * k)
by (rewrite Ea25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = o)
by (rewrite Ea27, R27; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SB)
by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
unfold ss_cwc_loop. apply pa_entry_st_ok_full.
- unfold E, cwc_lE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cwc_spillR, cwc_wordR.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite U9. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 33 0) A_FMT_D);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold A_FMT_D; lia | cbn; lia | exact V64].
    * apply (chunk_ok_val SEGS E _ sp1 72 8 (SOff 34 0) (F + OFF_LIST));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFF_LIST in *; lia | cbn; lia | exact V72].
    * apply (chunk_ok_val SEGS E _ sp1 80 8 (SOff 35 0) r);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V80].
    * apply (chunk_ok_val SEGS E _ sp1 88 8 CWC_Bx SHADOW_OFF);
      [unfold CWC_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | cbn; lia | exact V88].
  + cbn [base_val]. rewrite U24. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (wp + 8 * k) 0 8 (SOff 36 0) pk);
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact VW.
- apply pairwise_disjoint_of_extents.
  unfold cwc_spillR, cwc_wordR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [|exact I]].
  + cbn [cwc_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U25, U27, U32.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold CWC_PHI, SB. repeat split; lia.
  + cbn [cwc_lfacts f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|split; [|exact I]].
    * rewrite branch_geu_U.
      rewrite (U_atom E 25 (wp + 8 * k) (eq_trans Ea25 R25) ltac:(lia)),
        (U_atom E 19 wp (eq_trans Ea19 R19) ltac:(lia)).
      apply negb_true_iff, Z.ltb_ge. lia.
    * rewrite branch_eq_U.
      rewrite (U_atom E 22 0 (eq_trans Ea22 R22) ltac:(lia)), (U_lit E 0 ltac:(lia)). reflexivity.
Qed.

(* the shadow entry of the check of w[k], from the slot's shadow byte *)
Lemma cwc_shw_ok : forall E (W : world SEGS) m x,
bv_unsigned (ew E 32) = SB -> bv_unsigned (ew E 25) = x ->
rdW W m (SHADOW_OFF + x / 8) = Some 0 -> x mod 8 = 0 -> amem_range x 8 ->
sh_ok SEGS CWC_Bx cwc_SHw E (mrestrict (w_H W) m).
Proof.
intros E W m x U32 U25 Hsh Hx8 Hamr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, cwc_SHw. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E CWC_Bx 25 x 8 x 0 8).
- apply zero_shadow_of_bytes; [exact Hx8 | reflexivity | lia |].
  intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hsh.
- unfold U, CWC_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U32. reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U25.
- lia.
- lia.
- intros y Hy. cbn [Z.min Z.max] in Hy.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma cwc_soff0 : forall E n v, ew E n = w64 v -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma cwc_soff : forall E n c v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n c v H H1 H2. rewrite denot_lit_U. try unfold w64. f_equal.
apply (U_atom_off E n v c); [exact H | lia | lia].
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
(forall a, sp1 <= a < sp1 + 96 -> ~ X a) ->
(forall a, frame_addr ly CWC_CID fpos + 1016 <= a < frame_addr ly CWC_CID fpos + 1024 -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
0 <= spZ regs - 104 -> spZ regs < 2 ^ 64 -> 0 <= sp1 -> sp1 + 96 < 2 ^ 64 ->
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
{ destruct HSP2 as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split;
  (apply (cwc_vm_kept W memc memc'); [intros b Hb2; apply HK; [lia | apply Hsl; lia] |]);
  first [exact P0 | exact P1 | exact P2 | exact P3 | exact P4 | exact P5 | exact P6 | exact P7]. }
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

End fxh.

(* --- the loop --- *)

(* at every FP state: the induction hypothesis is used at the FP state the turn's snprintf call returned *)
Lemma cwc_loop_ok : forall fx : YK11.FPState, CWC_LOOP_stmt (fx := fx) B RLO RHI.
Proof.
intros fx. unfold CWC_LOOP_stmt. intros n. revert fx. induction n as [|n IH]; intros fx;
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 memc mdc fpos sp1 regsc k
HPRE HMID HFRM HRND Hn Hk R2 R3 R4 R8 R9 R19 R20 R22 R23 R24 R25 R27 HSP64 HLIST HWORDS HQ1 HQ2;
[exfalso; cbn in Hn; lia|].
pose proof (paj_run (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI)) as BR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
pose proof (cr_tl B RLO RHI HR) as TLv.
pose proof (pal_env B TLv) as HAPI.
pose proof HAPI as (HERRr & HERRimg & _).
pose proof HPRE as (HFN & HRO & Ea0 & Ea1 & Ea2 & Hr & Hwp & HROOK & HOBJ & HGU & HFLB & HERRv &
Hcp1 & Hcp2 & Hcp8 & HNAv & HNAr & HPQ1 & HPQ2 & HWSp & Hwp8 & HNA3 & HX1 & HX2 & HCNT & HNEV).
pose proof HMID as (HJ & HAB & HSP1 & HFRAME & HSPILL & HFLAGW & HFSH).
pose proof (proj1 HJ) as HAR.
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12528) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HSPz : alloc_ceiling + 12528 <= spZ regs <= 2 ^ 47) by lia.
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
assert (Hsp1m : (spZ regs - 224) mod 16 = 0)
by (replace (spZ regs - 224) with (spZ regs + (-14) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
pose proof (snt_sp1_facts (spZ regs - 224) ltac:(lia) Hsp1m) as (Hs1a & Hs1b & Hs1c).
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
(* the trap sites of w: the blocks of slots 2 and k start at 4096 or above *)
assert (HWLO : 4096 <= wp + 8 * k /\ 4080 <= wp).
{ pose proof (HWSp 2 ltac:(lia)) as (HBLK2 & _).
  destruct HBLK as (bb & bn & Hbin & Hb1 & Hb2). destruct HBLK2 as (bb2 & bn2 & Hbin2 & Hc1 & Hc2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR0 Hbin) as (_ & H4a & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb2 bn2 HAR0 Hbin2) as (_ & H4b & _). lia. }
assert (Hw8 : (wp + 8 * k) mod 8 = 0)
by (replace (wp + 8 * k) with (wp + k * 8) by lia; rewrite Z_mod_plus_full; exact Hwp8).
(* the state at the head of the loop *)
assert (HS : st_ok_pi SEGS VAL (cwc_lE regsc F r (nth (Z.to_nat k) pw 0)) ss_cwc_loop
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_LOOP)) memc (seg_rom SEGS)))).
{ pose proof HSPILL as (_ & _ & _ & _ & _ & P72 & P80 & P88).
  apply (cwc_loop_entry W regsc memc sp1 F r k wp o (nth (Z.to_nat k) pw 0));
  [ exact R9 | exact R19 | exact R22 | exact R24 | exact R25 | exact R27 | exact HSP64
  | exact P72 | exact P80 | exact P88
  | exact (cwc_val_mem_of_aval W memc _ _ _ HWK2)
  | lia | lia | lia | exact Hwp8 | lia | lia | exact HWK1 | exact HO | lia | lia | unfold OFF_LIST; lia
  | unfold astr_len in RD1; lia ]. }
set (E0 := cwc_lE regsc F r (nth (Z.to_nat k) pw 0)) in *.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, cwc_lE; apply Eimg_env).
assert (EN0 : forall (m : nat) (rr : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned rr ->
ew E0 m = getr regsc rr)
by (intros m rr Hm Hrr; unfold E0, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX0 : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (cwc_lx F r (nth (Z.to_nat k) pw 0)) (Z_to_bv 64 0))
by (intros j Hj; unfold E0, cwc_lE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (G2 : ew E0 2 = w64 sp1) by (rewrite (EN0 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
assert (G3 : ew E0 3 = w64 (as_gp B)) by (rewrite (EN0 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
assert (G4 : ew E0 4 = w64 (as_tp B)) by (rewrite (EN0 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
assert (G8 : ew E0 8 = w64 (spZ regs)) by (rewrite (EN0 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
assert (G9 : ew E0 9 = w64 sp1) by (rewrite (EN0 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
assert (G19 : ew E0 19 = w64 wp) by (rewrite (EN0 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
assert (G20 : ew E0 20 = w64 k) by (rewrite (EN0 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
assert (G22 : ew E0 22 = w64 0) by (rewrite (EN0 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
assert (G23 : ew E0 23 = w64 A_FMT_SPD) by (rewrite (EN0 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
assert (G24 : ew E0 24 = w64 (wp + 8 * k)) by (rewrite (EN0 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
assert (G25 : ew E0 25 = w64 (wp + 8 * k)) by (rewrite (EN0 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
assert (G27 : ew E0 27 = w64 o) by (rewrite (EN0 27%nat 27%bv ltac:(lia) eq_refl); exact R27).
assert (G32 : ew E0 32 = w64 SB) by exact (EX0 0%nat ltac:(lia)).
assert (G33 : ew E0 33 = w64 A_FMT_D) by exact (EX0 1%nat ltac:(lia)).
assert (G34 : ew E0 34 = w64 (F + OFF_LIST)) by exact (EX0 2%nat ltac:(lia)).
assert (G35 : ew E0 35 = w64 r) by exact (EX0 3%nat ltac:(lia)).
assert (G36 : ew E0 36 = w64 (nth (Z.to_nat k) pw 0)) by exact (EX0 4%nat ltac:(lia)).
assert (SHOK : sh_ok SEGS CWC_Bx (@nil shent) E0 (mrestrict (w_H W) memc)) by constructor.
lazymatch goal with |- SRr _ _ _ ?Qg => set (Qgoal := Qg) end.
(* the rest of the turn, which the two arms of the format choice share *)
assert (BODY : forall (E1 : env) (msb : machine_state) (mdx : Model) (fmtp : Z) (fl : list Z),
  img_env VAL A_LIM E1 ->
  st_ok_pi SEGS VAL E1 ss_cwc_chk (restrict (w_H W) msb) ->
  ms_mem msb = memc ->
  ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W (ms_mem msb) mdx 0 ->
  ew E1 2 = w64 sp1 -> ew E1 3 = w64 (as_gp B) -> ew E1 4 = w64 (as_tp B) ->
  ew E1 8 = w64 (spZ regs) -> ew E1 9 = w64 sp1 -> ew E1 19 = w64 wp -> ew E1 20 = w64 k ->
  ew E1 22 = w64 0 -> ew E1 23 = w64 A_FMT_SPD -> ew E1 24 = w64 (wp + 8 * k) ->
  ew E1 25 = w64 (wp + 8 * k) -> ew E1 27 = w64 o -> ew E1 32 = w64 SB -> ew E1 33 = w64 A_FMT_D ->
  ew E1 34 = w64 (F + OFF_LIST) -> ew E1 35 = w64 r ->
  ew E1 36 = w64 (nth (Z.to_nat k) pw 0) -> ew E1 37 = w64 fmtp ->
  (forall mem' md', ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W mem' md' 0 ->
     cwc_strk W mem' fmtp (pf_bytes fl)) ->
  pf_parse fl = Some (ci_ps (Z.to_nat k)) -> (length fl <= 3)%nat ->
  (* the format in the image, and its bytes (the shared snprintf contract's premises) *)
  RtPFCmd.CMD_IMG_LO <= fmtp -> fmtp + Z.of_nat (length fl) + 1 <= RtPFCmd.CMD_IMG_HI ->
  Forall (fun c => 0 <= c < 256) fl ->
  (* the snprintf family's literal check (RtPFCmd.fr_lit_ok), computed at each format *)
  (forall v, RtPFCmd.fr_lit_ok fmtp fl (map RtPFCmd.arg_of [AInt v]) = true) ->
  SRr SEGS W (mkCfg msb mdx) Qgoal).
2:{
(* 0x892b4 .. the compare of k with 2; the trap site 0x892b8 is decided by the fact o <= 744 *)
paj_run_tok RUN HS HJ SHOK CWC_Bspan; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
set (mdv1 := mdq) in *; clearbody mdv1 end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
assert (HM1 : ms_mem msx = memc)
by (exact (frame_of_read_only _ [cwc_spillR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
clear_frames.
psrr_branch_tok RUN BR HS SHOK CWC_Bspan.
- (* 2 < k: the format stays " %d" *)
  paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan CWC_CHK; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HM2 : ms_mem msx = memc)
  by (rewrite <- HM1; exact (frame_of_read_only _ [cwc_spillR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  rewrite branch_ltu_U, (U_lit E0 2 ltac:(lia)),
    (U_atom E0 20 k G20 ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  prreg HS (26%bv : bv 5) Q26.
  add_atom HS 37%nat (w64 A_FMT_SPD) E37.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (26%bv : bv 5) (SOff 37 0) HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact (eq_trans Q26 G23))) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (f_atoms cwc_lfacts) (f_conds cwc_lfacts) (@nil (sv * sv)) HS
      ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(intros xx Hxx; destruct Hxx)) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = ss_cwc_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
    apply (BODY Ev msx mdv2 A_FMT_SPD [32; 37; 100]) end;
  first [ assumption
        | exact E37
        | (rewrite ew_havoc_old by lia; assumption)
        | (intros mem' md' HJx; exact (proj2 (cwc_fmt_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HROOK HRO HJx)))
        | (unfold ci_ps; destruct (Nat.eqb_spec (Z.to_nat k) 2); [lia | reflexivity])
        | (cbn; lia)
        | (unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, A_FMT_SPD; cbn [length]; lia)
        | (repeat constructor; lia)
        | (intros ?; reflexivity) ].
- (* k = 2: the format is the word at sp1 + 64, "%d" *)
  paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan CWC_CHK; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HM2 : ms_mem msx = memc)
  by (rewrite <- HM1; exact (frame_of_read_only _ [cwc_spillR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  rewrite branch_ltu_U, (U_lit E0 2 ltac:(lia)),
    (U_atom E0 20 k G20 ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  prreg HS (26%bv : bv 5) Q26.
  add_atom HS 37%nat (w64 A_FMT_D) E37.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (26%bv : bv 5) (SOff 37 0) HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact (eq_trans Q26 G33))) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (f_atoms cwc_lfacts) (f_conds cwc_lfacts) (@nil (sv * sv)) HS
      ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(intros xx Hxx; destruct Hxx)) as HS3;
    clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = ss_cwc_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  assert (Hk2 : k = 2) by lia.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
    apply (BODY Ev msx mdv2 A_FMT_D [37; 100]) end;
  first [ assumption
        | exact E37
        | (rewrite ew_havoc_old by lia; assumption)
        | (intros mem' md' HJx; exact (proj1 (cwc_fmt_now B RLO RHI HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HROOK HRO HJx)))
        | (rewrite Hk2; reflexivity)
        | (cbn; lia)
        | (unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, A_FMT_D; cbn [length]; lia)
        | (repeat constructor; lia)
        | (intros ?; reflexivity) ]. }
intros E1 msb mdx fmtp fl HEI1 HS1 HMb HJ1 N2 N3 N4 N8 N9 N19 N20 N22 N23 N24 N25 N27 N32 N33 N34 N35 N36 N37
  HFMT HPARSE HFLEN HFIMG0 HFIMG1 HFMTB HLIT.
set (pk := nth (Z.to_nat k) pw 0) in *.
set (xk := nth (Z.to_nat k) ws []) in *.
assert (FRNE : forall a, F <= a < F + 1024 -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. apply (frm_img _ _ LAWS ly S2 W memc mdc CWC_CID fpos a HAR HINF);
  [rewrite HFB; rewrite <- HFdef; lia | exact (HERRimg a He)]. }
assert (SHOK1 : sh_ok SEGS CWC_Bx cwc_SHw E1 (mrestrict (w_H W) (ms_mem msb))).
{ rewrite HMb. apply (cwc_shw_ok E1 W memc (wp + 8 * k));
  [ rewrite N32; apply unsigned_lit_small; unfold SB; lia
  | rewrite N25; apply unsigned_lit_small; lia
  | exact HWK3 | exact Hw8 | exact HWAMR ]. }
(* 0x892cc .. the call of the atoi wrapper: the four trap sites are decided by the facts, the check of w[k] is
   removed by the shadow entry *)
paj_run_tok RUN HS1 HJ1 SHOK1 CWC_Bspan; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
set (mdw1 := mdq) in *; clearbody mdw1 end.
lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?msx) =>
assert (HMc : ms_mem msx = memc)
by (rewrite <- HMb; exact (frame_of_read_only _ [cwc_spillR; cwc_wordR] _ _ ltac:(vm_compute; reflexivity) HF));
rename msx into ms1 end.
clear_frames.
pmkst HS1.
prreg HS1 (1%bv : bv 5) P1.
rreg_by HS1 (2%bv : bv 5) (w64 sp1) (cwc_soff0 E1 2 sp1 N2) P2.
rreg_by HS1 (3%bv : bv 5) (w64 (as_gp B)) (cwc_soff0 E1 3 _ N3) Qgp.
rreg_by HS1 (4%bv : bv 5) (w64 (as_tp B)) (cwc_soff0 E1 4 _ N4) Qtp.
rreg_by HS1 (10%bv : bv 5) (w64 pk) (cwc_soff0 E1 36 _ N36) Qa0.
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
(* the atoi contract's separation premise: the word lies in a live
   block of the entry, whose bytes are not image bytes (YCbq's blk_img, the statement of RecBLemmas.v's
   recb_heap_noimg_m), and the errno cell is (PALib's pal_env, HERRimg) *)
assert (HSEPk : pk + astr_len xk + 1 <= as_errno B \/ as_errno B + 4 <= pk).
{ destruct (Z_le_gt_dec (pk + astr_len xk + 1) (as_errno B)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (as_errno B + 4) pk) as [H2|H2]; [right; exact H2|]. exfalso.
  pose proof HBLKk as Hb. unfold in_blockA in Hb. destruct Hb as (b0 & k0 & Hb0 & Hb1 & Hb2).
  assert (Hrq : k0 <= req_size k0)
  by (unfold req_size; destruct (k0 =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia).
  unfold astr_len in *.
  apply (blk_img _ _ LAWS ly S W mem md b0 k0 (Z.max pk (as_errno B)) HAR0 Hb0); [lia|].
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
(* 0x89308 .. the call of the snprintf wrapper *)
paj_run_tok RUN HS2 HJ2 SHOK2 CWC_Bspan; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
set (mdw2 := mdq) in *; clearbody mdw2 end.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
assert (HMd : ms_mem msx = mem2)
by (exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
rename msx into ms2 end.
clear_frames.
pmkst HS2.
assert (PF10 : sv_denot E2 (SAlu ALU_ADD (SOff 27 0) (SOff 34 0)) = w64 (F + OFF_LIST + o)).
{ rewrite denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E2 27 o) by (first [rewrite OLD2 by lia; exact N27 | lia]).
  rewrite (U_atom E2 34 (F + OFF_LIST)) by (first [rewrite OLD2 by lia; exact N34 | unfold OFF_LIST; lia]).
  rewrite zcanon_id by (unfold M64, OFF_LIST; lia). lia. }
assert (PF11 : sv_denot E2 (SAlu ALU_SUB (SLit 0) (SOff 27 (-769))) = w64 (769 - o)).
{ rewrite denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SLit, U_SOff, OLD2 by lia. rewrite N27. try unfold w64. rewrite unsigned_lit_small by lia.
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
rreg_by HS2 (12%bv : bv 5) (w64 fmtp) (cwc_soff0 E2 37 _ (eq_trans (OLD2 37%nat ltac:(lia)) N37)) QF.
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
    [(CWC_CID, fpos)] a).
{ intros a Ha. unfold OFF_LIST in Ha.
  unfold awr_byte. right; right; right; left. unfold in_frames. exists CWC_CID, fpos.
  split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite HFB, <- HFdef. lia. }
assert (HPC : forall a, F + OFF_LIST + o <= a < F + OFF_LIST + o + (769 - o) -> inFP [] a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ spZ regs <= a < ly_top ly ->
  writable_at SEGS (mrestrict (w_H W) mem2) a)
by (intros a _ Hfp; exfalso; exact (inFP_nil a Hfp)).
(* list + o's band [F + 32 + o, F + 809) with the slack word lies inside the 1024-byte class-4 frame *)
assert (HAMR : amem_range (F + OFF_LIST + o) (769 - o + 8))
by (unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, OFF_LIST in *; lia).
assert (HRAD : range_addressable (rdW W mem2) SHADOW_OFF (F + OFF_LIST + o) (769 - o)).
{ pose proof (cwc_list_ra (rdW W mem2) F o ltac:(rewrite HFdef; exact HF8) ltac:(lia) ltac:(lia) FSH2) as HL.
  unfold LEN_LIST in HL. exact HL. }
assert (HHULL : shadow_hull_vis (rdW W mem2) (F + OFF_LIST + o) (769 - o)).
{ apply (shadow_hull_vis_of_frame _ _ LAWS ly S2 W mem2 mdw2 CWC_CID fpos _ _ (proj1 HJ2) HINF);
  rewrite ?HFB, <- ?HFdef; unfold OFF_LIST; lia. }
assert (HARGS : apf_args_ok SEGS (3 * ESTACK) W (ms_regs ms2) mem2 (F + OFF_LIST + o) (769 - o)
  [getr (ms_regs ms2) 13; getr (ms_regs ms2) 14; getr (ms_regs ms2) 15; getr (ms_regs ms2) 16;
   getr (ms_regs ms2) 17] [AInt (atoi_a xk)]).
{ cbn [apf_args_ok apf_arg_ok]. split; [|exact I]. split; [unfold atoi_a; apply HSW|].
  rewrite Pa3. try unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_eq (atoi_a xk) (2 ^ 64)) by lia.
  replace (atoi_a xk - 2 ^ 64 * (atoi_a xk / 2 ^ 64))
    with (atoi_a xk + (- (2 ^ 32 * (atoi_a xk / 2 ^ 64))) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
eapply SRr_bind.
{ (* the destination [list + o, list + 769) lies in the frame, so off the image and below the call's window *)
  assert (HD0 : 0 < F + OFF_LIST + o) by (unfold OFF_LIST; lia).
  assert (HDIMG : F + OFF_LIST + o + (769 - o) <= RtPFCmd.CMD_IMG_LO \/ RtPFCmd.CMD_IMG_HI <= F + OFF_LIST + o).
  { pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR HINF) as HOI. rewrite HFB, <- HFdef in HOI.
    unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, OFF_LIST.
    destruct HOI as [HOI | HOI]; [left | right]; lia. }
  assert (HDWIN : F + OFF_LIST + o + (769 - o) <= spZ regs + (sp1 - spZ regs) - 3 * ESTACK)
  by (unfold OFF_LIST; lia).
  (* the stack-protector GOT word and guard lie in the image *)
  assert (HGI : RtPFCmd.CMD_IMG_LO <= 0xa6bf8 /\ 0xa6bf8 + 8 <= RtPFCmd.CMD_IMG_HI /\
    RtPFCmd.CMD_IMG_LO <= 0x604158 /\ 0x604158 + 8 <= RtPFCmd.CMD_IMG_HI)
  by (unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI; lia).
  destruct HGI as (HGI0 & HGI1 & HGI2 & HGI3).
  exact (cwc_aj_snprintf_atSF SEGS B LAWS Hsegs (SIGMA CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158
    (ASNPRINTF fx)
    W (ms_regs ms2) mem2 CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 mdw2 0
    (F + OFF_LIST + o) (769 - o) fmtp fl (ci_ps (Z.to_nat k)) (atoi_a xk) (ci_text atoi_a (Z.to_nat k) ws)
    (sp1 - spZ regs) (getr (ms_regs ms2) 1)
    HJ2 QD QN QF ltac:(lia) HD0 HDIMG HDWIN Qsp2 Ho16
    ltac:(lia) ltac:(lia) Qgp2 Qtp2 eq_refl Qra2
    HDEST HPC HAMR HRAD HHULL HGU2 HGI0 HGI1 HGI2 HGI3 HFIMG0 HFIMG1 HFSTR HFMTB HPARSE HTXT ltac:(lia)
    (nz_bytes _ (ci_text_nz atoi_a (Z.to_nat k) ws)) HFRD2 HARGS ROM2 (HLIT (atoi_a xk)) HRND). }
cbv beta. intros W3 c3 _ (HW3 & fx1 & regs3 & mem3 & md3 & Hfx & Hc3 & HJ3 & HP3 & HR3 & HB3 & HKP3 & HPR3 & _).
subst W3 c3.
rewrite P1b.
jafter_call_keep_pi HS2 60%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HMd. repeat apply Forall_cons; try apply Forall_nil.
  apply (cwc_region_kept _ W mem2 mem3 _); [|cbn; lia].
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite OLD2 by lia. rewrite N9. try unfold w64.
  rewrite unsigned_lit_small by lia.
  intros a Ha. apply HKP3; [lia | unfold OFF_LIST; lia | lia]. }
clear HS2. rewrite <- (restrict_mkst_fx (fx := fx)) in HS3.
(* the call returned at fx1: the symbolic state and the post move to fx1, rounding mode 0 holds at fx1, and the
   rest of the turn runs at fx1 (fx is cleared, so every FP argument below is fx1) *)
apply (st_ok_pi_restrict_xfx fx fx1) in HS3.
unfold Qgoal, cwc_post.
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
pose proof (fxrel_frm0 fx fx1 HRND Hfx) as HRND1.
clear dependent fx.
pose proof (paj_run (fx := fx1) (PL := PL_cmd) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx1) (PL := PL_cmd) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx1) (PI := PI)) as BR.
lazymatch type of HS3 with st_ok_pi _ _ ?Ev _ _ => remember Ev as E3 eqn:HE3 in HS3 end.
assert (HEIx3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall m, (m < 40)%nat -> ew E3 m = ew E1 m)
by (intros m Hm; rewrite HE3, ew_havoc_old by lia; apply OLD2; lia).
assert (M64a : ew E3 64 = getr regs3 10)
by (rewrite HE3; exact (ew_havoc_new E2 60 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (SHOK3 : sh_ok SEGS CWC_Bx (@nil shent) E3 (mrestrict (w_H W) mem3)) by constructor.
(* 0x8931c .. the back edge *)
paj_run_tok RUN HS3 HJ3 SHOK3 CWC_Bspan; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
set (mdw3 := mdq) in *; clearbody mdw3 end.
lazymatch type of HS3 with
| st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HMe : ms_mem msx = mem3)
  by (exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF))
| st_ok _ _ _ (restrict _ ?msx) =>
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
assert (HSP64' : val_mem SEGS (mrestrict (w_H W) mem3) (sp1 + 64) 8 A_FMT_D).
{ apply (cwc_vm_kept W memc mem3); [|exact HSP64].
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
psrr_branch_tok RUN BR HS3 SHOK3 CWC_Bspan.
+ (* r <> k + 1: the next turn *)
  rewrite branch_ne_U, (U_atom E3 35 r ltac:(rewrite OLD3 by lia; exact N35) ltac:(lia)),
    (U_atom_off E3 20 k 1 ltac:(rewrite OLD3 by lia; exact N20) ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hk1 : k + 1 < r) by lia.
  paj_run_to_tok RUNTO HS3 HJ3 SHOK3 CWC_Bspan CWC_LOOP; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw4 := mdq) in *; clearbody mdw4 end.
  lazymatch type of HS3 with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMf : ms_mem msx = mem3)
    by (rewrite <- HMe; exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms4
  | st_ok _ _ _ (restrict _ ?msx) =>
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
  rreg_by HS3 (19%bv : bv 5) (w64 wp) (cwc_soff0 E3 19 _ (eq_trans (OLD3 19%nat ltac:(lia)) N19)) T19.
  rreg_by HS3 (20%bv : bv 5) (w64 (k + 1))
    (cwc_soff E3 20 1 k (eq_trans (OLD3 20%nat ltac:(lia)) N20) ltac:(lia) ltac:(lia)) T20.
  rreg_by HS3 (22%bv : bv 5) (w64 0) (cwc_soff0 E3 22 _ (eq_trans (OLD3 22%nat ltac:(lia)) N22)) T22.
  rreg_by HS3 (23%bv : bv 5) (w64 A_FMT_SPD) (cwc_soff0 E3 23 _ (eq_trans (OLD3 23%nat ltac:(lia)) N23)) T23.
  rreg_by HS3 (24%bv : bv 5) (w64 (wp + 8 * k + 8))
    (cwc_soff E3 24 8 (wp + 8 * k) (eq_trans (OLD3 24%nat ltac:(lia)) N24) ltac:(lia) ltac:(lia)) T24.
  rreg_by HS3 (25%bv : bv 5) (w64 (wp + 8 * k + 8))
    (cwc_soff E3 25 8 (wp + 8 * k) (eq_trans (OLD3 25%nat ltac:(lia)) N25) ltac:(lia) ltac:(lia)) T25.
  assert (PF27 : sv_denot E3 (SAlu ALU_ADD (SOff 27 0) (SOff 64 0))
    = w64 (Z.of_nat (length (cwc_T ws (k + 1))))).
  { rewrite HO1, denot_lit_U. try unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E3 27 o) by (first [rewrite OLD3 by lia; exact N27 | lia]).
    rewrite (U_atom E3 64 (Z.of_nat (length (ci_text atoi_a (Z.to_nat k) ws))))
      by (first [rewrite M64a; exact HR3 | lia]).
    rewrite zcanon_id by (unfold M64; lia). lia. }
  rreg_by HS3 (27%bv : bv 5) (w64 (Z.of_nat (length (cwc_T ws (k + 1))))) PF27 T27.
  rewrite HMf.
  apply (IH fx1 ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 mem3 mdw4 fpos sp1 (ms_regs ms4) (k + 1));
  first [ exact HPRE | exact HFRM | exact HRND1 | lia | assumption
        | (rewrite T24; f_equal; lia)
        | (rewrite T25; f_equal; lia)
        | (rewrite <- HMf; exact HMID3)
        | (rewrite HMf in HJ3; destruct HMID3 as (_ & HM3r); split; [exact HJ3 | exact HM3r])
        | (intros j Hj; exact (HWORDS' j Hj)) ].
+ (* r = k + 1: the tail *)
  rewrite branch_ne_U, (U_atom E3 35 r ltac:(rewrite OLD3 by lia; exact N35) ltac:(lia)),
    (U_atom_off E3 20 k 1 ltac:(rewrite OLD3 by lia; exact N20) ltac:(lia) ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hk1 : r = k + 1) by lia.
  paj_run_to_tok RUNTO HS3 HJ3 SHOK3 CWC_Bspan CWC_TAIL; [awr_ok_tac|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw4 := mdq) in *; clearbody mdw4 end.
  lazymatch type of HS3 with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMf : ms_mem msx = mem3)
    by (rewrite <- HMe; exact (frame_of_read_only _ [cwc_spillR] _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms4
  | st_ok _ _ _ (restrict _ ?msx) =>
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
  rewrite HMf.
  assert (HLISTr : abytes_at SEGS W mem3 (F + OFF_LIST) (pf_bytes (chain_list_at atoi_a r ws ++ [0]))).
  { unfold chain_list_at. replace r with (k + 1) by lia. exact HLIST'. }
  apply (TAIL fx1 ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 mem3 mdw4 fpos sp1 (ms_regs ms4));
  first [ exact HPRE | exact HFRM | exact HRND1 | assumption
        | (rewrite HMf in HJ3; destruct HMID3 as (_ & HM3r); split; [exact HJ3 | exact HM3r]) ].
Qed.

End e.
End c.
End b.
