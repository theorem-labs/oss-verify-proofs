(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 684 of its 739 lines of code are new or changed and 1025 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A' (ASan build): segment S0 (row TPA-S0).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   WHAT IT PROVES: tp_seg_S0_holds : forall P, srr_inv_laws segs P -> tp_seg_S0 B SK CTX0 P, the statement of
   lib/A/Prog/TxPut102A_Base.v (sha256 62ed8c667f58; internal record), for an
   ABSTRACT memory invariant P with its runner laws only (S0 calls nothing, so no srr_inv_call). From tp_pre at
   tp_cfg0 (tx_put's entry, tpi_entry) to the three continuations tp_k_END (+332), tp_k_FIT (+248), tp_k_GROW (+172).
   THE IMAGE: A' = asan pin sha256 1be0f53d96cb9d6c; listing lib/A/Listing_prog.v (sha256 62db5cdc9519; internal record) (slots
   3523 ..); reading aid tx_put.asan.new.s (sha256 bbe8e5e792381262). Kit text served (through the
   base): lib/A/PRH_FnTx.v (sha256 00de73011bd4; internal record), PRH_Base.v (sha256 427856c3ea51; internal record).
   ENGINE (the set preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record), as on the base):
   YC80x.v 14f84f225e8f / YC1fPx.v 7814b594066f (paj_run_x_inv, paj_run_to_x_inv), YC1fP.v (sha256 ca004ee6467b; internal record) (paj_branch,
   pa_entry_st_ok_full), YCbn.v (sha256 9cc538f0d776; internal record) (the shadow-check tokens), YCbqGcallW.v 49e664902830 (ajournal_x_init_W,
   cj_kept_exec); S1Ledger.v (sha256 2f7584181620; internal record) (prh_ledger_kept_aview). Templates (shape only): the S10 tx walk
   S10TxPut.v (sha256 7d5da9894878; internal record) (:350-440), Caw102A_WA4.v (sha256 58015a35ca82; internal record), Ent102L0A.v (sha256 0a61f81f4dbf; internal record),
   Caw102B_WB0.v (sha256 6e6ccc226d48; internal record).
   THE CODE WALKED (byte offsets from the entry, A' 0x84cec):
     +0 .. +52   frame 112, the thirteen saves (ra s0 .. s11 at sp0 - 8 .. sp0 - 104)
     +56 .. +68  s1 = n; the GOT pair (A_OBJ 0 holds the shadow cell's address, tpi_pal's palc_got_shadow /
                 palc_cell) and `ld s6, 0(a2)` = SHADOW_OFF (ARx's const law)
     +72 .. +96  s0 = t, s4 = t + 24, s8 = shadow (t + 24), `lb a0, 0(s8)`, s2 = s, bnez -> slow path +420
     +100        `lw a0, 0(s4)` = failed (the 4-byte chunk of the record, atom 36)
     +104        bnez a0 -> +332 (FAILED AT ENTRY: tp_k_END with tp_Q's second arm, nothing written)
     +108 .. +164 s3 / s7 = t + 8 / its shadow, s5 / s9 = t + 16 / its shadow, a0 = n + len0, a1 = a0 + 1,
                 a2 = cap0, s10 = t >> 3
     +168        bgeu a2, a1 -> +248 (tp_k_FIT, b1 = b0, cap1 = cap0) / fall into +172 (tp_k_GROW)
   REFUTED / DISCHARGED SITES (every one an obligation of the engine's token rule YCbn.v tok_branch, discharged from
   prhtx_place's range_addressable SHADOW_OFF t 28, carried across the prologue's frame writes by s0_ra_frame):
     +96 bnez (shadow of t + 24) to the slow path +420: the slow block `andi a1, s4, 7; addi a1, a1, 3; blt a1, a0`
         returns to +100 exactly when the 4-byte access is addressable (obligation t + 24, 4 bytes); the report
         call __asan_report_load4 (+436) is unreachable;
     +124 bnez (shadow of t + 8) to __asan_report_load8 (+472): obligation t + 8, 8 bytes;
     +144 bnez (shadow of t + 16) to __asan_report_load8 (+480): obligation t + 16, 8 bytes.
   The two data branches (+104 failed, +168 the need test) are split by paj_branch; no other branch exists in S0.
   IMAGE FACTS USED (tp_img's projections, never positions): tpi_entry, tpi_pal (palc_got_shadow, palc_cell,
   palc_got_cell), tpi_pst_img. No Section hypothesis; no universal law.
   THE CARRY at the three cuts: s0_keep (every memory fact of tp_pre the cuts restate, off the frame
   [sp0 - 112, sp0)), s0_cut_carry (tp_carry: tp_J from the runner, tp_K by YCbqGcallW.cj_kept_exec, gp / tp / sp,
   the thirteen saved slots from the frame region's chunks), s0_regs_at (the register file at +168 / FIT / GROW).
   Numerals: 112 (LENGTH: TP_FRAME, the base's); 8 .. 104 (LENGTH: the save slots); 0 / 8 / 16 / 24 / 28 (LENGTH:
   the record's fields and its 28 accessed bytes); 3 (WORD: the shift of the shadow mapping) and 4 (the failed
   width); atom numbers 2 / 10 / 12 / 32 .. 36 and the engine's 512 (DERIVED: the engine's numbering); 2 ^ 28 /
   2 ^ 44 .. 2 ^ 47 / 2 ^ 61 / 2 ^ 64 (bounds: the text's need bound, shadow / stack / word bounds). No ADDRESS:
   every pc is TP_OFF + a TP_PC_* of the base, every image address a pa_val. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC88.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger TxPutCall102 TxPut102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure facts ---- *)
Lemma s0_shadow_lo : forall x, 0 <= x <= 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 45.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma s0_hull_low : forall x k s, 0 <= x -> 0 < k -> x + k <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + k - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 45.
Proof.
intros x k s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + k - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + k - 1) / 8) / 8 <= 2 ^ 42 - 1)
  by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
(* a frame_of whose write windows lie in [lo, hi) keeps every word outside it *)
Lemma s0_frame_keep : forall E rs (m m' : word -> option byte) lo hi,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros Hin. exact (Hx (Hw _ Hin)). Qed.
(* a prefix of a byte array *)
Lemma s0_garr8_prefix : forall segs (m : word -> option byte) p l1 l2,
  garr8 segs m p (l1 ++ l2) -> garr8 segs m p l1.
Proof.
intros segs m p l1 l2 H j Hj. specialize (H j ltac:(rewrite length_app; lia)).
rewrite app_nth1 in H by exact Hj. exact H.
Qed.

(* ---- the symbolic state at tx_put's entry ---- *)
(* the shadow base the inline checks name: the atom 32, whose value is the cell's SHADOW_OFF *)
Definition S0_Bx : sv := SOff 32 0.
Definition S0_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* struct text at t = the entry a0 (atom 10): b, n, cap (8 bytes, atoms 33 / 34 / 35) and failed (4 bytes, atom 36);
   S0 writes none of them *)
Definition s0_rec : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 28 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
     YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SOff 36 0))].
(* the frame [sp0 - 112, sp0), the GOT word (A_OBJ 0) holding the shadow cell's address, the cell (A_OBJ 12) holding
   the shadow base (atom 32), the record *)
Definition s0_regions : smem := [stack_region TP_FRAME; got_regionP; bcell_regionP 32; s0_rec].
(* sp (16-aligned), t (8-aligned, its 28 bytes below 2 ^ 47), n, the shadow base, len0, failed *)
Definition s0_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (12%nat, mkAF 0 (2 ^ 28) 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (34%nat, mkAF 0 (2 ^ 28) 0); (36%nat, mkAF 0 1 0)] [] [].
Definition s0_ss : sstate := mkSS TP_OFF sr_atoms s0_regions None s0_facts.
(* the frame region after the prologue: the thirteen saved registers at sp0 - 104 .. sp0 - 8 (the engine's own
   chunk list, unchanged by every later stretch of S0) *)
Definition s0_frame_cs : list YP09.chunk :=
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition s0_frame_end : YP09.region := YP09.mkRegion (Some 2%nat) (- TP_FRAME) 0 (- TP_FRAME) 0 s0_frame_cs.
(* the register file at +168 (the need test) and at the FIT / GROW cuts: s0 = t, s1 = n, s2 = s, s3 / s4 / s5 =
   t + 8 / t + 24 / t + 16, s6 = the shadow base, s7 / s8 / s9 their shadow addresses, s10 = t >> 3, a1 = n + 1 + len0,
   a2 = cap0 *)
Definition s0_regs2 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (- TP_FRAME); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 10 0; SOff 12 0;
   SAlu ALU_ADD (SOff 12 0) (SOff 34 0); SAlu ALU_ADD (SOff 12 1) (SOff 34 0); SOff 35 0; SOff 13 0; SOff 14 0;
   SOff 15 0; SOff 16 0; SOff 17 0; SOff 11 0; SOff 10 8; SOff 10 24; SOff 10 16; SOff 32 0;
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0);
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0);
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0);
   SAlu ALU_SRL (SOff 10 0) (SLit 3); SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].

(* the write premise of a stretch: the frame window lies in the journal's window [sp0 - STK, sp0 + dw), the other
   regions are read-only *)
Ltac s0_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with |- awr_ok ?Ex (YP09.mkRegion (Some ?m) _ _ _ _ _ :: _) _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (bv_unsigned (ew Ex m) - sp0')) end;
  [reflexivity | lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].
(* the range and width side goals of chunk_ok_val *)
Ltac s0_rng := first [ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32)
  | change (Z.of_N 8) with 8 | change (Z.of_N 4) with 4 ]; lia.
(* the write windows of a stretch's regions lie in the frame *)
Ltac s0_win Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Usp in Hr; unfold TP_FRAME; lia|]);
  destruct Hin.
(* the atoms below a run's K keep their values in the run's extended env *)
Ltac s0_ew := repeat rewrite ew_ewset_other by lia.
(* the facts of the entry env (Usp / UB / Ut in context) at the env a run ends in *)
Ltac s0_newenv D HS Usp UB Ut Usp' UB' Ut' :=
  lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
    assert (Usp' : bv_unsigned (ew E' 2) = spZ (tp_regs D)) by (s0_ew; exact Usp);
    assert (UB' : U E' S0_Bx = SHADOW_OFF) by (unfold S0_Bx in *; rewrite U_SOff in *; s0_ew; exact UB);
    assert (Ut' : forall c, 0 <= c <= 28 -> U E' (SOff 10 c) = tp_t D + c)
      by (let c := fresh "c" in let Hc := fresh "Hc" in
          intros c Hc; rewrite U_SOff; s0_ew; rewrite <- U_SOff; exact (Ut c Hc))
  end.

Section s0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances TP_PrhImg TP_RL TP_PAListing.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).

(* ---- THE KEEP: a memory that agrees with the entry memory off tx_put's frame [sp0 - 112, sp0) carries every
   memory fact of tp_pre the cuts restate ---- *)
Lemma s0_keep : forall D mem1,
  tp_pre B CTX0 D -> tp_img B ->
  (forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
     mrestrict (w_H (tp_W D)) mem1 x = mrestrict (w_H (tp_W D)) (tp_mem D) x) ->
  prhtx_rec (tp_W D) mem1 (tp_t D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D) /\
  prhtx_inv B (tp_Lam D) (tp_ly D) (tp_S D) (tp_W D) mem1 (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  prhtx_place (tp_ly D) (tp_S D) (tp_W D) (tp_regs D) mem1 (tp_dw D) (tp_t D) /\
  prhtx_trace B (tp_ly D) (tp_W D) mem1 (tp_t D) /\
  src_rd (tp_W D) mem1 (tp_s D) (tp_src D) /\
  prh_ledger B (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) mem1 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D)
    (tp_most D) (tp_own D) /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H (tp_W D)) mem1).
Proof.
intros D mem1 HPRE IMG KM.
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE & HREC & HINV
  & HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVT & HBB & HREQ & HLEN).
pose proof HFP as (HAFN & HROD & HTOP64 & HRAZ).
pose proof HAFN as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof YM05.alloc_ceiling_value as Hceilv.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
lazymatch type of Hslo with _ + ?stk <= _ =>
  lazymatch eval vm_compute in stk with ?n => assert (EST : stk = n) by (vm_compute; reflexivity) end end.
unfold tp_sp0, TP_FRAME in KM.
set (sp0 := spZ (tp_regs D)) in *.
assert (AGM : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0) ->
  mrestrict (w_H (tp_W D)) mem1 (Z_to_bv 64 a) = mrestrict (w_H (tp_W D)) (tp_mem D) (Z_to_bv 64 a)).
{ intros a Ha Hn. apply KM. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0) ->
  aview segs (w_H (tp_W D)) mem1 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Ha Hn. apply aview_eq_of. exact (AGM a Ha Hn). }
assert (AGL : forall a, 0 <= a < YM05.alloc_ceiling + 8 ->
  aview segs (w_H (tp_W D)) mem1 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Ha. apply AG; lia. }
assert (AGH : forall a, sp0 <= a < 2 ^ 64 ->
  aview segs (w_H (tp_W D)) mem1 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Ha. apply AG; lia. }
assert (AGS : forall x, 0 <= x <= 2 ^ 47 ->
  aview segs (w_H (tp_W D)) mem1 (shadow_of_addr SHADOW_OFF x) =
  aview segs (w_H (tp_W D)) (tp_mem D) (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (s0_shadow_lo x Hx). apply AGL. lia. }
assert (AGI : forall a, in_img segs a ->
  aview segs (w_H (tp_W D)) mem1 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Ha. pose proof (Hsegs a Ha). unfold kLowMemEnd in *. apply AGL. lia. }
assert (AGP : forall a, Exists (in_zr a) prh_pst ->
  aview segs (w_H (tp_W D)) mem1 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Ha. exact (AGI a (tpi_pst_img B IMG a Ha)). }
split.
{ (* the record *)
  destruct HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
  refine (conj Rb (conj Rl (conj Rc (conj Rf (conj _ (conj _ (conj _ _))))))); eapply val_mem_kept;
    (try (intros k Hk; apply AGH; cbn in Hk; lia)); eassumption. }
split.
{ (* the buffer *)
  destruct HINV as (Hltxt & [Hz | (Hc0 & Hlc & Hblk & Hby & H4096 & Hceil8 & Hamr & Hbw & Hbra & Hhull & Hnl)]).
  - split; [exact Hltxt | left; exact Hz].
  - split; [exact Hltxt|]. right.
    split; [exact Hc0|]. split; [exact Hlc|]. split; [exact Hblk|].
    split.
    { unfold bytes_at in *. eapply garr8_aview_kept; [|exact Hby].
      intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply AGL. lia. }
    split; [exact H4096|]. split; [exact Hceil8|]. split; [exact Hamr|].
    split.
    { intros a Ha. eapply writable_at_eq; [|exact (Hbw a Ha)]. apply AGM; lia. }
    split.
    { eapply range_addressable_agree; [|exact Hbra]. intros x Hx. apply AGS. lia. }
    split; [|exact Hnl].
    intros s Hs. pose proof (s0_hull_low (tp_b0 D) (tp_cap0 D) s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
    rewrite AGL by lia. exact (Hhull s Hs). }
split.
{ (* the record's place *)
  split; [exact Hta|]. split; [exact Ht1|]. split; [exact Ht2|].
  split.
  { intros a Ha. eapply writable_at_eq; [|exact (Hwrit a Ha)]. apply AGM; lia. }
  eapply range_addressable_agree; [|exact Hra28]. intros x Hx. apply AGS. lia. }
split.
{ (* the frame chain the realloc call's trace reads: [t - 16, ly_top) lies above sp0 *)
  intros Hce. destruct (HTRACE Hce) as [Hp Hc]. split.
  - intros a Ha. rewrite AGH by lia. exact (Hp a Ha).
  - intros rd ch Hrd Hfp. apply (Hc rd ch); [|exact Hfp].
    intros a Ha Hn. rewrite (Hrd a Ha Hn). apply AGH. lia. }
split.
{ (* the source window *)
  destruct HSRC as (Hsby & Hs4096 & Hsceil & Hsamr & Hsra & Hshull).
  split.
  { unfold bytes_at in *. eapply garr8_aview_kept; [|exact Hsby]. intros a Ha. apply AGL. lia. }
  split; [exact Hs4096|]. split; [exact Hsceil|]. split; [exact Hsamr|].
  split.
  { eapply range_addressable_agree; [|exact Hsra]. intros x Hx. apply AGS. lia. }
  intros Hnpos s Hs. pose proof (s0_hull_low (tp_s D) (Z.of_nat (length (tp_src D))) s ltac:(lia) Hnpos ltac:(lia) Hs).
  rewrite AGL by lia. exact (Hshull Hnpos s Hs). }
split.
{ (* the ledger: the statics are image bytes, the harness heads lie in allocator blocks below the ceiling *)
  apply (prh_ledger_kept_aview B (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_ly D) (tp_S D) (tp_Hp D)
    (tp_W D) mem1 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) HLED).
  - exact AGP.
  - intros a k i Hin Hi.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED) (a, k) Hin)
      as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ (conj HAR HXS) Hab) as (_ & H4096 & Hc & _).
    pose proof (cf_head_nonneg) as Hh0.
    assert (Hrq : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    apply AGL. lia.
  - intros a k _ H. exact H.
  - apply Permutation_refl. }
(* the read-only view: image bytes *)
intros a Hro Hos Her.
assert (Him : in_img segs a).
{ destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
rewrite (AGI a Him). exact (HROD a Hro Hos Her).
Qed.


(* ---- the entry env: the registers, then the shadow base and the record's four fields as atoms 32 .. 36 ---- *)
Definition s0_E (regs : bvmap 5 word) (b0 len0 cap0 f0 : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; b0; len0; cap0; f0])).
(* what the entry env names *)
Lemma s0_E_at : forall regs b0 len0 cap0 f0,
  (forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s0_E regs b0 len0 cap0 f0) n = getr regs r) /\
  ew (s0_E regs b0 len0 cap0 f0) 32 = Z_to_bv 64 SHADOW_OFF /\ ew (s0_E regs b0 len0 cap0 f0) 33 = Z_to_bv 64 b0 /\
  ew (s0_E regs b0 len0 cap0 f0) 34 = Z_to_bv 64 len0 /\ ew (s0_E regs b0 len0 cap0 f0) 35 = Z_to_bv 64 cap0 /\
  ew (s0_E regs b0 len0 cap0 f0) 36 = Z_to_bv 64 f0.
Proof.
intros regs b0 len0 cap0 f0. unfold s0_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [intros n r Hn; pose proof (u5_range r); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r Hn)|].
split; [exact (ew_Ereg_extra _ _ 0)|]. split; [exact (ew_Ereg_extra _ _ 1)|]. split; [exact (ew_Ereg_extra _ _ 2)|].
split; [exact (ew_Ereg_extra _ _ 3) | exact (ew_Ereg_extra _ _ 4)].
Qed.
(* an atom's U value *)
Lemma s0_U_atom : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof. intros E n v c H Hv Hc. rewrite U_SOff, H, unsigned_lit_small by exact Hv. apply zcanon_id. unfold M64. lia. Qed.
Lemma s0_rd_of : forall (H : word -> bool) m, rd_of segs (mrestrict H m) = aview segs H m.
Proof. reflexivity. Qed.

(* U of the shapes the walk's registers take *)
Lemma s0_U_ewset : forall E m w (n : nat) c, (n < m)%nat -> U (ewset E m w) (SOff n c) = U E (SOff n c).
Proof. intros E m w n c Hn. rewrite !U_SOff, ew_ewset_other by lia. reflexivity. Qed.
Lemma s0_U_add : forall E a b, 0 <= U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = U E a + U E b.
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
Lemma s0_U_srl3 : forall E a, U E (SAlu ALU_SRL a (SLit 3)) = U E a / 8.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. pose proof (U_range E a) as R. unfold M64 in R.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
assert (U E a / 8 <= U E a) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
(* a register of a symbolic state whose U value is known *)
Lemma s0_reg : forall (H : word -> bool) En ss ms (r : bv 5) e v,
  st_ok_pi segs VAL En ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> U En e = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H En ss ms r e v HS He HU. rewrite (st_ok_pi_restrict_reg H En ss ms r HS), He. unfold w64. rewrite <- HU.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a word of the frame region (atom 2 = sp0) of a symbolic state *)
Lemma s0_slot : forall (H : word -> bool) En ss ms cs,
  st_ok_pi segs VAL En ss (restrict H ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (- TP_FRAME) 0 (- TP_FRAME) 0 cs) ->
  forall od e v, In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot En e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs (mrestrict H (ms_mem ms)) (bv_unsigned (ew En 2) + od) 8 v.
Proof.
intros H En ss ms cs HS Hn od e v Hin He Hv.
pose proof (st_ok_mem_ok segs En (abs_ss VAL ss) (restrict H ms) HS) as (_ & HMO & _).
assert (Hn' : nth_error (ss_mem (abs_ss VAL ss)) 0 =
  Some (YP09.mkRegion (Some 2%nat) (- TP_FRAME) 0 (- TP_FRAME) 0 cs)) by (destruct ss; exact Hn).
pose proof (proj1 (Forall_forall _ _) HMO _ (nth_error_In _ _ Hn')) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck.
exact (val_of_chunk_ok segs En _ _ od 8 e v Hck He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
  ltac:(change (Z.of_N 8) with 8; lia)).
Qed.
(* a range_addressable fact of the shadow survives a memory change off the frame (the shadow lies below 2 ^ 45) *)
Lemma s0_ra_frame : forall (W : world segs) m m' sp0 a n,
  (forall x : word, ~ (sp0 - TP_FRAME <= bv_unsigned x < sp0) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  2 ^ 45 + TP_FRAME <= sp0 -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF a n -> range_addressable (aview segs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' sp0 a n KM Hsp Ha Han H. eapply range_addressable_agree; [|exact H].
intros x Hx. pose proof (s0_shadow_lo x ltac:(lia)) as Hs. apply aview_eq_of. apply KM.
rewrite unsigned_lit_small by lia. unfold TP_FRAME in *. lia.
Qed.

Lemma s0_entry : forall D, tp_pre B CTX0 D -> tp_img B ->
  st_ok_pi segs VAL (s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) s0_ss
    (restrict (w_H (tp_W D)) (YK11.mkst (tp_regs D) (Z_to_bv 64 (BASE + TP_OFF)) (tp_mem D) (YK11.seg_rom segs))).
Proof.
intros D HPRE IMG.
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE & HREC & HINV
  & HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVT & HBB & HREQ & HLEN).
pose proof HFP as (HAFN & HROD & HTOP64 & HRAZ).
pose proof HAFN as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
pose proof YM05.alloc_ceiling_value as Hceilv.
unfold tp_need in HNEED.
lazymatch type of Hslo with _ + ?stk <= _ =>
  lazymatch eval vm_compute in stk with ?n => assert (EST : stk = n) by (vm_compute; reflexivity) end end.
pose proof (tpi_pal B IMG) as PAL.
destruct (alx_const segs B (ARcfx B) LAWS _ _ _ _ _ _ (conj HAR HXS)) as (Kcell & _ & Kgot & _).
pose proof (amc_syms _ _ _ _ _ (proj1 HAR)) as SY.
pose proof (asyms_area_bound B (as_shadow_cell B, 8) SY ltac:(cbn; tauto)) as A12.
pose proof (asyms_area_bound B (as_got_shadow B, 8) SY ltac:(cbn; tauto)) as A0.
cbn [fst snd] in A12, A0.
rewrite (palc_got_shadow B PAL), (palc_cell B PAL) in Kgot. rewrite (palc_cell B PAL) in Kcell.
rewrite (palc_got_shadow B PAL) in A0. rewrite (palc_cell B PAL) in A12.
pose proof (palc_got_cell B PAL) as HgcD.
set (E := s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s0_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat ->
  ew E k = ew (Ereg (tp_regs D) (map (Z_to_bv 64) [SHADOW_OFF; tp_b0 D; tp_len0 D; tp_cap0 D; tp_f0 D])) k)
  by (intros k Hk; unfold E, s0_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr (tp_regs D) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (tp_t D))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 (tp_n D))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (tp_b0 D)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (tp_len0 D)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (tp_cap0 D)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (tp_f0 D)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ (tp_regs D)) by (rewrite E2; reflexivity).
assert (Ut : bv_unsigned (ew E 10) = tp_t D) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Un : bv_unsigned (ew E 12) = tp_n D) by (rewrite E12; apply unsigned_lit_small; lia).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; apply HEI; exact Hj).
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply Uimg; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply Uimg; unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite restrict_mkst_fx. unfold s0_ss. apply pa_entry_st_ok_full.
- unfold E, s0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s0_regions, stack_region, got_regionP, bcell_regionP, s0_rec.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold TP_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable segs). apply Hpres. lia.
  + rewrite U0. unfold kImgEnd in A0. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12))).
    * cbn [sv_denot]. rewrite U12, Z.add_0_r. reflexivity.
    * s0_rng.
    * s0_rng.
    * rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (tp_W D)) (tp_mem D) _ _ Kgot).
  + rewrite U12. unfold kImgEnd in A12. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ _ 0 8 (SOff 32 0) SHADOW_OFF).
    * apply Dv; [exact E32 | unfold SHADOW_OFF; lia].
    * unfold SHADOW_OFF; s0_rng.
    * s0_rng.
    * rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (tp_W D)) (tp_mem D) _ _ Kcell).
  + rewrite Ut. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val segs E _ _ 0 8 (SOff 33 0) (tp_b0 D)); [apply Dv; [exact E33 | lia] | s0_rng | s0_rng |].
      rewrite Z.add_0_r. exact Mb.
    * apply (chunk_ok_val segs E _ _ 8 8 (SOff 34 0) (tp_len0 D)); [apply Dv; [exact E34 | lia] | s0_rng | s0_rng |].
      exact Ml.
    * apply (chunk_ok_val segs E _ _ 16 8 (SOff 35 0) (tp_cap0 D)); [apply Dv; [exact E35 | lia] | s0_rng | s0_rng |].
      exact Mc.
    * apply (chunk_ok_val segs E _ _ 24 4 (SOff 36 0) (tp_f0 D)); [apply Dv; [exact E36 | lia] | s0_rng | s0_rng |].
      exact Mf.
- apply pairwise_disjoint_of_extents.
  unfold s0_regions, stack_region, got_regionP, bcell_regionP, s0_rec, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Ut, U0, U12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TP_FRAME, kImgEnd in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Ut, Un, E32, E34, E36.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  pose proof (Z.div_mod (tp_t D) 8 ltac:(lia)) as Htd. rewrite Hta, Z.add_0_r in Htd.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* a symbolic state at listing offset TP_OFF + o is the cut configuration tp_cfg at o *)
Lemma s0_leaf : forall (W : world segs) E ss ms md o (G : world segs -> config -> Prop),
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = TP_OFF + o ->
  SRr segs W (tp_cfg o (ms_regs ms) (ms_mem ms) md) G -> SRr segs W (mkCfg ms md) G.
Proof.
intros W E ss ms md o G HS Hrv Hpc H.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv), Hpc.
unfold tp_cfg, tp_pc in H. rewrite Z.add_assoc. exact H.
Qed.

(* a shadow address the inline checks compute: (x >> 3) + the shadow base *)
Lemma s0_U_sh : forall E a b, U E b = SHADOW_OFF ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL a (SLit 3)) b) = SHADOW_OFF + U E a / 8.
Proof.
intros E a b Hb. pose proof (U_range E a) as R. unfold M64 in R.
assert (0 <= U E a / 8) by (apply Z.div_pos; lia).
assert (U E a / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
rewrite s0_U_add; rewrite s0_U_srl3, Hb; unfold SHADOW_OFF in *; lia.
Qed.

(* the U value of an atom below 512 at a later env of the walk is its value at the entry env *)
Lemma s0_U_En : forall En E (n : nat) c, (forall m : nat, (m < 512)%nat -> ew En m = ew E m) -> (n < 512)%nat ->
  U En (SOff n c) = U E (SOff n c).
Proof. intros En E n c HEn Hn. rewrite !U_SOff, (HEn n Hn). reflexivity. Qed.

(* ---- the register file at +168 / FIT / GROW (s0_regs2), read as the cuts state it ---- *)
Lemma s0_regs_at : forall D En ss (ms : machine_state) (H : word -> bool),
  tp_pre B CTX0 D ->
  st_ok_pi segs VAL En ss (restrict H ms) ->
  (forall n : nat, (n < 512)%nat -> ew En n = ew (s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) n) ->
  ss_regs ss = s0_regs2 ->
  tp_shregs D (ms_regs ms) /\
  getr (ms_regs ms) 11 = w64 (tp_need D) /\ getr (ms_regs ms) 12 = w64 (tp_cap0 D) /\
  getr (ms_regs ms) 19 = w64 (tp_t D + 8) /\ getr (ms_regs ms) 21 = w64 (tp_t D + 16) /\
  getr (ms_regs ms) 20 = w64 (tp_t D + 24) /\
  getr (ms_regs ms) 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) /\
  getr (ms_regs ms) 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) /\
  getr (ms_regs ms) 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8) /\ getr (ms_regs ms) 26 = w64 (tp_t D / 8).
Proof.
intros D En ss ms H HPRE HS HEn Hregs.
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE & HREC & HINV
  & HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVT & HBB & HREQ & HLEN).
pose proof HFP as (HAFN & HROD & HTOP64 & HRAZ).
pose proof HAFN as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
pose proof HSRC as (_ & Hs4096 & Hsceil & _).
pose proof YM05.alloc_ceiling_value as Hceilv.
unfold tp_need in HNEED |- *.
set (E := s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) in HEn.
destruct (s0_E_at (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) as (ER & E32 & E33 & E34 & E35 & E36).
fold E in ER, E32, E33, E34, E35, E36.
assert (Ut : forall c, 0 <= c <= 28 -> U En (SOff 10 c) = tp_t D + c).
{ intros c Hc. rewrite (s0_U_En En E 10 c HEn) by lia.
  apply (s0_U_atom E 10 (tp_t D) c); [rewrite (ER 10%nat 10%bv eq_refl); exact H10 | lia | lia]. }
assert (Un : forall c, 0 <= c <= 1 -> U En (SOff 12 c) = tp_n D + c).
{ intros c Hc. rewrite (s0_U_En En E 12 c HEn) by lia.
  apply (s0_U_atom E 12 (tp_n D) c); [rewrite (ER 12%nat 12%bv eq_refl); exact H12 | lia | lia]. }
assert (Us : U En (SOff 11 0) = tp_s D).
{ rewrite (s0_U_En En E 11 0 HEn) by lia.
  rewrite (s0_U_atom E 11 (tp_s D) 0); [lia | rewrite (ER 11%nat 11%bv eq_refl); exact H11 | lia | lia]. }
assert (UB : U En (SOff 32 0) = SHADOW_OFF).
{ rewrite (s0_U_En En E 32 0 HEn) by lia. rewrite (s0_U_atom E 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia). lia. }
assert (Ul : U En (SOff 34 0) = tp_len0 D).
{ rewrite (s0_U_En En E 34 0 HEn) by lia. rewrite (s0_U_atom E 34 (tp_len0 D) 0 E34) by lia. lia. }
assert (Uc : U En (SOff 35 0) = tp_cap0 D).
{ rewrite (s0_U_En En E 35 0 HEn) by lia. rewrite (s0_U_atom E 35 (tp_cap0 D) 0 E35) by lia. lia. }
assert (SR : forall (r : bv 5) e v, sr_get s0_regs2 r = e -> U En e = v -> getr (ms_regs ms) r = w64 v).
{ intros r e v He HU. apply (s0_reg H En ss ms r e v HS); [rewrite Hregs; exact He | exact HU]. }
split; [split; [|split; [|split]]|].
- apply (SR 22%bv (SOff 32 0)); [reflexivity | exact UB].
- apply (SR 8%bv (SOff 10 0)); [reflexivity | rewrite (Ut 0) by lia; lia].
- apply (SR 9%bv (SOff 12 0)); [reflexivity | rewrite (Un 0) by lia; lia].
- apply (SR 18%bv (SOff 11 0)); [reflexivity | exact Us].
- split; [apply (SR 11%bv (SAlu ALU_ADD (SOff 12 1) (SOff 34 0))); [reflexivity|];
          rewrite s0_U_add; rewrite (Un 1), Ul by lia; lia|].
  split; [apply (SR 12%bv (SOff 35 0)); [reflexivity | exact Uc]|].
  split; [apply (SR 19%bv (SOff 10 8)); [reflexivity | apply Ut; lia]|].
  split; [apply (SR 21%bv (SOff 10 16)); [reflexivity | apply Ut; lia]|].
  split; [apply (SR 20%bv (SOff 10 24)); [reflexivity | apply Ut; lia]|].
  split; [apply (SR 23%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0))); [reflexivity|];
          rewrite (s0_U_sh _ _ _ UB), (Ut 8) by lia; reflexivity|].
  split; [apply (SR 25%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0))); [reflexivity|];
          rewrite (s0_U_sh _ _ _ UB), (Ut 16) by lia; reflexivity|].
  split; [apply (SR 24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0))); [reflexivity|];
          rewrite (s0_U_sh _ _ _ UB), (Ut 24) by lia; reflexivity|].
  apply (SR 26%bv (SAlu ALU_SRL (SOff 10 0) (SLit 3))); [reflexivity|].
  rewrite s0_U_srl3, (Ut 0) by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* ---- THE CARRY at a cut of S0: tp_carry from the final symbolic state of a walk that wrote only the frame
   (KM), with the journal from entry the runner kept (HJ) ---- *)
Lemma s0_cut_carry : forall D En ss ms md,
  tp_pre B CTX0 D -> tp_img B ->
  st_ok_pi segs VAL En ss (restrict (w_H (tp_W D)) ms) ->
  (forall n : nat, (n < 512)%nat -> ew En n = ew (s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) n) ->
  nth_error (ss_mem ss) 0 = Some s0_frame_end ->
  sr_get (ss_regs ss) 2 = SOff 2 (- TP_FRAME) -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  tp_J B SK D (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (ms_mem ms) md 0 [] ->
  same_but_materialized (tp_md D) md ->
  (forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
     mrestrict (w_H (tp_W D)) (ms_mem ms) x = mrestrict (w_H (tp_W D)) (tp_mem D) x) ->
  tp_carry B SK CTX0 D (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (ms_regs ms) (ms_mem ms) md 0 [].
Proof.
intros D En ss ms md HPRE IMG HS HEn Hfr H2 H3 H4 HJ Hsame KM.
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE & HREC & HINV
  & HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVT & HBB & HREQ & HLEN).
pose proof HFP as (HAFN & HROD & HTOP64 & HRAZ).
pose proof HAFN as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YM05.alloc_ceiling_value as Hceilv.
lazymatch type of Hslo with _ + ?stk <= _ =>
  lazymatch eval vm_compute in stk with ?n => assert (EST : stk = n) by (vm_compute; reflexivity) end end.
destruct (s0_E_at (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) as (ER & _ & _ & _ & _ & _).
destruct (s0_keep D (ms_mem ms) HPRE IMG KM) as (_ & _ & _ & _ & _ & _ & Rod).
assert (SV : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot En (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr (tp_regs D) r))).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, (HEn n) by lia. rewrite (ER n r Hr). reflexivity. }
assert (Usp : bv_unsigned (ew En 2) = tp_sp0 D).
{ rewrite (HEn 2%nat) by lia. rewrite (ER 2%nat 2%bv eq_refl). reflexivity. }
unfold tp_carry.
split; [exact HPRE|]. split; [exact HJ|].
split.
{ unfold tp_K, tp_OR.
  eapply (cj_kept_exec (SK := SK) segs B prh_pst (ARcfx B) LAWS (@pa_segs_low _ _ PA))
    with (Wr := fun a => tp_sp0 D - TP_FRAME <= a < tp_sp0 D).
  - exact (conj HAR HXS).
  - exact Hceil.
  - unfold tp_sp0. lia.
  - unfold tp_sp0. lia.
  - exact KM.
  - intros a Ha. left. unfold tp_sp0, TP_FRAME in *. lia.
  - exact Hsame. }
split.
{ intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]].
  - rewrite (st_ok_pi_restrict_reg _ _ _ _ 3%bv HS), H3, (SV 3%nat 3%bv) by (reflexivity || lia).
    apply Z_to_bv_bv_unsigned.
  - rewrite (st_ok_pi_restrict_reg _ _ _ _ 4%bv HS), H4, (SV 4%nat 4%bv) by (reflexivity || lia).
    apply Z_to_bv_bv_unsigned. }
split.
{ unfold spZ at 1. rewrite (s0_reg _ _ _ _ 2%bv _ (tp_sp0 D - TP_FRAME) HS H2).
  - unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold tp_sp0, TP_FRAME. lia.
  - rewrite U_SOff, Usp. apply zcanon_id. unfold M64, tp_sp0, TP_FRAME. lia. }
split.
{ assert (SL : forall od (n : nat) (r : bv 5), In (YP09.mkChunk od (CVal 8 (SOff n 0))) s0_frame_cs ->
    (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
    val_mem segs (rdW (tp_W D) (ms_mem ms)) (tp_sp0 D + od) 8 (bv_unsigned (getr (tp_regs D) r))).
  { intros od n r Hin Hn Hr. rewrite <- Usp.
    apply (s0_slot _ En ss ms s0_frame_cs HS Hfr od (SOff n 0)); [exact Hin | exact (SV n r Hn Hr) |].
    exact (bv_unsigned_in_range 64 _). }
  unfold tp_saved, raZ.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- val_mem _ _ (tp_sp0 D - ?o) _ (bv_unsigned (getr _ ?r)) =>
    replace (tp_sp0 D - o) with (tp_sp0 D + - o) by lia;
    apply (SL (- o) (Z.to_nat (bv_unsigned r)) r);
    [unfold s0_frame_cs; cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; lia | vm_compute; reflexivity]
  end. }
split; [reflexivity | exact Rod].
Qed.

(* ---- the cuts after the GROW's realloc (FIT, END) carry the journal and the keep at wle' segs RZ_cf: S0 runs at one
   world (no allocator call), so its plain carry lifts (YA0nH.wle_wle') ---- *)
Lemma s0_carry_lift : forall D ly3 S3 Hp3 (W3 : world segs) regs3 mem3 md3 k WS,
  tp_carry B SK CTX0 D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS ->
  tp_carryR B SK CTX0 (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS.
Proof.
intros D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS (HP & HJ & HK & HR).
split; [exact HP|]. split.
- unfold tp_JR. unfold tp_J in HJ.
  exact (ajournal_xwR_mono (SK := SK) segs B prh_pst (ARcfx B) (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
    (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJ).
- split; [|exact HR]. unfold tp_KR. unfold tp_K in HK.
  destruct HK as (K1 & K2 & K3 & K4).
  exact (conj K1 (conj K2 (conj (wle_wle' segs YGcfRehidePost.RZ_cf _ _ K3) K4))).
Qed.

Lemma tp_seg_S0_holds : forall P, srr_inv_laws segs P -> tp_seg_S0 B SK CTX0 P.
Proof.
intros P PLAW Q D HPRE HK1 IMG KEND KFIT KGROW HPM.
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE & HREC & HINV
  & HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVT & HBB & HREQ & HLEN).
pose proof HFP as (HAFN & HROD & HTOP64 & HRAZ).
pose proof HAFN as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
pose proof YM05.alloc_ceiling_value as Hceilv.
unfold tp_need in HNEED.
lazymatch type of Hslo with _ + ?stk <= _ =>
  lazymatch eval vm_compute in stk with ?n => assert (EST : stk = n) by (vm_compute; reflexivity) end end.
pose proof (s0_entry D HPRE IMG) as HS.
pose proof (ajournal_x_init_W (SK := SK) segs B prh_pst (ARcfx B) STK_tx_put (tp_dw D) (tp_FP D) (tp_ly D) (tp_S D)
  (tp_Hp D) (tp_W D) (tp_regs D) (tp_mem D) (tp_md D) (tp_ch D) HAFN
  ltac:(unfold fwin in HFWIN; unfold fwin_x; exact HFWIN)) as HJ.
set (E := s0_E (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s0_E; apply Eimg_env).
assert (SHOK : sh_ok segs S0_Bx [] E (mrestrict (w_H (tp_W D)) (tp_mem D))) by (unfold sh_ok; apply Forall_nil).
change (P (tp_mem D)) in HPM.
destruct (s0_E_at (tp_regs D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D)) as (ER & E32 & E33 & E34 & E35 & E36).
fold E in ER, E32, E33, E34, E35, E36.
assert (Hn28 : 0 <= tp_n D <= 2 ^ 28) by lia.
assert (Usp : bv_unsigned (ew E 2) = spZ (tp_regs D)) by (rewrite (ER 2%nat 2%bv eq_refl); reflexivity).
assert (Ut : forall c, 0 <= c <= 28 -> U E (SOff 10 c) = tp_t D + c).
{ intros c Hc. apply (s0_U_atom E 10 (tp_t D) c); [rewrite (ER 10%nat 10%bv eq_refl); exact H10 | lia | lia]. }
assert (UB : U E S0_Bx = SHADOW_OFF).
{ unfold S0_Bx. rewrite (s0_U_atom E 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia). lia. }
assert (Uf : U E (SOff 36 0) = tp_f0 D) by (rewrite (s0_U_atom E 36 (tp_f0 D) 0 E36) by lia; lia).
assert (Uc : U E (SOff 35 0) = tp_cap0 D) by (rewrite (s0_U_atom E 35 (tp_cap0 D) 0 E35) by lia; lia).
assert (Ul : U E (SOff 34 0) = tp_len0 D) by (rewrite (s0_U_atom E 34 (tp_len0 D) 0 E34) by lia; lia).
assert (Un : forall c, 0 <= c <= 1 -> U E (SOff 12 c) = tp_n D + c).
{ intros c Hc. apply (s0_U_atom E 12 (tp_n D) c); [rewrite (ER 12%nat 12%bv eq_refl); exact H12 | lia | lia]. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_txp_A) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_txp_A) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW).
pose (BR := paj_branch (L := A_prog_listing) (PI := PA)).
unfold tp_cfg0, cfg_at. rewrite (tpi_entry B IMG). change (w64 (BASE + TP_OFF)) with (Z_to_bv 64 (BASE + TP_OFF)).
(* the run is plain SRr (no allocator call), lifted once into SRr' segs RZ_cf, the continuations' relation *)
apply (YGcfRhLift.ra_rh_of_SRr segs YGcfRehidePost.RZ_cf).
(* ---- +0 .. +104: the prologue, the GOT pair, the shadow base, the 4-byte check of t + 24 (slow path +420 taken
   back to +100 when the shadow byte k satisfies 3 < k), `lw a0, 0(s4)` = failed; stops at `bnez a0` ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM S0_Bspan.
{ cbn [ms_mem YK11.mkst]. rewrite s0_rd_of, UB, (Ut 24) by lia.
  apply (range_addressable_sub _ SHADOW_OFF (tp_t D) 28 (tp_t D + 24) 4 Hra28); lia. }
{ s0_awr. }
rename HF into HF1, HFr into HFr1, HG into HG1.
pose proof (s0_frame_keep _ _ _ _ (spZ (tp_regs D) - TP_FRAME) (spZ (tp_regs D)) HFr1 ltac:(s0_win Usp)) as KM1.
s0_newenv D HS Usp UB Ut Usp1 UB1 Ut1.
psrr_branch_tok RUN BR HS SHOK S0_Bspan.
- (* +104 TAKEN: failed <> 0, straight to the epilogue (A0 FAILED AT ENTRY) *)
  rename Hc into Hf0c.
  assert (Hf0 : tp_f0 D <> 0).
  { rewrite branch_ne_U in Hf0c. repeat rewrite s0_U_ewset in Hf0c by lia. rewrite Uf, U_SLit in Hf0c.
    change (zcanon 0) with 0 in Hf0c. apply negb_true_iff, Z.eqb_neq in Hf0c. exact Hf0c. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM S0_Bspan (TP_OFF + TP_PC_END).
  { s0_awr. }
  rename HF into HF3, HFr into HFr3, HG into HG3.
  pose proof (s0_frame_keep _ _ _ _ (spZ (tp_regs D) - TP_FRAME) (spZ (tp_regs D)) HFr3 ltac:(s0_win Usp1)) as KM3.
  lazymatch type of HS with st_ok_pi _ _ ?En ?ss (restrict _ ?msF) =>
    assert (KMF : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
      mrestrict (w_H (tp_W D)) (ms_mem msF) x = mrestrict (w_H (tp_W D)) (tp_mem D) x)
      by (intros x Hx; unfold tp_sp0 in Hx; rewrite (KM3 x Hx); exact (KM1 x Hx));
    assert (HEn : forall n : nat, (n < 512)%nat -> ew En n = ew E n) by (intros n Hn; s0_ew; reflexivity);
    pose proof (s0_cut_carry D En ss msF _ HPRE IMG HS HEn ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ
      (with_vm_backing_same _ _) KMF) as HCAR;
    apply (s0_leaf (tp_W D) En ss msF _ TP_PC_END _ HS eq_refl ltac:(vm_compute; reflexivity))
  end.
  apply SRr_ret. cbv beta.
  apply (KEND (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) _ _ _ 0); [|exact HPM].
  exists []. split; [exact (tp_budget_nil D)|].
  split; [exact (s0_carry_lift _ _ _ _ _ _ _ _ _ _ HCAR)|].
  (* the text's post body, FAILED AT ENTRY: nothing written, f1 = f0, own' = own, pre = [] *)
  destruct (s0_keep D _ HPRE IMG KMF) as (KRec & KInv & KPlace & KTrace & KSrc & KLed & KRod).
  exists (tp_b0 D), (tp_cap0 D), (tp_f0 D), (tp_own D), (@nil Z).
  cbn [length Z.of_nat]. rewrite Z.add_0_r, app_nil_r.
  split.
  { split; [exact KRec|]. split; [exact KInv|]. split; [exact KPlace|]. split; [reflexivity|].
    split; [left; split; [reflexivity | split; reflexivity] | lia]. }
  split; [right; left; split; [exact Hf0 | repeat split]|].
  split; [intros Hz; exfalso; exact (Hf0 Hz)|].
  split; [exact (proj1 KSrc)|].
  split; [exact HRL|].
  split; [intros Hz; exfalso; exact (Hf0 Hz)|].
  split; [intros _; exact HPOS|].
  exact KLed.
- (* +104 NOT TAKEN: failed = 0; the checks of t + 8 and t + 16, the need test *)
  rename Hc into Hf0n.
  assert (Hf0 : tp_f0 D = 0).
  { rewrite branch_ne_U in Hf0n. repeat rewrite s0_U_ewset in Hf0n by lia. rewrite Uf, U_SLit in Hf0n.
    change (zcanon 0) with 0 in Hf0n. apply negb_false_iff, Z.eqb_eq in Hf0n. exact Hf0n. }
  paj_run_tok_x_inv RUN HS HJ SHOK HPM S0_Bspan.
  { rewrite s0_rd_of, UB1, (Ut1 16) by lia.
    apply (s0_ra_frame (tp_W D) (tp_mem D) (ms_mem ms) (spZ (tp_regs D))); [exact KM1 | unfold TP_FRAME; lia | lia | lia |].
    apply (range_addressable_sub _ SHADOW_OFF (tp_t D) 28 (tp_t D + 16) 8 Hra28); lia. }
  { rewrite s0_rd_of, UB1, (Ut1 8) by lia.
    apply (s0_ra_frame (tp_W D) (tp_mem D) (ms_mem ms) (spZ (tp_regs D))); [exact KM1 | unfold TP_FRAME; lia | lia | lia |].
    apply (range_addressable_sub _ SHADOW_OFF (tp_t D) 28 (tp_t D + 8) 8 Hra28); lia. }
  { s0_awr. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  pose proof (s0_frame_keep _ _ _ _ (spZ (tp_regs D) - TP_FRAME) (spZ (tp_regs D)) HFr2 ltac:(s0_win Usp1)) as KM2.
  s0_newenv D HS Usp1 UB1 Ut1 Usp2 UB2 Ut2.
  psrr_branch_tok RUN BR HS SHOK S0_Bspan.
  + (* +168 TAKEN: len0 + n + 1 <= cap0, the buffer fits (FIT) *)
    rename Hc into Hfit.
    rewrite branch_geu_U in Hfit.
    rewrite (s0_U_add _ (SOff 12 1) (SOff 34 0)) in Hfit
      by (repeat rewrite s0_U_ewset by lia; rewrite (Un 1), Ul by lia; lia).
    repeat rewrite s0_U_ewset in Hfit by lia. rewrite Uc, (Un 1), Ul in Hfit by lia.
    apply negb_true_iff, Z.ltb_ge in Hfit.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM S0_Bspan (TP_OFF + TP_PC_FIT).
    { s0_awr. }
    rename HF into HF4, HFr into HFr4, HG into HG4.
    pose proof (s0_frame_keep _ _ _ _ (spZ (tp_regs D) - TP_FRAME) (spZ (tp_regs D)) HFr4 ltac:(s0_win Usp2)) as KM4.
    lazymatch type of HS with st_ok_pi _ _ ?En ?ss (restrict _ ?msF) =>
      assert (KMF : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
        mrestrict (w_H (tp_W D)) (ms_mem msF) x = mrestrict (w_H (tp_W D)) (tp_mem D) x)
        by (intros x Hx; unfold tp_sp0 in Hx; rewrite (KM4 x Hx), (KM2 x Hx); exact (KM1 x Hx));
      assert (HEn : forall n : nat, (n < 512)%nat -> ew En n = ew E n) by (intros n Hn; s0_ew; reflexivity);
      pose proof (s0_cut_carry D En ss msF _ HPRE IMG HS HEn ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ
        (with_vm_backing_same _ _) KMF) as HCAR;
      pose proof (s0_regs_at D En ss msF _ HPRE HS HEn ltac:(vm_compute; reflexivity))
        as (RSH & R11 & R12 & R19 & R21 & R20 & R23 & R25 & R24 & R26);
      apply (s0_leaf (tp_W D) En ss msF _ TP_PC_FIT _ HS eq_refl ltac:(vm_compute; reflexivity))
    end.
    apply SRr_ret. cbv beta.
    apply (KFIT (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) _ _ _ 0 (tp_b0 D) (tp_cap0 D)); [|exact HPM].
    destruct (s0_keep D _ HPRE IMG KMF) as (KRec & KInv & KPlace & KTrace & KSrc & KLed & KRod).
    destruct KInv as (Hltxt & [(Hc0 & _ & _) | (Hcp & Hlc & Hblk & Hby & H4096 & Hbceil & Hamr & Hbw & Hbra & Hhull
      & Hnl)]); [exfalso; lia|].
    (* the buffer's + 8 margin: the batch-kit prhtx_inv states the block below the ceiling only; the margin is the
       allocator's (AR_laws_x's alx_blocks_ceil8, F21b), at the entry state where the block is live *)
    assert (Hceil8 : tp_b0 D + tp_cap0 D + 8 <= YM05.alloc_ceiling).
    { pose proof (alx_blocks_ceil8 segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ (conj HAR HXS) Hblk) as X.
      unfold req_size in X. destruct (Z.eqb_spec (tp_cap0 D) 0); lia. }
    exists []. split; [exact (tp_budget_nil D)|].
    split; [exact (s0_carry_lift _ _ _ _ _ _ _ _ _ _ HCAR)|]. split; [exact RSH|]. split; [exact Hf0|].
    split; [exact R19|]. split; [exact R21|]. split; [exact R23|]. split; [exact R25|]. split; [exact R26|].
    split; [unfold tp_recat; rewrite Hf0 in KRec; exact KRec|].
    split; [exact (conj Hcp (conj Hblk (conj H4096 (conj Hceil8 (conj Hamr (conj Hbw (conj Hbra (conj Hhull Hnl))))))))|].
    split; [unfold bytes_at in *; exact (s0_garr8_prefix segs _ _ _ _ Hby)|].
    split; [unfold tp_need; lia|].
    split; [intros a Ha; exact (proj2 (HDISJ a Ha))|].
    split; [exact HKEPT|].
    split; [left; split; [unfold tp_need; lia | repeat split]|].
    split; [split; [exact KLed | split; [exact KSrc | exact HRL]]|].
    split; [intros _ _ Hlt; exfalso; unfold tp_need in Hlt; lia | intros _; exact HPOS].
  + (* +168 NOT TAKEN: cap0 < len0 + n + 1, on to the grow block (GROW) *)
    rename Hc into Hgrow.
    rewrite branch_geu_U in Hgrow.
    rewrite (s0_U_add _ (SOff 12 1) (SOff 34 0)) in Hgrow
      by (repeat rewrite s0_U_ewset by lia; rewrite (Un 1), Ul by lia; lia).
    repeat rewrite s0_U_ewset in Hgrow by lia. rewrite Uc, (Un 1), Ul in Hgrow by lia.
    apply negb_false_iff, Z.ltb_lt in Hgrow.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM S0_Bspan (TP_OFF + TP_PC_GROW).
    { s0_awr. }
    rename HF into HF4, HFr into HFr4, HG into HG4.
    pose proof (s0_frame_keep _ _ _ _ (spZ (tp_regs D) - TP_FRAME) (spZ (tp_regs D)) HFr4 ltac:(s0_win Usp2)) as KM4.
    lazymatch type of HS with st_ok_pi _ _ ?En ?ss (restrict _ ?msF) =>
      assert (KMF : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
        mrestrict (w_H (tp_W D)) (ms_mem msF) x = mrestrict (w_H (tp_W D)) (tp_mem D) x)
        by (intros x Hx; unfold tp_sp0 in Hx; rewrite (KM4 x Hx), (KM2 x Hx); exact (KM1 x Hx));
      assert (HEn : forall n : nat, (n < 512)%nat -> ew En n = ew E n) by (intros n Hn; s0_ew; reflexivity);
      pose proof (s0_cut_carry D En ss msF _ HPRE IMG HS HEn ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ
        (with_vm_backing_same _ _) KMF) as HCAR;
      pose proof (s0_regs_at D En ss msF _ HPRE HS HEn ltac:(vm_compute; reflexivity))
        as (RSH & R11 & R12 & R19 & R21 & R20 & R23 & R25 & R24 & R26);
      apply (s0_leaf (tp_W D) En ss msF _ TP_PC_GROW _ HS eq_refl ltac:(vm_compute; reflexivity))
    end.
    apply SRr_ret. cbv beta.
    apply (KGROW (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) _ _ _ 0); [|exact HPM].
    destruct (s0_keep D _ HPRE IMG KMF) as (KRec & KInv & KPlace & KTrace & KSrc & KLed & KRod).
    split; [exact HK1|].
    split; [exact HCAR|]. split; [exact RSH|]. split; [exact Hf0|]. split; [unfold tp_need; lia|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact R11|]. split; [exact R12|]. split; [exact R19|]. split; [exact R21|]. split; [exact R20|].
    split; [exact R23|]. split; [exact R25|]. split; [exact R24|]. split; [exact R26|].
    split; [unfold tp_recat; rewrite Hf0 in KRec; exact KRec|].
    split; [exact KInv|]. split; [exact KTrace|].
    split; [exact KLed | split; [exact KSrc | exact HRL]].
Qed.

End s0.

Print Assumptions tp_seg_S0_holds.
