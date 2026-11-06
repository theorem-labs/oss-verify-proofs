(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segA: the ENTRY segment of the image-B (asan-ubsan) walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, i.e. llvm_b_entry_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v: offsets
   +0x000..+0x070 of the listing lib/B/Prog/DecodeBList.v, ending at the return of __asan_stack_malloc_0, whose
   post is llvm_b_st_074.

   The code (DecodeBList.v slots 0..28, decoded from the audited listing):
     +0x000 addi sp,sp,-224      +0x004 sd zero,0(sp)      +0x008..+0x038 the 13 callee-saved stores
     +0x03c addi s0,sp,224       +0x040 andi sp,sp,-32      +0x044 mv s1,sp      +0x048 mv s3,a1
     +0x04c..+0x058 the two GOT loads (objects 0 / 1 of lib/B/Prog/DecodeBAddr.v through the auipc values 0 / 1)
     +0x05c lw a2,0(a2)  (the use-after-return flag cell, object 15)
     +0x060 ld s2,0(a1)  (the shadow base cell, object 14)      +0x064 mv s8,a0
     +0x068 beqz a2,+0x7c         +0x06c li a0,64              +0x070 jal __asan_stack_malloc_0
   The one branch of the segment, +0x068, is refuted: dec_crt_cells pins the flag cell
   (lib/B/AsanCells.v UAR) to 1, so a2 is 1 and the branch is not taken. No other branch leaves the segment,
   and the segment reaches no report or trap block.

   Two pieces the shared kit does not carry are proved here, for this file only:
   - dec_ceff_journal: lib/Reusable/YCbq.v:858 call_effect_journal with the caller's write set given as the
     call's stack window alone instead of ascratch (the window OR the errno cell). __asan_stack_malloc_0's
     own post (lib/Reusable/YG0d.v:298) keeps every byte outside the window and the owned bytes, errno
     included, so the weaker hypothesis is the one the call gives; and with it the proof no longer needs
     `api_env segs B`, which the fixed statement dec_llvmf_holds_stmt
     (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:212-246) does not carry. The text is YCbq's, clause for clause,
     with the errno case of each clause removed.
   - dec_aj_stack_malloc: lib/A/Prog/YC85.v:291 aj_stack_malloc_atS over dec_ceff_journal, so with the same
     premises less api_env, and with the post stating the call's own frame condition in place of acall_kept.
   Everything else is the kit: the Pa run of lib/A/Prog/PaRun.v through lib/B/Prog/DecodeBPaLib.v's
   paj_run_to / paj_branch, and lib/Reusable/YCbq.v's ajournal_init and ajournal_sub.

   Templates: cgif_file_fuzzer's entry walk lib/A/ACez.v and its entry state lib/A/ACf5.v (origin/ossv/recipes
   c8557374ad2e), boxreg's lib/A/Prog/ReadName.v (a working branch). sp1_facts,
   land_m32 and denot_and_m32 below are cgif lib/A/ACer.v:140-166, copied because fuzz_decode's kit has no
   `andi sp,sp,-32` lemma. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.AsanCells.

(* ------------------------------------------------------------------ *)
(* 1. `andi sp, sp, -32` (cgif lib/A/ACer.v:140-166)                    *)
(* ------------------------------------------------------------------ *)

Lemma dec_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma dec_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma dec_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite dec_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* `mv s1,sp` right after the realign (+0x044). *)
Lemma dec_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv.
assert (Hq : 0 <= 32 * ((v + c) / 32) < 2 ^ 64).
{ split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite dec_land_m32 by lia.
rewrite (zcanon_id (32 * ((v + c) / 32))) by (rewrite M64_val; lia).
rewrite (zcanon_id 0) by (rewrite M64_val; lia). rewrite Z.add_0_r.
apply zcanon_id. rewrite M64_val. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The journal of the one call, without api_env                      *)
(* ------------------------------------------------------------------ *)

Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* YCbq.v:858 call_effect_journal, clause for clause, with the call's write set given as its stack window
   alone: the errno cell is not in it, so the proof needs neither ERRIMG nor api_env. *)
Lemma dec_ceff_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 (Eb : Z -> Prop) FP1 nf k1,
AR segs B ly2 S2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
 ~ (spZ regs - stk <= a < spZ regs) -> ~ Eb a ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
AR segs B lyc Sc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
 b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
ajournal segs B stk (spZ regs) FP1 lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 Eb FP1 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> ~ Eb a -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H5 H6. exact (Hfr a H6 H1 H2 H3 H5). }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|].
split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{ intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- intros He. destruct (HE a He) as (b & m & Hbm & Hr & _). pose proof (BLK b m a Hbm Hr). zlia.
- zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- intros He. destruct (HE _ He) as (b & m & Hbm & Hr & [Hf | Hnot]); [exact (Hnf Hf)|].
destruct Hbm as [Hbm|Hbm]; [exact (Hnot Hbm)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks segs B LAWS ly2 S2 W2 mem2 md2 b m p n HAR2 Hbm H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia. }
split.
{ intros a Hi Hns He _. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- intros Heb. destruct (HE a Heb) as (b & m & Hbm & Hr & _).
destruct Hbm as [Hbm|Hbm];
[exact (blk_img segs B LAWS _ _ _ _ _ b m a HAR Hbm Hr Hi) | exact (blk_img segs B LAWS _ _ _ _ _ b m a HAR2 Hbm Hr Hi)].
- zlia. }
split.
{ intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia.
exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia.
exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- intros Heb. destruct (HE a Heb) as (b & m & Hbm & Hrb & _). pose proof (BLK b m a Hbm Hrb).
destruct Hr as [Hr|Hr]; [|zlia].
destruct Hbm as [Hbm|Hbm].
+ pose proof (sep_block_frame segs B LAWS lyc Sc W memc mdc b m cid pos HAR Hbm Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
+ pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 b m cid pos HAR2 Hbm Hin2) as Hd. rewrite Efa in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- destruct Hr as [Hr|Hr]; zlia. }
split; [exact Hgone|]. split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
{ intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (AR_extra_law_ok segs B lyc Sc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (AR_extra_law_ok segs B ly2 S2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- intros Heb. destruct (HE a Heb) as (b & m & [Hbm|Hbm] & Hr & _); [exact (Xb b m Hbm Hr) | exact (Yb b m Hbm Hr)].
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.
End cj.

(* ------------------------------------------------------------------ *)
(* 3. The class-0 stack malloc as one journal step                      *)
(* ------------------------------------------------------------------ *)

Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.

(* lib/A/Prog/YC85.v:291 aj_stack_malloc_atS over dec_ceff_journal: the same step without api_env, and with
   the call's own frame condition (lib/Reusable/YG0d.v:298) in place of acall_kept. *)
Lemma dec_aj_stack_malloc : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
(exists f, S2 = set_fs f Sc)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (SMP Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (dec_ceff_journal segs B LAWS segs_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. exact (Hfr a H0 H1 H2 H3).
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1. split; [|exists f; exact ES2].
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End sm.

(* ------------------------------------------------------------------ *)
(* 3b. Memory helpers (image A's twin file, lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v:100-157)     *)
(* ------------------------------------------------------------------ *)

Section mh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma dec_rdword_of_val_mem : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (BY : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (BY 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (BY 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (BY 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (BY 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (BY 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (BY 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (BY 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (BY 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma dec_val_mem_moved : forall segs H H' (m m' : word -> option byte) a b n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros segs H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma garr8_kept : forall segs H H' (m m' : word -> option byte) base l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros segs H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (dec_val_mem_moved segs H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma saved_slot : forall segs E m n cs lo hi wlo whi off (r : nat) b,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk off (CVal 8 (SOff r 0))) cs ->
val_mem segs m (b + off) 8 (bv_unsigned (ew E r)).
Proof.
intros segs E m n cs lo hi wlo whi off r b HR Hb Hc.
pose proof (bv_unsigned_in_range 64 (ew E r)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
exact (field_of_region E m n b cs lo hi wlo whi off 8 (SOff r 0) (bv_unsigned (ew E r)) HR Hb Hc
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
End mh.

Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; awr_ro_rec ].
(* The value of register r in the machine state of a symbolic state HS. *)
Ltac reg_at HS r v H tac :=
  lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* 4. The entry symbolic state                                          *)
(* ------------------------------------------------------------------ *)

(* The two runtime cells the prologue reads besides the shadow base: the GOT word of the
   use-after-return flag (object 0) and the flag cell itself (object 15), whose value 1 is what refutes
   the branch at +0x068. cgif's uar_got_region / uar_cell_region, lib/A/ACem.v:57-60. *)
Definition dec_uar_got_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 15) 0))].
Definition dec_uar_cell_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 15)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
(* Slot 32 is the shadow base, as every walk of this unit names it. *)
Definition dec_extra : list word := [Z_to_bv 64 SB].
Definition dec_entry_regions : smem :=
  [stack_region 224; got_regionP; bcell_regionP 32; dec_uar_got_region; dec_uar_cell_region].
Definition dec_entry_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_dec_entry : sstate :=
  mkSS AF_LLVMFuzzerTestOneInput sr_atoms dec_entry_regions None dec_entry_facts.

Section entry. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PIB := (@PI_decodeb rc).
#[local] Notation SEGS := (@pa_segs rc decodeb_listing PIB).
#[local] Notation VAL := (@pa_val rc decodeb_listing PIB).
#[local] Notation BASE := (@pa_val rc decodeb_listing PIB A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegsB0 B.

Lemma dec_val_mem_of_rd32 : forall (H : word -> bool) mem a v,
  rd32 (aview decodesegsB0 H mem) a v -> val_mem decodesegsB0 (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk.
destruct (aview_byte decodesegsB0 H mem (a + Z.of_nat k) (le_byte v 4 k) (Hr k Hk)) as (b & Hb & Hv & Hrng).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite <- Hv. symmetry. apply Z.mod_small. lia.
Qed.

(* The four runtime cells the prologue reads, at the listing's own object addresses: from dec_crt_cells
   through AR's am_const (lib/Reusable/YG0n.v:211), as lib/Reusable/YG0s.v:69-81 reads the four cells
   asyms_ok fixes. *)
Lemma dec_cells_of_AR : forall ly S (W : world decodesegsB0) mem md,
  dec_crt_cells B -> AR decodesegsB0 B ly S W mem md ->
  rdword (aview decodesegsB0 (w_H W) mem) DCells.GOT_CELL_K = Some DCells.CELL_K /\
  rdword (aview decodesegsB0 (w_H W) mem) DCells.CELL_K = Some DCells.ASAN_K /\
  rdword (aview decodesegsB0 (w_H W) mem) DCells.GOT_UAR = Some DCells.UAR /\
  rd32 (aview decodesegsB0 (w_H W) mem) DCells.UAR 1.
Proof.
intros ly S W mem md HC HAR. pose proof HAR as (M & _ & _).
pose proof (am_const _ _ _ _ M) as Cst.
destruct (HC ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
assert (F := fun c (H : In c (as_const B ly)) => proj1 (Forall_forall _ _) Cst c H).
split; [eapply (rdword_cell B); [unfold DCells.CELL_K; lia | exact (F _ I2)]|].
split; [eapply (rdword_cell B); [unfold DCells.ASAN_K; lia | exact (F _ I1)]|].
split; [eapply (rdword_cell B); [unfold DCells.UAR; lia | exact (F _ I7)]|].
pose proof (F _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
intros k Hk. exact (H6 k Hk).
Qed.

(* The entry state of the walk: the registers as they arrive, the own 224-byte frame, and the four
   runtime cells as read-only regions. cgif's rt_entry, lib/A/ACf5.v:187. *)
Lemma dec_entry_st : forall ly S (W : world decodesegsB0) regs mem md,
  dec_crt_cells B ->
  afn_pre decodesegsB0 B DEC_LLVMF_STK ly S W regs mem md [] ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs dec_extra)) ss_dec_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md HC HFN.
pose proof HFN as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
destruct (dec_cells_of_AR ly S W mem md HC HAR) as (Kgot & Kcell & Kguar & Kuar).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dec_extra)).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs dec_extra) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (V0 : VAL (A_OBJ 0) = DCells.GOT_UAR) by (vm_compute; reflexivity).
assert (V1 : VAL (A_OBJ 1) = DCells.GOT_CELL_K) by (vm_compute; reflexivity).
assert (V14 : VAL (A_OBJ 14) = DCells.CELL_K) by (vm_compute; reflexivity).
assert (V15 : VAL (A_OBJ 15) = DCells.UAR) by (vm_compute; reflexivity).
assert (E0o : ew E (A_OBJ 0) = Z_to_bv 64 DCells.GOT_UAR)
  by (subst E; rewrite <- V0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 DCells.GOT_CELL_K)
  by (subst E; rewrite <- V1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E14o : ew E (A_OBJ 14) = Z_to_bv 64 DCells.CELL_K)
  by (subst E; rewrite <- V14; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E15o : ew E (A_OBJ 15) = Z_to_bv 64 DCells.UAR)
  by (subst E; rewrite <- V15; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = DCells.GOT_UAR)
  by (rewrite E0o; apply unsigned_lit_small; unfold DCells.GOT_UAR; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = DCells.GOT_CELL_K)
  by (rewrite E1o; apply unsigned_lit_small; unfold DCells.GOT_CELL_K; lia).
assert (U14 : bv_unsigned (ew E (A_OBJ 14)) = DCells.CELL_K)
  by (rewrite E14o; apply unsigned_lit_small; unfold DCells.CELL_K; lia).
assert (U15 : bv_unsigned (ew E (A_OBJ 15)) = DCells.UAR)
  by (rewrite E15o; apply unsigned_lit_small; unfold DCells.UAR; lia).
unfold ss_dec_entry. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dec_entry_regions, stack_region, got_regionP, bcell_regionP, dec_uar_got_region, dec_uar_cell_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [zone_lia|]. split; [zone_lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable decodesegsB0). apply Hpres. rewrite FFS in Hslo. zone_lia.
  + rewrite U1. split; [unfold DCells.GOT_CELL_K; lia|]. split; [unfold DCells.GOT_CELL_K; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val decodesegsB0 E _ DCells.GOT_CELL_K 0 8 (SOff (A_OBJ 14) 0) DCells.CELL_K);
    [cbn [sv_denot]; rewrite E14o, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold DCells.CELL_K; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword decodesegsB0 (w_H W) mem _ _ Kgot).
  + rewrite U14. split; [unfold DCells.CELL_K; lia|]. split; [unfold DCells.CELL_K; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val decodesegsB0 E _ DCells.CELL_K 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword decodesegsB0 (w_H W) mem _ _ Kcell).
  + rewrite U0. split; [unfold DCells.GOT_UAR; lia|]. split; [unfold DCells.GOT_UAR; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val decodesegsB0 E _ DCells.GOT_UAR 0 8 (SOff (A_OBJ 15) 0) DCells.UAR);
    [cbn [sv_denot]; rewrite E15o, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold DCells.UAR; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword decodesegsB0 (w_H W) mem _ _ Kguar).
  + rewrite U15. split; [unfold DCells.UAR; lia|]. split; [unfold DCells.UAR; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val decodesegsB0 E _ DCells.UAR 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (dec_val_mem_of_rd32 (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold dec_entry_regions, stack_region, got_regionP, bcell_regionP, dec_uar_got_region,
    dec_uar_cell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
  rewrite Usp, U0, U1, U14, U15.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold DCells.GOT_UAR, DCells.GOT_CELL_K, DCells.CELL_K, DCells.UAR.
  rewrite FFS in Hslo. repeat split; zone_lia.
- split; [|split; [exact I | exact I]].
  cbn [dec_entry_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, USB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite FFS in Hslo.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; zone_lia.
Qed.

Variable MT : ameter_ops.
Definition DEN (regs : bvmap 5 word) : env := Eimg (PI := PIB) (Ereg regs dec_extra).
(* One saved word of dec_b_saved: the run stored it in the machine-stack region HR0 (the chunk at -off holds
   atom r, the entry value of register r), and the stack malloc kept it (HKS). *)
Ltac saved_tac HR0 HKS EE Usp msv regsv W :=
  lazymatch goal with |- rdword _ (spZ regsv - ?off) = Some (bv_unsigned (YK11.getr regsv (Z_to_bv 5 ?r))) =>
    let rn := eval vm_compute in (Z.to_nat r) in
    rewrite (rdword_kept (aview decodesegsB0 (w_H W) (ms_mem msv)) _ (spZ regsv - off))
      by (intros i Hi; apply HKS; lia);
    rewrite <- (EE rn (Z_to_bv 5 r) eq_refl);
    apply dec_rdword_of_val_mem;
    [ replace (spZ regsv - off) with (spZ regsv + (- off)) by lia;
      eapply (saved_slot _ _ _ _ _ _ _ _ _ (- off) rn (spZ regsv) HR0 Usp);
      cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
    | let w := fresh "w" in pose proof (bv_unsigned_in_range 64 (ew (DEN regsv) rn)) as w;
      change (bv_modulus 64) with (2 ^ 64) in w; exact w ]
  end.

(* +0x000 .. +0x070 and the return of __asan_stack_malloc_0 at +0x074: the segment's whole run. *)
Lemma dec_entry_walk :
  pc_stack_malloc (as_code B) 0 = decodeb_sigma DB___asan_stack_malloc_0 ->
  dec_crt_cells B ->
  model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B ->
  @astack_malloc_realizes fx rc decodesegsB0 B 0 ->
  forall ly S (W : world decodesegsB0) regs mem md p n pl M (XL : Z -> Z),
    afn_pre decodesegsB0 B DEC_LLVMF_STK ly S W regs mem md [] ->
    YK11.getr regs 10 = w64 p -> YK11.getr regs 11 = w64 n ->
    0 <= n < 2 ^ 26 -> (0 < n -> In (p, n) (ablocks B ly S)) ->
    n = Z.of_nat (length pl) ->
    garr8 decodesegsB0 (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
    frames S = [] -> mo_ok MT S (XL n) -> frm_zero (@fp_csr fx) ->
    (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
    SRr decodesegsB0 W (@cfg_at fx decodesegsB0 DEC_A_LLVMF regs mem md)
      (fun W' c' => exists fpos,
         llvm_b_st_074 B MT (mkDCtx fx ly S W regs mem md p n pl M fpos) W' c').
Proof.
intros HPCS HCELLS ML MTL MTF SMP ASM ly S W regs mem md p n pl M XL
  HFN H10 H11 Hn26 Hinp Hlen Hgarr Hfrs HMOK HFRM HXL.
pose proof HFN as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : DEC_LLVMF_STK = 32768) by reflexivity.
pose proof (ajournal_init (SK := dec_B_sink_head) decodesegsB0 B DEC_LLVMF_STK [] ly S W regs mem md [] HFN) as HJ.
pose proof (dec_entry_st ly S W regs mem md HCELLS HFN) as HS.
assert (HEI : img_env VAL A_LIM (DEN regs)) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) (DEN regs) (mrestrict (w_H W) mem)) by constructor.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (DEN regs) k = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold DEN. rewrite (Eimg_low (PI := PIB) (Ereg regs dec_extra) kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs dec_extra kk r Hk). }
assert (E2 : ew (DEN regs) 2 = YK11.getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (Usp : bv_unsigned (ew (DEN regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew (DEN regs) 32 = Z_to_bv 64 SB)
  by (unfold DEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS)) md) Q) end.
change (Eimg (Ereg regs dec_extra)) with (DEN regs) in HS.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [reflexivity | rewrite Usp; lia | cbn; rewrite Hstkv; lia | cbn; lia |].
  awr_ro_rec. }
assert (Hsprng : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
set (sp1 := 32 * ((spZ regs + -224) / 32)).
destruct (dec_sp1_facts (spZ regs + -224) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (E2' : ew (DEN regs) 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 116)) R1 ltac:(apply codeptr_val; exact HEI).
reg_at HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (dec_denot_and_m32 (DEN regs) 2 (spZ regs) (-224) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
reg_at HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
reg_at HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (dec_denot_and_m32_add0 (DEN regs) 2 (spZ regs) (-224) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
reg_at HS (18%bv : bv 5) (w64 SHADOW_OFF) R18
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (19%bv : bv 5) (w64 n) R19
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
reg_at HS (24%bv : bv 5) (w64 p) R24
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HR0 : region_ok segsx Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (st_ok_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
end.
cbn [ms_mem restrict] in HR0.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (mkst rg (Z_to_bv 64 (decodeb_sigma DB___asan_stack_malloc_0)) mm rom) mdx) Q) end.
rewrite <- HPCS.
assert (Hcnt : count_cid 0 (frames S) < fs_frames 0) by (rewrite Hfrs; vm_compute; reflexivity).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (dec_aj_stack_malloc (SK := dec_B_sink_head) SEGS B LAWS decodeb_segs_low ML SMP 0 ASM
    ltac:(lia) W rg mm DEC_LLVMF_STK (spZ regs) [] ly S W mem md [] ly S mdx 0 (sp1 - spZ regs)
    (Z_to_bv 64 (BASE + 116)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp16, Hsp1al16. reflexivity.
  - lia.
  - unfold ESTACK. rewrite Hstkv. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hz & Hflag & Hfpres & HK
  & (f & ES2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HFal & _ & _ & _).
destruct (frames_bounds _ B LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in Hz, Hflag, Hfpres, HFceil.
assert (HKS : forall a, spZ regs - 224 <= a < spZ regs ->
  aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) (ms_mem ms) a).
{ intros a Ha. apply (proj1 HK); unfold ESTACK; lia. }
assert (HPAY : forall j, 0 <= j < n -> aview decodesegsB0 (w_H W) mem2 (p + j) = aview decodesegsB0 (w_H W) mem (p + j)).
{ intros j Hj. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  apply (F2 p n j (Hinp ltac:(lia))); [rewrite Eab; exact (Hinp ltac:(lia)) | lia | intros (rg & [] & _)]. }
exists pos.
unfold llvm_b_st_074, dec_b_core, dec_b_saved, d_sp1, d_sp0, d_F, d_FL, DEC_FCLASS.
cbn [d_fx d_ly d_S d_W d_regs d_mem d_md d_p d_n d_pl d_M d_fpos].
replace (spZ regs - 224) with (spZ regs + -224) by lia. fold sp1.
exists fx, ly, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HFRM|].
split.
{ split; [exact HJ2|].
  split; [rewrite Hfrs2, Hfrs; reflexivity|].
  split; [transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
  split; [transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
  split; [unfold spZ at 1; transitivity (bv_unsigned (YK11.getr (ms_regs ms) 2));
    [f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia)) | rewrite R2; apply unsigned_lit_small; lia]|].
  split; [lia|]. split; [exact Hsp1al|].
  split; [transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
  split; [transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
  split.
  { unfold dec_b_saved_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: saved_tac HR0 HKS EE Usp ms regs W. }
  split; [exact HF4096|]. split; [exact HFal|].
  split; [intros a Ha; apply Hfpres; lia|].
  split; [replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia; exact Hflag|].
  split; [intros Hn0; rewrite Eab; exact (Hinp Hn0)|].
  apply (garr8_kept decodesegsB0 (w_H W) (w_H W) mem mem2 p _); [| exact Hgarr].
  intros j Hj. rewrite length_map, <- Hlen in Hj. apply HPAY. lia. }
split; [exact Eab|].
split; [unfold dec_spent_074; rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)|].
split.
{ rewrite ES2. apply (mo_ok_set_fs MT MTF). apply (mo_ok_le MT MTL S (dec_rest_074 MT n) (XL n) HMOK).
  pose proof (dec_cost_ladder MT n) as (L0 & _). unfold dec_spent_074 in L0. pose proof (HXL n ltac:(lia)). lia. }
split; [exact Ha0|].
split; [transitivity (YK11.getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
split; [transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
split; [transitivity (YK11.getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
exact Hz.
Qed.
End entry.

(* ------------------------------------------------------------------ *)
(* 6. The segment theorem                                               *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
(* lib/B/Prog/LLVMFuzzerTestOneInput_segs.v Section seg, variable for variable; the theorem uses none of
   its Hypotheses. *)
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem llvm_b_entry_ok :
  llvm_b_entry_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_entry_stmt.
intros HPCS HCELLS LAWS ML MTL MTF SMP ASM0 fx ly S W regs mem md p n pl M HPRE HROMv HXL.
pose proof HPRE as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Hrod & Hrom
  & Hsink & Hfd & Hsorted & Hmeta & Hmo & Hfrm).
exact (dec_entry_walk B LAWS MT HPCS HCELLS ML MTL MTF SMP (ASM0 fx) ly S W regs mem md p n pl M XL
  HAFN H10 H11 ltac:(destruct Hpn as [[-> _] | [Hq _]]; lia)
  ltac:(intros Hn0; destruct Hpn as [[Hq _] | [_ Hq]]; [lia | exact Hq])
  Hlen Hgarr Hfrs Hmo Hfrm HXL).
Qed.

End sg.
