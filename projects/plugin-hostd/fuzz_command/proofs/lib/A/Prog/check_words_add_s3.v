(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment 4b of check_reply's walk (fuzz_command.asan, 0x86d78): the refusal
   path from the return of snprintf at 0x86f9c to the strcmp call at 0x86fb8 (cr_s4b : CR_STRCMP_stmt ->
   CR_RSNP_stmt, lib/A/Prog/check_reply_m.v), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call step with
   cl_callS and jafter_call_keep_pi).

   The segment is stated at its section's FP state, and check_reply_s4.v uses it at the FP state the snprintf wrapper
   returns (the segment-lemma form): the walk seeds the mid-walk state at 0x86f9c
   (check_reply_sd.v cr_seed) with g_rec's fields as the only region, runs `mv a0,s5` to the call of
   rec_code_declared, takes the code's declared answer 1 (reply_okA), so the abort branch at 0x86fa4 is not taken,
   and runs over the inline check of g_rec.reply and the loads of the reply and the refusal to 0x86fb8. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s4b.v, with its module paths and module names changed; 362 of its 397 lines of code are new or changed and 338 lines of the source are left out. *)
(* check_words_add's walk, part 3: the placement-word middle 0x88b60 .. 0x88bd0 when the placement is word 3.
   The twin of cwa_mid_dash in lib/A/Prog/check_words_add_s2.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_add_c.
Module PCwa := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_s1 check_words_add_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the state at 0x88b60 (offset 0x267c) when the placement is word 3 (one of "own", "default", "pool:..."):
   atom 9 is s1 (the placement pointer), 42 its first byte, 18 s2 (the word array), 19 s3 (read), 21 s5 (the
   shadow base), 33 and 34 the recorded arguments, 35..41 the saved registers, 44 word 4. *)
Definition cwa_wplR : YP09.region := YP09.mkRegion (Some 9%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 42 0))].
Definition cwa_regionsW : smem := [cwa_wplR].
Definition cwa_factsW : facts :=
mkFacts [(9%nat, mkAF 1 0x7fffff800000 0); (19%nat, mkAF 0 64 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
(42%nat, mkAF 100 112 0)] [] [].
Definition cwa_SHW : list shent := [mkSHE 9 0 1].
Definition cwa_SHWW : list shent := [mkSHE 9 0 1; mkSHE 18 32 40].
Definition cwa_ssW : sstate := mkSS 0x267c sr_atoms cwa_regionsW None cwa_factsW.
Definition cwa_extraW (q2 q3 b0 p3 p4 : Z) (regs : bvmap 5 word) : list word :=
[Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 q2; Z_to_bv 64 q3;
getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21;
Z_to_bv 64 b0; Z_to_bv 64 p3; Z_to_bv 64 p4].
Definition cwa_EW (regsc : bvmap 5 word) (q2 q3 b0 p3 p4 : Z) (regs : bvmap 5 word) : env :=
Eimg (Ereg regsc (cwa_extraW q2 q3 b0 p3 p4 regs)).

(* the first byte of a placement word *)
Lemma cwa_placement_head : forall w, PCwa.is_placement_b w = true ->
exists c rest, w = c :: rest /\ 100 <= bv_unsigned c <= 112.
Proof.
intros w H. unfold PCwa.is_placement_b in H. apply orb_prop in H as [H | H]; [apply orb_prop in H as [H | H]|].
- apply bytes_eqb_iff in H. subst w. eexists _, _. split; [reflexivity|]. vm_compute. split; discriminate.
- apply bytes_eqb_iff in H. subst w. eexists _, _. split; [reflexivity|]. vm_compute. split; discriminate.
- apply prefixb_iff in H. destruct w as [|c rest]; [vm_compute in H; discriminate|].
  exists c, rest. split; [reflexivity|]. cbn [length S_POOL str map firstn] in H.
  injection H as Hc _. subst c. vm_compute. split; discriminate.
Qed.

(* a signed bge between two values the facts pin below 2^63 *)
Lemma cwa_branch_ge : forall E a b (x y : Z),
sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken].
assert (HU : forall z : Z, 0 <= z < 2 ^ 63 -> bv_unsigned (Z_to_bv 64 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. lia. }
unfold bv_lts. rewrite !bv_signed_small by (rewrite HU by lia; lia).
rewrite !HU by lia. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HFACTS : CwaFacts B.
#[local] Notation LAWS := (cwa_laws B).

Let RUN := paj_run B (cwa_laws B).
Let RUNTO := paj_run_to B (cwa_laws B).
Let BR := paj_branch (PI := PI).

(* a string argument lies off the shadow band: its block is heap memory *)
Lemma cwa_str_band : forall ly S W mem md p x,
AR SEGS B ly S W mem md ->
cwa_str B ly S (rdW W mem) p x ->
p + astr_len x + 1 <= kLowShadowBeg \/ kHighMemBeg <= p.
Proof.
intros ly S W mem md p x HAR HSTR.
destruct HSTR as (_ & Hblk & _). unfold astr_len.
destruct Hblk as (q & k & Hin & Hq1 & Hq2).
destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ q k HAR Hin) as (_ & _ & _ & Hia & _).
pose proof (req_size_pos k ltac:(lia)) as [Hr1 Hr2].
unfold in_app, kLowShadowBeg, kHighMemBeg in *. destruct Hia as [_ [Ha | [Ha _]]]; [left | right]; lia.
Qed.

Lemma cwa_mid_word_entry :
forall ly S (W : world SEGS) memc mdc (regsc : bvmap 5 word) (q2 q3 b0 p3 p4 r : Z) (regs : bvmap 5 word),
AR SEGS B ly S W memc mdc ->
getr regsc 9 = w64 p3 -> getr regsc 19 = w64 r -> 0 <= r <= 64 ->
getr regsc 21 = w64 SHADOW_OFF -> 100 <= b0 <= 112 ->
1 <= p3 -> p3 + 1 <= 0x7fffff800000 ->
(p3 + 1 <= kLowShadowBeg \/ kHighMemBeg <= p3) ->
aval_mem (rdW W memc) p3 1 b0 ->
range_addressable (rdW W memc) SHADOW_OFF p3 1 ->
st_ok_pi SEGS VAL (cwa_EW regsc q2 q3 b0 p3 p4 regs) cwa_ssW
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x267c)) memc (seg_rom SEGS)))
/\ sh_ok SEGS CWA_BXT cwa_SHW (cwa_EW regsc q2 q3 b0 p3 p4 regs) (mrestrict (w_H W) memc).
Proof.
intros ly S W memc mdc regsc q2 q3 b0 p3 p4 r regs HAR R9 R19 Hr R21 Hb0 Hp1 Hp2 Hband HB0 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (EN : forall (k : nat) (rr : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned rr ->
ew (cwa_EW regsc q2 q3 b0 p3 p4 regs) k = getr regsc rr)
by (intros k rr Hk Hrr; unfold cwa_EW; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 13)%nat -> ew (cwa_EW regsc q2 q3 b0 p3 p4 regs) (32 + j) = nth j (cwa_extraW q2 q3 b0 p3 p4 regs) (Z_to_bv 64 0))
by (intros j Hj; unfold cwa_EW; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 21%nat 21%bv ltac:(lia) eq_refl) as Ea21.
pose proof (EX 10%nat ltac:(lia)) as Ea42. cbn [Nat.add nth cwa_extraW] in Ea42.
rewrite restrict_mkst_fx.
set (E := cwa_EW regsc q2 q3 b0 p3 p4 regs) in *.
assert (Upl : bv_unsigned (ew E 9) = p3) by (rewrite Ea9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (Ur : bv_unsigned (ew E 19) = r) by (rewrite Ea19, R19; unfold w64; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite Ea21, R21; unfold w64; apply unsigned_lit_small; cwa_unf; lia).
assert (Ub0 : bv_unsigned (ew E 42) = b0) by (rewrite Ea42; apply unsigned_lit_small; lia).
split.
- unfold cwa_ssW. apply pa_entry_st_ok_full.
  + unfold E, cwa_EW. apply (regs_ok_agree 32 (Ereg regsc (cwa_extraW q2 q3 b0 p3 p4 regs)));
    [split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity | apply regs_ok_Ereg].
  + vm_compute. reflexivity.
  + unfold cwa_regionsW, cwa_wplR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Upl. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ p3 0 1 (SOff 42 0) b0);
    [ cbn [sv_denot]; rewrite Ea42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (cwa_val_mem W memc p3 1%nat b0 HB0).
  + unfold cwa_regionsW. cbn [pairwise_disjoint all_disjoint]. split; [constructor | exact I].
  + split; [|split; exact I].
    cbn [cwa_factsW f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Upl, Ur, Usb, Ub0. rewrite !Z.pow_0_r, !Z.mod_1_r.
    cwa_unf. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, cwa_SHW. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E CWA_BXT 9 p3 1 p3 0 1).
  + exact HRA.
  + unfold U, CWA_BXT. cbn [sv_denot]. rewrite Ea21, R21, Z.add_0_r. unfold w64.
    rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. cwa_unf. lia.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Upl.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg in Hband. cwa_unf. lia.
Qed.


(* 0x88b60 .. 0x88bd0 when the placement is word 3: the check of its first byte, the compare with '-' (never
   equal: the first byte is 'o', 'd' or 'p'), then the client is word 4 if read > 4 and the literal "-"
   otherwise. *)
Lemma cwa_mid_word : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
(cp q2 q3 wp r p3 p4 : Z) (x3 w3 w4 : list byte) memc mdc (regsc : bvmap 5 word),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W memc mdc 0 ->
cmd_val_objs -> astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp) ->
cmd_ro_ok (rdW W memc) ->
getr regsc 2 = w64 (spZ regs - 64) ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall rr, 22 <= rr <= 27 -> getr regsc (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) ->
getr regsc 8 = w64 cp -> getr regsc 9 = w64 p3 -> getr regsc 18 = w64 wp ->
getr regsc 19 = w64 r -> getr regsc 21 = w64 SHADOW_OFF ->
3 < r <= 64 ->
cwa_frame (mrestrict (w_H W) memc) (spZ regs) regs ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW W memc) (cp + CALL_OFF_NARGS) 4 4 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 16) 8 q2 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 24) 8 q3 ->
cwa_str B ly S (rdW W memc) q2 w3 ->
cwa_str B ly S (rdW W memc) q3 x3 ->
cwa_str B ly S (rdW W memc) p3 w3 ->
PCwa.is_placement_b w3 = true ->
(4 < r -> in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W memc) (wp + 32) 8 p4 /\
 cwa_str B ly S (rdW W memc) p4 w4) ->
x3 = (if 4 <? r then w4 else S_DASH) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 0x267c)) memc (seg_rom SEGS)) mdc)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
Proof.
intros ly S W regs mem md cp q2 q3 wp r p3 p4 x3 w3 w4 memc mdc regsc
HPRE HRO HJ VOBJS ASTRCMP HROK R2 R3 R4 Rhi R8 R9 R18 R19 R21 Hr HFR Hcp1 Hcp2 HN HQ2 HQ3
AQ2 AQ3 AP3 HPL AW4 HX3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
pose proof (proj1 HJ) as HARc.
pose proof ASAN_CEIL_range as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (Hspc : alloc_ceiling <= spZ regsc - 2 * ESTACK).
{ unfold spZ in *. rewrite R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by (cwa_unf; lia). cwa_unf. lia. }
destruct (cwa_dash_str B HFACTS ly S W regsc memc mdc HARc HROK Hspc) as (SDA & RDA & TDA & _ & _).
destruct (cwa_str_facts B ly S W regsc memc mdc q2 w3 HARc AQ2 Hspc)
as (Hq20 & SQ2 & RQ2 & TQ2 & Bq2 & Rq2).
destruct (cwa_str_facts B ly S W regsc memc mdc q3 x3 HARc AQ3 Hspc)
as (Hq30 & SQ3 & RQ3 & TQ3 & Bq3 & Rq3).
destruct (cwa_str_facts B ly S W regsc memc mdc p3 w3 HARc AP3 Hspc)
as (Hp30 & SP3 & RP3 & TP3 & Bp3 & Rp3).
pose proof (cwa_str_band ly S W memc mdc p3 w3 HARc AP3) as Hband.
destruct (cwa_placement_head w3 HPL) as (c & rest & Hw3 & Hc0).
assert (HB0 : aval_mem (rdW W memc) p3 1 (bv_unsigned c)).
{ pose proof AP3 as AP3'. unfold cwa_str in AP3'. destruct AP3' as (_ & _ & [HBy _]).
  pose proof (cwa_aval_of_bytes _ p3 (w3 ++ [Z_to_bv 8 0]) 0 c HBy ltac:(rewrite Hw3; reflexivity)) as HX.
  cbn [Z.of_nat] in HX. rewrite Z.add_0_r in HX. exact HX. }
assert (HRA : range_addressable (rdW W memc) SHADOW_OFF p3 1).
{ destruct RP3 as (_ & _ & _ & _ & _ & HRa & _). intros a Ha. apply HRa. unfold astr_len. lia. }
assert (Lw3 : 0 <= astr_len w3) by (unfold astr_len; lia).
destruct (cwa_mid_word_entry ly S W memc mdc regsc q2 q3 (bv_unsigned c) p3 p4 r regs
HARc R9 R19 ltac:(lia) R21 Hc0 ltac:(lia) ltac:(lia) ltac:(destruct Hband; [left | right]; lia) HB0 HRA)
as [HS SHOK].
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew (cwa_EW regsc q2 q3 (bv_unsigned c) p3 p4 regs) n = getr regsc rr)
by (intros n rr Hn Hrr; unfold cwa_EW; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 13)%nat ->
ew (cwa_EW regsc q2 q3 (bv_unsigned c) p3 p4 regs) (32 + j) = nth j (cwa_extraW q2 q3 (bv_unsigned c) p3 p4 regs) (Z_to_bv 64 0))
by (intros j Hj; unfold cwa_EW; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 18%nat 18%bv ltac:(lia) eq_refl) as Ea18.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 21%nat 21%bv ltac:(lia) eq_refl) as Ea21.
pose proof (EX 12%nat ltac:(lia)) as Ea44. pose proof (EX 1%nat ltac:(lia)) as Ea33.
pose proof (EX 2%nat ltac:(lia)) as Ea34.
cbn [Nat.add nth cwa_extraW] in Ea33, Ea34, Ea44.
set (E := cwa_EW regsc q2 q3 (bv_unsigned c) p3 p4 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, cwa_EW; apply Eimg_env).
paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26cc; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
assert (HmemE : ms_mem ms = memc)
by (exact (frame_of_read_only _ cwa_regionsW _ _ ltac:(vm_compute; reflexivity) HF)).
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (HR19 : sv_denot E1 (SOff 19 0) = Z_to_bv 64 r);
[ cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
  rewrite Z.add_0_r, Ea19, R19, Z_to_bv_bv_unsigned; reflexivity |];
assert (HR4 : sv_denot E1 (SLit 4) = Z_to_bv 64 4) by reflexivity end.
psrr_branch_tok RUN BR HS SHOK CWA_SPAN.
- rewrite (cwa_branch_ge _ _ _ 4 r HR4 HR19 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (VO29 : VAL (A_OBJ 29) = 0x21ac0)
  by (rewrite (VOBJS 29%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
  assert (X3D : x3 = S_DASH) by (rewrite HX3; rewrite (proj2 (Z.ltb_ge 4 r) Hc); reflexivity).
  rewrite X3D in SQ3, RQ3, TQ3, Bq3.
  assert (E270 : ew (cwa_EW regsc q2 q3 (bv_unsigned c) p3 p4 regs) 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (unfold cwa_EW; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  fold E in E270.

    paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26ec; [awr_ok_tac |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
      assert (HM2 : mm = memc);
      [ rewrite <- HmemE;
        lazymatch goal with HFx : frame_of _ ?rs _ mm |- _ =>
          exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HFx) end
      | ] end.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.

    assert (T18 : getr (ms_regs ms0) 18 = w64 0x21ac0) by (rewrite P18, E270, VO29; reflexivity).

    assert (T2 : getr (ms_regs ms0) 2 = w64 (spZ regs - 64))
    by (rewrite P2, (EN 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
    assert (T3 : getr (ms_regs ms0) 3 = getr regs 3)
    by (rewrite P3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
    assert (T4 : getr (ms_regs ms0) 4 = getr regs 4)
    by (rewrite P4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
    assert (T8 : getr (ms_regs ms0) 8 = w64 cp)
    by (rewrite P8, (EN 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
    assert (T9 : getr (ms_regs ms0) 9 = w64 p3)
    by (rewrite P9, (EN 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
    assert (T21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
    by (rewrite P21, (EN 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
    assert (Thi : forall rr, 22 <= rr <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
    { intros rr Hrr.
      assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
      lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
        rewrite (EN n r2 ltac:(lia) eq_refl); apply Rhi; lia end. }
    assert (Hsp0 : spZ (ms_regs ms0) = spZ regsc) by (unfold spZ; rewrite T2, R2; reflexivity).
    rewrite HM2 in HJ.

    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    apply (cwa_tail B RLO RHI HFACTS ly S W regs mem md cp q2 q3 p3 0x21ac0 w3 S_DASH mm mdq rg) end.
    all: rewrite ?HM2.
    all: try assumption.
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ2)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ3)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RDA)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RP3)).
    all: try (cbv [astr_len S_DASH str map length]); cwa_unf; lia.
- rewrite (cwa_branch_ge _ _ _ 4 r HR4 HR19 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  destruct (AW4 Hc) as (HBK & HVW & AP4).
  destruct (cwa_str_facts B ly S W regsc memc mdc p4 w4 HARc AP4 Hspc)
  as (Hp40 & SP4 & RP4 & TP4 & Bp4 & Rp4).
  assert (X3W : x3 = w4) by (rewrite HX3; rewrite (proj2 (Z.ltb_lt 4 r) Hc); reflexivity).
  rewrite X3W in SQ3, RQ3, TQ3, Bq3.
  destruct HBK as (qb & kb & Hinb & Hqb1 & Hqb2).
  assert (HRAW : range_addressable (rdW W memc) SHADOW_OFF qb (req_size kb))
  by (exact (range_addressable_of_block SEGS B (cwa_laws B) ly S W memc mdc qb kb qb (req_size kb) HARc Hinb
  ltac:(lia) ltac:(lia))).
  destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qb kb HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & _).
  pose proof (req_size_pos kb ltac:(lia)) as [Hr1 Hr2].
  assert (Hwp1 : 4064 <= wp) by lia.
  assert (Hwp2 : wp + 40 <= 0x7fffff800000) by lia.
  apply cwa_set_mem_nil in HS.
  apply (st_ok_pi_add_fact _ _ _ 18%nat (mkAF 4064 0x7fffff800000 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2];
     cbn [ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
     rewrite Ea18, R18; unfold w64; rewrite unsigned_lit_small by lia;
     rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia].
  apply (st_ok_pi_add_region _ _ _ (cwa_wordR 32 44)) in HS;
  [ | vm_compute; reflexivity | | ].
  + lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 _ =>
      assert (SHOKW : sh_ok SEGS CWA_BXT cwa_SHWW E1 (mrestrict (w_H W) (ms_mem ms))) end.
    { unfold sh_ok, cwa_SHWW. constructor; [|constructor; [|constructor]].
      - exact (Forall_inv SHOK).
      - apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) _ CWA_BXT 18 qb (req_size kb) wp 32 40).
        + rewrite HmemE. exact HRAW.
        + unfold U, CWA_BXT. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
          rewrite Z.add_0_r, Ea21, R21. unfold w64. rewrite Z_to_bv_bv_unsigned.
          apply unsigned_lit_small. cwa_unf. lia.
        + unfold U. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
          rewrite Z.add_0_r, Ea18, R18. unfold w64. rewrite Z_to_bv_bv_unsigned.
          apply unsigned_lit_small. lia.
        + lia.
        + lia.
        + intros x Hx. cbn [Z.min Z.max] in Hx.
          unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia. destruct Hbia as [_ [Hap | [Hap Hap2]]];
          cwa_unf; lia. }
    clear SHOK. rename SHOKW into SHOK.

    paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26ec; [awr_ok_tac |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
      assert (HM2 : mm = memc);
      [ rewrite <- HmemE;
        lazymatch goal with HFx : frame_of _ ?rs _ mm |- _ =>
          exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HFx) end
      | ] end.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.

    assert (T18 : getr (ms_regs ms0) 18 = w64 p4) by (rewrite P18, Ea44; reflexivity).

    assert (T2 : getr (ms_regs ms0) 2 = w64 (spZ regs - 64))
    by (rewrite P2, (EN 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
    assert (T3 : getr (ms_regs ms0) 3 = getr regs 3)
    by (rewrite P3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
    assert (T4 : getr (ms_regs ms0) 4 = getr regs 4)
    by (rewrite P4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
    assert (T8 : getr (ms_regs ms0) 8 = w64 cp)
    by (rewrite P8, (EN 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
    assert (T9 : getr (ms_regs ms0) 9 = w64 p3)
    by (rewrite P9, (EN 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
    assert (T21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
    by (rewrite P21, (EN 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
    assert (Thi : forall rr, 22 <= rr <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
    { intros rr Hrr.
      assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
      lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
        rewrite (EN n r2 ltac:(lia) eq_refl); apply Rhi; lia end. }
    assert (Hsp0 : spZ (ms_regs ms0) = spZ regsc) by (unfold spZ; rewrite T2, R2; reflexivity).
    rewrite HM2 in HJ.

    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    apply (cwa_tail B RLO RHI HFACTS ly S W regs mem md cp q2 q3 p3 p4 w3 w4 mm mdq rg) end.
    all: rewrite ?HM2.
    all: try assumption.
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ2)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ3)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RP3)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RP4)).
    all: cwa_unf; lia.
  + unfold cwa_wordR, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
    assert (BW' : bv_unsigned (ew E 18) = wp)
    by (rewrite Ea18, R18; unfold w64; apply unsigned_lit_small; lia).
    cbn [base_val ew ewset Nat.eqb]. rewrite HmemE, ?BW'.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ wp 32 8 (SOff 44 0) p4);
    [ cbn [sv_denot ew ewset Nat.eqb]; rewrite Ea44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | zside | zside |].
    exact (cwa_val_mem W memc (wp + 32) 8%nat p4 HVW).
  + cbn [ss_mem]. unfold all_disjoint. first [constructor | exact I].
Qed.

End e.
End f.
End d.
