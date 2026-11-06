(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_sd.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses (a Theorem Labs lane's pairing, a Theorem Labs lane's reloc). *)
(* Modified by Theorem Labs, 2026-10: the mid-walk seed of check_reply (fuzz_command.asan-ubsan), after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v cl_seed: from the mid-walk invariant cr_mid and the registers cr_regs_at
   (check_reply_m.v), the symbolic state at any program point after the frame call.

   The atoms (0..31 are the registers at that point):
     32 SB   33 g_rec   34 the reply block   35 |reply| + 1   36 F (the frame)   37 FL (its flag cell)
     38 SB + F / 8   39 w   40 w->w (mod 2^64)   41 w->n   42 w->w[0] (mod 2^64)
     43..54 the entry's ra, s0, .., s10 (stored at sp0 - 8, .., sp0 - 96)
   The registers: s0 = sp0 (atom 8 itself), s1 = sp (atom 2), s2 = s7 = F, s6 = SB + F/8, s8 = SB, s9 = g_rec,
   s4 = g_rec + 928, s10 = SB + (g_rec + 928) / 8 (the shadow address the inline checks 0x8700c, 0x870c0, 0x870e4 load).
   The regions: the entry's callee-saved registers below sp0 (read-only), g_rec.reply and g_rec.reply_size, the
   frame's header [0, 32) (written by the epilogue), its tail [64, 128) with the flag pointer at 120, and its shadow
   [0, 16) with refusal[32]'s shadow bytes 4..7 at 0, writable only for the epilogue's plain run (a writable region
   inside the shadow span is outside what the token engine's sh_static_ok allows). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_c check_reply_k check_reply_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition cr_s10 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 928) (SLit 3)) (SOff 32 0).
Definition sr_mid : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
  (9%bv : bv 5) (SOff 2 0)) (18%bv : bv 5) (SOff 36 0)) (23%bv : bv 5) (SOff 36 0)) (22%bv : bv 5) (SOff 38 0))
  (24%bv : bv 5) (SOff 32 0)) (25%bv : bv 5) (SOff 33 0)) (20%bv : bv 5) (SOff 33 928)) (26%bv : bv 5) cr_s10.

Definition cr_stkm : YP09.region := Eval vm_compute in
YP09.mkRegion (Some 8%nat) (-96) 0 0 0
(map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (43 + j) 0))) (seq 0 12)).
Definition cr_grecm : YP09.region :=
YP09.mkRegion (Some 33%nat) 928 944 0 0 [YP09.mkChunk 928 (CVal 8 (SOff 34 0)); YP09.mkChunk 936 (CVal 8 (SOff 35 0))].
Definition cr_frh : YP09.region := YP09.mkRegion (Some 36%nat) 0 32 0 32 [].
Definition cr_frt : YP09.region := YP09.mkRegion (Some 36%nat) 64 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 37 0))].
Definition cr_frs (shw : bool) : YP09.region :=
YP09.mkRegion (Some 38%nat) 0 16 0 (if shw then 16 else 0)
[YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 7 (CVal 1 (SLit 0))].
Definition cr_regions_mid (shw : bool) : smem := [cr_stkm; cr_grecm; cr_frh; cr_frt; cr_frs shw].
Definition cr_facts_mid : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBc SBc 0);
          (33%nat, mkAF 0x5e32c0 0x5e32c0 3); (34%nat, HPc); (35%nat, mkAF 1 8194 0); (36%nat, HPTR 5);
          (37%nat, HPTR 0); (38%nat, mkAF (SBc + 512) (SBc + 2 ^ 44) 2); (39%nat, mkAF (2 ^ 46) (2 ^ 47) 3);
          (41%nat, mkAF 0 2147483647 0) ] [] [].
Definition ss_mid (pc : Z) (shw : bool) : sstate := mkSS pc sr_mid (cr_regions_mid shw) None cr_facts_mid.
Definition crSH_mid : list shent := [mkSHE 33 928 944].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition crM_extra (v : crv) (lyc : alayout) (pos : Z) : list word :=
map (Z_to_bv 64) [SBc; 0x5e32c0; c_p v; c_nr v + 1; frame_addr lyc 1 pos; flag_addr lyc 1 pos;
  SBc + frame_addr lyc 1 pos / 8; c_w v; c_ww v mod 2 ^ 64; c_n v; c_p0 v mod 2 ^ 64]
++ map (fun r => getr (c_regs v) (Z_to_bv 5 r)) cr_saved_regs.
Definition crM (regs1 : bvmap 5 word) (v : crv) (lyc : alayout) (pos : Z) : env :=
Eimg (Ereg regs1 (crM_extra v lyc pos)).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Lemma crM_low : forall regs1 v lyc pos k, (k < A_TEXT)%nat ->
ew (crM regs1 v lyc pos) k = ew (Ereg regs1 (crM_extra v lyc pos)) k.
Proof. intros. unfold crM. apply Eimg_low. exact H. Qed.
Lemma crM_reg : forall regs1 v lyc pos k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (crM regs1 v lyc pos) k = getr regs1 r.
Proof.
intros regs1 v lyc pos k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite crM_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.
Lemma crM_extra_nth : forall regs1 v lyc pos j, (j < 23)%nat ->
ew (crM regs1 v lyc pos) (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0).
Proof. intros. rewrite crM_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma denot_s10 : forall E, ew E 33 = Z_to_bv 64 0x5e32c0 -> ew E 32 = Z_to_bv 64 SBc ->
sv_denot E cr_s10 = w64 (SHADOW_OFF + (A_G_REC + OFF_REPLY) / 8).
Proof.
intros E H33 H32. rewrite denot_lit_U. unfold w64. f_equal.
unfold cr_s10. rewrite U_SAlu, U_srl3, !U_SOff, H33, H32, !unsigned_lit_small by (unfold SBc; lia).
vm_compute. reflexivity.
Qed.
Lemma regs_ok_mid : forall v lyc pos regs1,
cr_regs_at B v lyc pos regs1 -> regs_ok (crM regs1 v lyc pos) sr_mid regs1.
Proof.
intros v lyc pos regs1 (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
set (E := crM regs1 v lyc pos).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; apply crM_reg; assumption).
pose proof (crM_extra_nth regs1 v lyc pos 0 ltac:(lia)) as E32. pose proof (crM_extra_nth regs1 v lyc pos 1 ltac:(lia)) as E33.
pose proof (crM_extra_nth regs1 v lyc pos 4 ltac:(lia)) as E36. pose proof (crM_extra_nth regs1 v lyc pos 6 ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E36, E38. fold E in E32, E33, E36, E38.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite R26; symmetry; apply denot_s10; assumption
| rewrite R20; cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
  | rewrite (EE 2%nat 2%bv eq_refl), R9, R2; reflexivity
  | rewrite E36; exact R18 | rewrite E36; exact R23 | rewrite E38; exact R22 | rewrite E32; exact R24
  | rewrite E33; exact R25 ] | idtac "MARK" rr2; fail ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cr_seed : forall v lyc Sc Wc regs1 memc mdc pos pc shw,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regs1 ->
4096 <= c_p v -> c_p v mod 16 = 0 -> c_p v + c_nr v + 1 <= 140737479966720 -> c_nr v + 1 <= 8194 ->
st_ok_pi SEGS VAL (crM regs1 v lyc pos) (ss_mid pc shw)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos pc shw CX MID RA Hp4096 Hp16 Hphi Hnr.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw8 & Hspw & _ & _ & _ & Hn & _ & _ & _ & _ & _ & _ & Hwhi).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as HFimg.
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFLp & _ & HFLapp & HFLc).
change (fs_frame_bytes 1) with 128 in *. unfold in_app in HFLapp, HFapp.
set (sp0 := c_sp v) in *. set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
unfold c_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, Hbot, Htop, Hspw, Hpres0.
assert (Hsp1 : sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32) by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
rewrite restrict_mkst_fx.
set (E := crM regs1 v lyc pos).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; apply crM_reg; assumption).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0)) by (intros; apply crM_extra_nth; lia).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 9%nat ltac:(lia)) as E41.
cbn [Nat.add nth crM_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E41.
assert (E2 : ew E 2 = getr regs1 2) by (apply EE; reflexivity).
assert (E8 : ew E 8 = getr regs1 8) by (apply EE; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp1_of sp0) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; destruct Hsp1 as [Hs1 Hs2]; rewrite Hs1; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0) by (rewrite E8, R8; unfold w64; apply unsigned_lit_small; lia).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (Hwr : forall o, sp0 - CHECK_REPLY_STK <= o < sp0 -> writable_at SEGS (mrestrict (w_H Wc) memc) o)
by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; exact Ho).
unfold ss_mid. apply pa_entry_st_ok_full.
+ apply regs_ok_mid. exact RA.
+ destruct shw; vm_compute; reflexivity.
+ unfold cr_regions_mid, cr_stkm, cr_grecm, cr_frh, cr_frt, cr_frs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* rewrite (VB 8%nat sp0 ltac:(rewrite E8, R8; reflexivity)) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
let j := eval compute in (n - 43)%nat in let r := eval compute in (nth j cr_saved_regs 0) in
apply (chunk_ok_val SEGS E _ sp0 off 8 (SOff n 0) (bv_unsigned (ew E n)));
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
| cbn; lia
| replace (sp0 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
  let k := eval compute in (n - 32)%nat in change (ew E n) with (ew E (32 + k)); rewrite (EX k ltac:(lia)); cbn [Nat.sub nth crM_extra map app];
  exact (VSV j r eq_refl) ] end.
* rewrite (VB 33%nat 0x5e32c0 E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ 0x5e32c0 928 8 (SOff 34 0) (c_p v));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold c_p; apply Z.mod_pos_bound; lia | zside | exact VREP].
-- apply (chunk_ok_val SEGS E _ 0x5e32c0 936 8 (SOff 35 0) (c_nr v + 1));
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold c_nr in *; lia | zside | exact VSZ].
* rewrite (VB 36%nat F E36) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))).
* rewrite (VB 36%nat F E36) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ F 120 8 (SOff 37 0) FL);
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside | exact VFL].
* rewrite (VB 38%nat (SBc + F / 8) E38) by (pose proof (Z.div_pos F 8); pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)); unfold SBc; lia).
split; [pose proof (Z.div_pos F 8); unfold SBc; lia|]. split; [pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)); unfold SBc; lia|]. split.
{ intros o Ho. destruct shw; [|lia]. apply (apresent_writable SEGS).
unfold shadow_addr in HFSpres. rewrite <- SBc_SHADOW_OFF in HFSpres. apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia))). }
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SLit 0))) =>
apply (chunk_ok_val SEGS E _ (SBc + F / 8) off 1 (SLit 0) 0); [reflexivity | lia | zside |
rewrite SBc_SHADOW_OFF; apply VSH; lia] end.
+ apply pairwise_disjoint_of_extents. unfold cr_regions_mid, cr_stkm, cr_grecm, cr_frh, cr_frt, cr_frs, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 33%nat 0x5e32c0 E33) by lia. rewrite (VB 36%nat F E36) by lia.
rewrite (VB 38%nat (SBc + F / 8) E38) by (pose proof (Z.div_pos F 8); pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)); unfold SBc; lia).
rewrite (VB 8%nat sp0 ltac:(rewrite E8, R8; reflexivity)) by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
unfold in_app, off_img, SBc, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
repeat split; lia.
+ split; [|split; exact I].
cbn [cr_facts_mid f_atoms atoms_ok]. unfold afact_ok, HPc, HPTR. cbn [af_lo af_hi af_al2].
fold F FL in E36, E37, E38.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HFm : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z.div_mul; lia).
pose proof Hw8 as Hw8'. unfold c_sp in Hspw.
rewrite U2, U8, E32, E33, E34, E35, E36, E37, E38, E39, E41.
rewrite (unsigned_lit_small SBc) by (unfold SBc; lia). rewrite (unsigned_lit_small 0x5e32c0) by lia.
rewrite (unsigned_lit_small (c_p v)) by (unfold c_nr in *; lia). rewrite (unsigned_lit_small (c_nr v + 1)) by (unfold c_nr in *; lia).
rewrite (unsigned_lit_small F) by lia. rewrite (unsigned_lit_small FL) by lia.
rewrite (unsigned_lit_small (SBc + F / 8)) by (unfold SBc; lia).
rewrite (unsigned_lit_small (c_w v)) by lia. rewrite (unsigned_lit_small (c_n v)) by lia.
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
destruct Hsp1 as [Hs1 Hs2]. rewrite Hs1.
unfold SBc, c_nr in *.
repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
all: try (replace (sp0 - 128 - sp0 mod 32) with ((sp0 / 32 - 4) * 32) by (pose proof (Z.div_mod sp0 32 ltac:(lia)); lia); apply Z_mod_mult).
all: try (rewrite HFm; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult).
Qed.
End e.
End f.
End d.
