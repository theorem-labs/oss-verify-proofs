(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_checksum_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlChecksumVerify.v, with its module paths and numbers changed; 198 of its 313 lines of code are new or changed and 147 lines of the source are left out. *)
(* mac_is_zero (fuzz_boxreg.asan-ubsan 0x81a38, 38 instructions): the contract of the ASan+UBSan build's code. The
   asan build has no such function: it inlines mac_is_zero into reac_boxreg_find and reac_boxreg_add.
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; it saves ra there for the call of
   __asan_report_load1) and reads the 6 bytes mac[0..5] at p (a0), one byte load each after the check of its shadow
   byte, up to the first byte that is not 0. It returns 1 in a0 when the six bytes are 0 (M = zero6 of
   lib/Prog/Boxreg.v) and 0 otherwise. It writes nothing outside its own frame.
   Where the 6 bytes lie: the image has two calls (jal at 0x81968 in reac_boxreg_find, 0x81fec in reac_boxreg_add),
   both on the caller's mac argument, which is the harness's uint8_t mac[6], a frame object of a side-stack frame of
   LLVMFuzzerTestOneInput: the premise is afobj (p, 6) of lib/A/Prog/BoxBase.v. (reac_boxreg_add's test of
   r->box[i].mac is inlined at 0x820a0..0x820d8 and does not call this function.)
   Hazards: the UBSan pointer-overflow checks on p + i (bltu, and the p + i = 0 test) and the null check on p branch
   to the UBSan trap (the unimp at 0x81acc); they are refuted by 4096 <= p and p + 6 <= alloc_ceiling (the frame
   laws for afobj's frame). The branches to __asan_report_load1 are refuted by afobj's range_addressable.
   The memory model is Pau's plain one (lib/Prog/Boxreg.v zero6), used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require BoxregStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame and ESTACK below it for the
   memory-checking runtime (it calls nothing but the error path). *)
Definition AB_mac_is_zeroP : Z := BASE + AF_mac_is_zero.
Definition MAC_IS_ZERO_STKB : Z := 16 + ESTACK.
Section h.
Variable B : asyms.
Definition tbmac_is_zero_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (M : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B MAC_IS_ZERO_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
((M = Boxreg.zero6 /\ getr regs' 10 = w64 1) \/ (M <> Boxreg.zero6 /\ getr regs' 10 = w64 0))).
Definition tbmac_is_zero_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p : Z) (M : list byte),
afn_pre SEGS B MAC_IS_ZERO_STKB ly S W regs mem md ch ->
getr regs 10 = w64 p ->
afobj SEGS B ly S W mem p 6 ->
length M = 6%nat ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (cfg_at SEGS AB_mac_is_zeroP regs mem md) (tbmac_is_zero_post regs ly S W mem md M).
(* The walk. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The symbolic state at the first slot: atoms 32..37 are the bytes mac[0..5], atom 38 the shadow base. *)
Definition MZ_SB : Z := 0x7fff8000.
Definition MZx : sv := SOff 38 0.
Definition MZspan : Z * Z := (MZ_SB, MZ_SB + 2 ^ 44 - 1).
Definition mz_chunk (j : nat) : YP09.chunk := YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (32 + j) 0)).
Definition mz_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 38;
YP09.mkRegion (Some 10%nat) 0 6 0 0 (map mz_chunk (seq 0 6)) ].
Definition mz_facts : facts :=
mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (10%nat, mkAF 4096 140737479966720 3) ::
map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 6) ++ [(38%nat, mkAF MZ_SB MZ_SB 0)]) [] [].
Definition ss_mz : sstate := mkSS AF_mac_is_zero sr_atoms mz_regions None mz_facts.
Definition mz_SH : list shent := [ mkSHE 10 0 6 ].
Definition mzb (M : list byte) (j : nat) : Z := bv_unsigned (nth j M (Z_to_bv 8 0)).
Definition mz_extra (M : list byte) : list word :=
map (fun j => Z_to_bv 64 (mzb M j)) (seq 0 6) ++ [Z_to_bv 64 MZ_SB].
Definition EM (regs : bvmap 5 word) (M : list byte) : env := Eimg (Ereg regs (mz_extra M)).
Lemma mzb_range : forall M j, 0 <= mzb M j < 256.
Proof.
intros M j. unfold mzb. pose proof (bv_unsigned_in_range 8 (nth j M (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma mz_ew : forall regs M,
(forall n, (32 <= n < 38)%nat -> ew (EM regs M) n = Z_to_bv 64 (mzb M (n - 32))) /\
ew (EM regs M) 38 = Z_to_bv 64 MZ_SB.
Proof.
intros regs M. split; [|reflexivity].
intros n Hn. do 32 (destruct n as [|n]; [lia|]).
do 6 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
Lemma mz_afact_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> afact_ok E n (mkAF 0 255 0).
Proof.
intros E n v H Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma mz_aview_val : forall (W : world SEGS) mem a v,
aview SEGS (w_H W) mem a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 v.
Proof.
intros W mem a v Ha Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
injection Ha as <-. f_equal.
unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma mz_entry : forall ly S W (regs : bvmap 5 word) mem md ch (p : Z) (M : list byte),
afn_pre SEGS B MAC_IS_ZERO_STKB ly S W regs mem md ch -> getr regs 10 = w64 p ->
afobj SEGS B ly S W mem p 6 ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
st_ok_pi SEGS VAL (EM regs M) ss_mz (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_mac_is_zeroP) mem (seg_rom SEGS)))
/\ sh_ok SEGS MZx mz_SH (EM regs M) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch p M HPRE H10 HFO HM.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : MAC_IS_ZERO_STKB = 4112) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (GB : forall j, (j < 6)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (p + Z.of_nat j) 1 (mzb M j)).
{ intros j Hj. apply mz_aview_val; [|apply mzb_range].
pose proof (HM (Z.of_nat j) ltac:(lia)) as Hj'. rewrite Nat2Z.id in Hj'. exact Hj'. }
rewrite restrict_mkst_fx.
destruct (mz_ew regs M) as [EX E38].
set (E := EM regs M) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (mz_extra M)) n)
by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_mz, AB_mac_is_zeroP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold mz_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 MZx MZ_SB);
[cbn [sv_denot MZx]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold MZ_SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold mz_chunk.
apply (chunk_ok_val SEGS E _ p (Z.of_nat j) 1 (SOff (32 + j) 0) (mzb M j)).
-- cbn [sv_denot]. rewrite (EX (32 + j)%nat) by lia. replace (32 + j - 32)%nat with j by lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- pose proof (mzb_range M j). zside.
-- zside.
-- exact (GB j ltac:(lia)).
+ apply pairwise_disjoint_of_extents. unfold mz_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat p E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hf4096 Hfceil Hflo Hfhi Hfimg C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [mz_facts f_atoms atoms_ok map seq app Nat.add].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 3) with 8;
revert Hf4096 Hfceil Hflo Hfhi Hp8 C1; clear; intros; repeat split; lia|].
repeat match goal with
| |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
split; [apply (mz_afact_byte E n (mzb M (n - 32))); [apply EX; lia | apply mzb_range] |]
end.
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, unsigned_lit_small by (unfold MZ_SB; lia).
rewrite Z.pow_0_r, Z.mod_1_r. unfold MZ_SB. lia.
- unfold sh_ok, mz_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E MZx 10 p 6 p 0 6 HRA).
+ unfold U, MZx. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold MZ_SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
(* 0x81a74 beqz a7, a7 = (p != 0) xor (-(p + j) = 0): the UBSan trap side (to the unimp at 0x81acc) is not taken,
   since 4096 <= p and p + j < 2^64. *)
Lemma mz_ubsan_ok : forall E (p j : Z), ew E 10 = Z_to_bv 64 p -> 4096 <= p -> p + 6 <= 2 ^ 47 -> 0 <= j < 6 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_SUB (SLit 0) (SOff 10 j)) (SLit 1))))
(sv_denot E (SLit 0)) = false.
Proof.
intros E p j H10 Hp Hp6 Hj.
assert (U1 : U E (SOff 10 j) = p + j).
{ rewrite U_SOff, H10, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U2 : U E (SAlu ALU_SUB (SLit 0) (SOff 10 j)) = 2 ^ 64 - (p + j)).
{ rewrite U_SAlu, U_SLit, U1. cbn [zalu_raw]. unfold zcanon, M64. rewrite Zmod_0_l.
replace (0 - (p + j)) with ((2 ^ 64 - (p + j)) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
assert (U3 : U E (SAlu ALU_SLTU (SAlu ALU_SUB (SLit 0) (SOff 10 j)) (SLit 1)) = 0).
{ rewrite U_SAlu, U2, U_SLit. cbn [zalu_raw]. unfold zcanon, M64. rewrite (Z.mod_small 1) by lia.
replace (2 ^ 64 - (p + j) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite branch_eq_U, U_SAlu, U3, !U_SLit. reflexivity.
Qed.
(* 0x81a90 bnez a7, a7 = mac[j]: the branch condition as a fact on the byte. *)
Lemma mz_hc_byte : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = negb b.
Proof.
intros E n v b Hn Hv Hb. rewrite branch_ne_U, (U_atom E n v Hn ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hb.
subst b. rewrite Bool.negb_involutive. reflexivity.
Qed.
(* The value returned at 0x81ac8 (seqz a0, a7 at 0x81abc): a7 = mac[j] <> 0 for the first nonzero byte, or a7 = mac[5]
   = 0 when the six bytes are 0. *)
Lemma mz_ret_nz : forall M j, (j < 6)%nat -> mzb M j <> 0 ->
(M = Boxreg.zero6 /\ alu64 ALU_SLTU (Z_to_bv 64 (mzb M j)) (Z_to_bv 64 1) = w64 1) \/
(M <> Boxreg.zero6 /\ alu64 ALU_SLTU (Z_to_bv 64 (mzb M j)) (Z_to_bv 64 1) = w64 0).
Proof.
intros M j Hj Hnz. right. split.
- intros Ez. apply Hnz. unfold mzb. rewrite Ez. unfold Boxreg.zero6. rewrite nth_repeat. reflexivity.
- pose proof (mzb_range M j) as R. apply bv_eq. rewrite alu64_unsigned, !unsigned_lit_small by lia. cbn [zalu_raw].
replace (mzb M j <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma mz_ret_z : forall M, length M = 6%nat -> (forall j, (j < 6)%nat -> mzb M j = 0) ->
(M = Boxreg.zero6 /\ alu64 ALU_SLTU (Z_to_bv 64 (mzb M 5)) (Z_to_bv 64 1) = w64 1) \/
(M <> Boxreg.zero6 /\ alu64 ALU_SLTU (Z_to_bv 64 (mzb M 5)) (Z_to_bv 64 1) = w64 0).
Proof.
intros M HL HZ. left. split.
- apply BoxregStep.bx_zero6_of; [exact HL|]. intros i Hi.
rewrite (nth_error_nth' M (Z_to_bv 8 0)) by lia. f_equal. apply bv_eq. exact (HZ i Hi).
- rewrite (HZ 5%nat ltac:(lia)). apply bv_eq. rewrite alu64_unsigned. reflexivity.
Qed.
Theorem pbb_mac_is_zero : tbmac_is_zero_spec.
Proof.
unfold tbmac_is_zero_spec.
intros ly S W regs mem md ch p M HPRE H10 HFO HLEN HM.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (mz_entry ly S W regs mem md ch p M HPRE H10 HFO HM) as [HS SHOK].
pose proof (ajournal_init SEGS B MAC_IS_ZERO_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HpB : 4096 <= p /\ p + 6 <= 2 ^ 47).
{ pose proof HFO as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _).
pose proof (asan_consts) as (C1 & _ & _ & _ & _). lia. }
destruct HpB as [Hp4096 Hp47].
destruct (mz_ew regs M) as [EX E38].
remember (EM regs M) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EM; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (mz_extra M)) n)
by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (mz_extra M)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 AB_mac_is_zeroP) with (Z_to_bv 64 AB_mac_is_zeroP).
(* The return at 0x81ac8, after ld ra and addi sp,sp,16: a0 = seqz mac[j]. A taken 0x81a90 (mac[j] <> 0) gives 0;
   the fall-through of the last 0x81aa4 (all six bytes 0) gives 1. *)
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in let mat' := fresh "mat" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold tbmac_is_zero_post, apost_base; eexists ly, S, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (mz_extra M) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
| vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
cbn [ms_regs]; rewrite R10;
lazymatch goal with
| Hc : branch_taken BC_NE (sv_denot ?E' (SOff ?n 0)) (sv_denot _ (SLit 0)) = true |- _ =>
let Hz := fresh "Hz" in
pose proof (mz_hc_byte E' n (mzb M (n - 32)) true ltac:(cbn [ew ewset Nat.eqb]; apply EX; lia) (mzb_range M (n - 32)) Hc) as Hz;
rewrite (EX n) by lia;
apply (mz_ret_nz M (n - 32)); [lia | apply Z.eqb_neq; exact Hz]
| _ =>
repeat match goal with Hc : branch_taken BC_NE (sv_denot ?E' (SOff ?n 0)) (sv_denot _ (SLit 0)) = false |- _ =>
let Hz := fresh "Hz" in
pose proof (mz_hc_byte E' n (mzb M (n - 32)) false ltac:(cbn [ew ewset Nat.eqb]; apply EX; lia) (mzb_range M (n - 32)) Hc) as Hz;
clear Hc; cbn [negb Nat.sub] in Hz; apply Z.eqb_eq in Hz
end;
rewrite (EX 37%nat) by lia;
apply (mz_ret_z M HLEN); intros j Hj; do 6 (destruct j as [|j]; [assumption|]); lia
end
end in
(* The trap side of 0x81a74 has a false condition. *)
let trap := idtac;
lazymatch goal with
| Hc : branch_taken BC_EQ (sv_denot ?E' (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_SUB (SLit 0) (SOff 10 ?j)) (SLit 1)))) _ = true |- _ =>
exfalso; rewrite (mz_ubsan_ok E' p j ltac:(cbn [ew ewset Nat.eqb]; exact E10) Hp4096 Hp47 ltac:(lia)) in Hc; discriminate Hc
end in
(* The loop at 0x81a60 is unrolled: the engine decides 0x81a60 bltu, 0x81a78 beqz p and 0x81aa4 bnez (5 - j <> 0) and
   takes the slow path of every shadow check (shadow byte 6, (p + j) & 7 = j < 6) back to the load at 0x81a8c; it stops
   at 0x81a74 (the UBSan check), at 0x81a90 (mac[j] <> 0) and at the return. *)
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK MZspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM MZx mz_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K MZx MZspan mz_SH (start K MZx MZspan mz_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch BC_EQ (SAlu ALU_XOR _ _) _ => psrr_branch_tok RUN BR HS' SHOK' MZspan; [trap | go]
| SR_branch BC_NE (SOff _ 0) (SLit 0) => psrr_branch_tok RUN BR HS' SHOK' MZspan; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
End f.
End d.
