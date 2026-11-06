(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_headamp_record_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_headamp_record_verify on image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48), proving image B's contract walk_reac_ctrl_headamp_record_verify of lib/B/Prog/GrantBContracts.v over image B's listing; image B's code is NOT the same as image A's: it is 36 bytes longer (UBSan's five trap guards and three report branches, refuted here, one of them through the six assumed loop guards hrv_conds), and its shadow-base cell is object 35 where image A's is object 32. *)
(* Ported from lib/A/Prog/CtrlHeadampRecordVerify.v at a working branch 5aae1e8a0ce (identical at a working branch afd75724b5b). *)
(* Image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e) walk of
   reac_ctrl_headamp_record_verify (0x834dc = BASE + AF_reac_ctrl_headamp_record_verify 0x2aa0), the port of
   lib/A/Prog/CtrlHeadampRecordVerify.v to image B's listing and walk layer (lib/B/Prog).

   a0 = f, the 50-byte frame object of check_groupa. The call reads f[18]; when it is 4 it reads f[19]; when that
   is 3 it sums the six bytes f[34..40) and returns 0 when the sum is 0 mod 128; every other case returns -1
   (RcLeaf.hv). It writes nothing outside its own 16-byte frame and takes no call.

   Image B's own bytes (read from bin/fuzz_grant/fuzz_grant.asan-ubsan), the five trap sites and the three report
   branches this walk refutes:
     0x834e4 beqz a0            -> 0x835b8 unimp     (f = 0)
     0x834ec bgeu a0, -0x12     -> 0x835b8 unimp     (f >=u 2^64 - 18)
     0x83524 bltu -0x14, a0     -> 0x835b8 unimp     (f >u 2^64 - 20)
     0x8354c bltu -0x11, a1     -> 0x835b8 unimp     (f + 18 >u 2^64 - 17)
     0x83564 bltu a5, a2        -> 0x835b8 unimp     (~(f + 34) <u j)
     0x835c8 jal __asan_report_load1   (load1 at f + 18, returns into 0x835cc)
     0x835d8 jal __asan_report_load1   (load1 at f + 19; the LAST instruction, falls into
                                        reac_ctrl_identity_poll_block 0x835dc)
     0x83598 jal __asan_report_load1   (load1 at f + 34 + j, returns into 0x8359c)
   The five traps are false from afobj (4096 <= f and f + 50 <= alloc_ceiling); the three report branches are
   false from afobj's shadow conjunct, carried through sh_ok.
   The shadow base is read through the GOT at 0x834f0 / 0x834f4 (PHi (11) 32 / PLdHi .. (A_OBJ 1) ..): on image B
   the GOT word is object 1 and the cell it points at is object 35 (lib/B/Prog/GrantPaLib.v PALib), where image
   A's cell is object 32. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLeaf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the address-free arithmetic of the six-byte sum (shared with image A's walk) ----------------------- *)
Fixpoint hrv_zsum (RS : list Z) (k : nat) : Z :=
match k with O => 0 | S k' => hrv_zsum RS k' + nth k' RS 0 end.
Lemma hrv_zsum_range : forall RS k, (forall j, (j < k)%nat -> 0 <= nth j RS 0 < 256) ->
0 <= hrv_zsum RS k <= 255 * Z.of_nat k.
Proof.
intros RS k. induction k as [|k IH]; intros H; cbn [hrv_zsum]; [lia|].
pose proof (H k ltac:(lia)). pose proof (IH ltac:(intros j Hj; apply H; lia)). lia.
Qed.
Lemma hrv_psum_map : forall RS k, (forall j, (j < k)%nat -> 0 <= nth j RS 0 < 256) ->
psum (map (Z_to_bv 8) RS) k = hrv_zsum RS k.
Proof.
intros RS k. induction k as [|k IH]; intros H; cbn [psum hrv_zsum]; [reflexivity|].
rewrite IH by (intros j Hj; apply H; lia). f_equal.
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. apply H. lia.
Qed.
Lemma hrv_add0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
intros x. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite Z_to_bv_unsigned.
unfold bv_wrap. rewrite Zmod_0_l, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 x) as R. apply Z.mod_small. exact R.
Qed.
(* 0x8359c andi a0,a1,0x7f; 0x835a0 seqz a2,a0; 0x835a4 addi a2,a2,-1 *)
Lemma hrv_fin : forall s, 0 <= s < 2 ^ 64 ->
alu64 ALU_ADD (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 s) (Z_to_bv 64 127)) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)) =
w64 (if s mod 128 =? 0 then 0 else -1).
Proof.
intros s Hs. unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small s) by lia. change (127 mod 2 ^ 64) with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
pose proof (Z.mod_pos_bound s 128 ltac:(lia)) as M.
rewrite (Z.mod_small (s mod 128)) by lia. change (1 mod 2 ^ 64) with 1. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
destruct (Z.eqb_spec (s mod 128) 0) as [E|E].
- rewrite E. reflexivity.
- replace (s mod 128 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* Image B's loop guard 0x83564 `bltu a5, a2`, which image A's build has not got: a5 is
   `not (f + 34)` (0x8355c `not a5,a3`), whose symbolic form SAlu ALU_XOR (SOff 10 34) (SLit (-1))
   carries no range in YP0m.v's sv_range, so the walk hands the engine the six guards it needs as
   assumed conditions (j = 0 .. 5, the loop's counter). Each is proved here from f's own range. *)
Lemma hrv_novf : forall E (v j : Z), ew E 10 = Z_to_bv 64 v -> 0 <= v <= 140737479966720 -> 0 <= j <= 5 ->
acond_ok E (mkAC BC_GEU (SAlu ALU_XOR (SOff 10 34) (SLit (-1))) (SLit j)).
Proof.
intros E v j Hv Hr Hj. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_not_off E 10 v 34 Hv ltac:(lia) ltac:(lia)), (U_lit E j ltac:(lia)).
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Definition B_hrv_entryP : Z := BASE + AF_reac_ctrl_headamp_record_verify.
Definition HRV_SB : Z := 0x7fff8000.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
(* atoms 32, 33 are f[18], f[19]; 34..39 the record bytes f[34..40); atom 40 is the shadow base. *)
Definition HBx : sv := SOff 40 0.
Definition HBspan : Z * Z := (HRV_SB, HRV_SB + 2 ^ 44 - 1).
Definition hrv_chunk (j : nat) : YP09.chunk := YP09.mkChunk (34 + Z.of_nat j) (CVal 1 (SOff (34 + j) 0)).
Definition hrv_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 40;
YP09.mkRegion (Some 10%nat) 0 50 0 0
(YP09.mkChunk 18 (CVal 1 (SOff 32 0)) :: YP09.mkChunk 19 (CVal 1 (SOff 33 0)) :: map hrv_chunk (seq 0 6)) ].
Definition hrv_nv : sv := SAlu ALU_XOR (SOff 10 34) (SLit (-1)).
Definition hrv_conds : list acond :=
[ mkAC BC_GEU hrv_nv (SLit 0); mkAC BC_GEU hrv_nv (SLit 1); mkAC BC_GEU hrv_nv (SLit 2);
  mkAC BC_GEU hrv_nv (SLit 3); mkAC BC_GEU hrv_nv (SLit 4); mkAC BC_GEU hrv_nv (SLit 5) ].
Definition hrv_facts : facts :=
mkFacts ((2%nat, mkAF (2^46) (2^47) 4) :: (10%nat, mkAF 4096 140737479966720 3) ::
map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 8) ++ [(40%nat, mkAF HRV_SB HRV_SB 0)]) hrv_conds [].
Definition ss_hrv : sstate := mkSS AF_reac_ctrl_headamp_record_verify sr_atoms hrv_regions None hrv_facts.
Definition hrv_SH : list shent := [ mkSHE 10 0 50 ].
Definition hrv_extra (b0 b1 : Z) (REC : list Z) : list word := map (Z_to_bv 64) ((b0 :: b1 :: REC) ++ [HRV_SB]).
Definition EH (regs : bvmap 5 word) (b0 b1 : Z) (REC : list Z) : env := Eimg (Ereg regs (hrv_extra b0 b1 REC)).
Lemma hrv_ew : forall regs b0 b1 REC, length REC = 6%nat ->
(forall n, (32 <= n < 40)%nat -> ew (EH regs b0 b1 REC) n = Z_to_bv 64 (nth (n - 32) (b0 :: b1 :: REC) 0)) /\
ew (EH regs b0 b1 REC) 40 = Z_to_bv 64 HRV_SB.
Proof.
intros regs b0 b1 REC HL. unfold EH. split.
- intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra. unfold hrv_extra.
rewrite map_nth. rewrite app_nth1 by (cbn [length]; lia). reflexivity.
- rewrite Eimg_low by (unfold A_TEXT; lia).
replace 40%nat with (32 + 8)%nat by lia. rewrite ew_Ereg_extra. unfold hrv_extra.
rewrite map_nth. rewrite app_nth2 by (cbn [length]; lia). cbn [length]. rewrite HL. reflexivity.
Qed.
Lemma hrv_afact_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> afact_ok E n (mkAF 0 255 0).
Proof.
intros E n v H Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma hrv_entry : forall ly S W (regs : bvmap 5 word) mem md ch (f b0 b1 : Z) (REC : list Z),
afn_pre SEGS B STK_reac_ctrl_headamp_record_verify ly S W regs mem md ch -> getr regs 10 = w64 f ->
afobj SEGS B ly S W mem f 50 ->
garr8 SEGS (mrestrict (w_H W) mem) (f + 18) [b0; b1] ->
garr8 SEGS (mrestrict (w_H W) mem) (f + 34) REC -> length REC = 6%nat ->
st_ok_pi SEGS VAL (EH regs b0 b1 REC) ss_hrv
(restrict (w_H W) (mkst regs (Z_to_bv 64 B_hrv_entryP) mem (seg_rom SEGS)))
/\ sh_ok SEGS HBx hrv_SH (EH regs b0 b1 REC) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch f b0 b1 REC HPRE H10 HFO HB2 HBR HLEN.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hf8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_headamp_record_verify = 16) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgB B ly S W mem md cid pos HAR Hfin) as Hfimg.
pose proof IMG_LO_B_val as HLO. pose proof IMG_TOP_B_val as HTOP.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (GL : forall j, (j < 2)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (f + 18 + Z.of_nat j) 1 (nth j [b0; b1] 0) /\ 0 <= nth j [b0; b1] 0 < 256)
by (intros j Hj; apply HB2; cbn [length]; lia).
assert (GR : forall j, (j < 6)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (f + 34 + Z.of_nat j) 1 (nth j REC 0) /\ 0 <= nth j REC 0 < 256)
by (intros j Hj; apply HBR; lia).
rewrite restrict_mkst_fx.
destruct (hrv_ew regs b0 b1 REC HLEN) as [EX E40].
set (E := EH regs b0 b1 REC) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hrv_extra b0 b1 REC)) n)
by (intros n Hn; subst E; unfold EH; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eo35 : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_hrv, B_hrv_entryP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold hrv_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
[cbn [sv_denot]; rewrite Eo35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Eo35) by (pose proof (pa_val_range (A_OBJ 35)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 HBx HRV_SB);
[cbn [sv_denot HBx]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold HRV_SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat f E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
-- destruct (GL 0%nat ltac:(lia)) as [Gv Gr]. cbn [nth] in Gv, Gr.
apply (chunk_ok_val SEGS E _ f 18 1 (SOff 32 0) b0);
[cbn [sv_denot]; rewrite (EX 32%nat ltac:(lia)); cbn [Nat.sub nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| zside | zside | rewrite <- (Z.add_0_r (f + 18)) at 1; change (f + 18 + 0) with (f + 18 + Z.of_nat 0); exact Gv].
-- destruct (GL 1%nat ltac:(lia)) as [Gv Gr]. cbn [nth] in Gv, Gr.
apply (chunk_ok_val SEGS E _ f 19 1 (SOff 33 0) b1);
[cbn [sv_denot]; rewrite (EX 33%nat ltac:(lia)); cbn [Nat.sub nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| zside | zside | replace (f + 19) with (f + 18 + Z.of_nat 1) by (cbn [Z.of_nat]; lia); exact Gv].
-- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold hrv_chunk. destruct (GR j ltac:(lia)) as [Gv Gr].
apply (chunk_ok_val SEGS E _ f (34 + Z.of_nat j) 1 (SOff (34 + j) 0) (nth j REC 0)).
++ cbn [sv_denot]. rewrite (EX (34 + j)%nat) by lia. replace (34 + j - 32)%nat with (2 + j)%nat by lia.
cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
++ zside.
++ zside.
++ rewrite Z.add_assoc. exact Gv.
+ apply pairwise_disjoint_of_extents. unfold hrv_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat f E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Eo35) by (pose proof (pa_val_range (A_OBJ 35)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hf4096 Hfceil Hflo Hfhi Hfimg HLO HTOP C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
repeat split; lia.
+ split; [|split; [|exact I]].
2:{ cbn [hrv_facts f_conds hrv_conds conds_ok]. unfold hrv_nv.
assert (Hfb : 0 <= f <= 140737479966720)
by (revert Hf4096 Hfceil Hflo Hfhi C1; clear; intros; lia).
split; [exact (hrv_novf E f 0 E10 Hfb ltac:(lia))|].
split; [exact (hrv_novf E f 1 E10 Hfb ltac:(lia))|].
split; [exact (hrv_novf E f 2 E10 Hfb ltac:(lia))|].
split; [exact (hrv_novf E f 3 E10 Hfb ltac:(lia))|].
split; [exact (hrv_novf E f 4 E10 Hfb ltac:(lia))|].
split; [exact (hrv_novf E f 5 E10 Hfb ltac:(lia))|].
exact I. }
cbn [hrv_facts f_atoms atoms_ok map seq app Nat.add].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 3) with 8;
revert Hf4096 Hfceil Hflo Hfhi Hf8 C1; clear; intros; repeat split; lia|].
split; [apply (hrv_afact_byte E 32%nat b0); [rewrite (EX 32%nat ltac:(lia)); reflexivity | exact (proj2 (GL 0%nat ltac:(lia)))]|].
split; [apply (hrv_afact_byte E 33%nat b1); [rewrite (EX 33%nat ltac:(lia)); reflexivity | exact (proj2 (GL 1%nat ltac:(lia)))]|].
repeat match goal with
| |- afact_ok _ (34 + ?j)%nat (mkAF 0 255 0) /\ _ =>
split; [apply (hrv_afact_byte E (34 + j)%nat (nth j REC 0));
[rewrite (EX (34 + j)%nat ltac:(lia)); replace (34 + j - 32)%nat with (2 + j)%nat by lia; cbn [nth]; reflexivity
| exact (proj2 (GR j ltac:(lia)))] |]
| |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
split; [apply (hrv_afact_byte E n (nth (n - 34) REC 0));
[rewrite (EX n ltac:(lia)); replace (n - 32)%nat with (2 + (n - 34))%nat by lia; cbn [nth]; reflexivity
| exact (proj2 (GR (n - 34)%nat ltac:(lia)))] |]
end.
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E40, unsigned_lit_small by (unfold HRV_SB; lia).
rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, hrv_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E HBx 10 f 50 f 0 50 HRA).
+ unfold U, HBx. cbn [sv_denot]. rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold HRV_SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Lemma pb_hrv_core : tb_reac_ctrl_headamp_record_verify_spec B.
Proof.
unfold tb_reac_ctrl_headamp_record_verify_spec, tb_reac_ctrl_headamp_record_verify_post.
intros ly S W regs mem md ch f b0 b1 REC HPRE H10 HFO HB2 HLEN HBR.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (hrv_entry ly S W regs mem md ch f b0 b1 REC HPRE H10 HFO HB2 HBR HLEN) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_ctrl_headamp_record_verify [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Rb0 : 0 <= b0 < 256) by (exact (proj2 (HB2 0%nat ltac:(cbn [length]; lia)))).
assert (Rb1 : 0 <= b1 < 256) by (exact (proj2 (HB2 1%nat ltac:(cbn [length]; lia)))).
assert (GR : forall j, (j < 6)%nat -> 0 <= nth j REC 0 < 256) by (intros j Hj; apply HBR; lia).
destruct (hrv_ew regs b0 b1 REC HLEN) as [EX E40].
remember (EH regs b0 b1 REC) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EH; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hrv_extra b0 b1 REC)) n)
by (intros n Hn; subst E; unfold EH; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 b0) by (rewrite (EX 32%nat ltac:(lia)); reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 b1) by (rewrite (EX 33%nat ltac:(lia)); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (hrv_extra b0 b1 REC)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_headamp_record_verify)) with (Z_to_bv 64 B_hrv_entryP).
let hb H := rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?(U_atom E 32 b0 E32), ?(U_atom E 33 b1 E33) in H by lia; rewrite ?U_lit in H by lia;
try (apply (proj1 (negb_true_iff _)) in H); try (apply (proj1 (negb_false_iff _)) in H);
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H | idtac ] in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold apost_base; eexists ly, S, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (hrv_extra b0 b1 REC) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
| vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
cbn [ms_regs]; rewrite R10;
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hb H end;
unfold hv, rsum;
rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite (Z.mod_small b0 256) by lia; rewrite (Z.mod_small b1 256) by lia;
repeat (rewrite EX by lia); cbn [Nat.sub nth];
rewrite ?hrv_add0; rewrite ?alu64_add_lit;
repeat match goal with
| H : ?x = ?y |- context [(?x =? ?y)] => rewrite (proj2 (Z.eqb_eq x y) H)
| H : ?x <> ?y |- context [(?x =? ?y)] => rewrite (proj2 (Z.eqb_neq x y) H)
end; cbn [andb];
first
[ unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
| (lazymatch goal with |- context [alu64 ALU_AND (Z_to_bv 64 ?s) _] =>
replace s with (hrv_zsum REC 6) by (cbn [hrv_zsum]; lia) end);
rewrite hrv_fin by (pose proof (hrv_zsum_range REC 6 GR); lia);
rewrite (hrv_psum_map REC 6 GR); reflexivity
| match goal with |- ?g => idtac "HRV-RET" g end; fail 1 "HRV-RET: unexpected leaf" ]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK HBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM HBx hrv_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K HBx HBspan hrv_SH (start K HBx HBspan hrv_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' HBspan; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
Section w.
Variable B : asyms.
Theorem pb_reac_ctrl_headamp_record_verify : walk_reac_ctrl_headamp_record_verify B.
Proof. intros [HL HP]. exact (pb_hrv_core B HL HP). Qed.
End w.
End f.
End d.
