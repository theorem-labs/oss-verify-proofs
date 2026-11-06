(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e) twin of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v at a working branch 5aae1e8a0ce, in that file's shape but NOT its text: image B's code is 96 bytes where image A's is 80, because the UBSan build adds the overflow guard `not a5,a3; bltu a5,a4' at 0x83604 / 0x83608 and the `mul a4,a0,a2' that feeds it, so this walk adds that branch and the refutation of its trap arm (0x83638).  The contract also differs: image B drops image A's `arodata_okP' premise, and the write right is `twr_ok', which per destination byte adds `~ aowned B lyc Sc a' and `~ (sp - ESTACK <= a < sp)' to image A's `awr_byte' and `apresent'. *)
(* Image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e) walk of
   reac_ctrl_identity_poll_block, 0x835dc = BASE 0x80a3c + AF_reac_ctrl_identity_poll_block 0x2ba0
   (lib/B/Prog/GrantList.v).  The one theorem of this file is
   GrantBContracts.walk_reac_ctrl_identity_poll_block; the contract is stated there and is only REFERRED to
   here.

   Ported from lib/A/Prog/CtrlIdentityPollBlock.v (image A, 0x82d3c) at a working branch 5aae1e8a0ce,
   whose AB01 blob is 1e6f4323d1e, a Theorem Labs lane's current generation.  Its whole Require closure inside this unit
   is 152 files, grepped for `Admitted|admit\b|Axiom|Parameter': 0 hits.  Every address, constant and byte
   below is image B's, and the shape of the proof is image A's, not its text: the segments are grantsegsB0
   (GrantTop.v), the listing is lib/B/Prog/GrantList.v, the table GRANT_GROUPB is image B's object 19
   (B_GROUPB; 0x21080, 204 bytes, GrantBContracts.b_groupb_check), the registered-global list is
   GRANT_GLOBS_B, __asan_memcpy is SIGMA GS___asan_memcpy (image B's 0x51b88, through RT_MEMCPY), and the
   image range is GrantTop.v's IMG_LO_B 0x10000 / IMG_TOP_B 0x5fb000, computed from image B's PT_LOADs.  No
   image-A number appears.

   Image B's 24 slots (0x2ba0 .. 0x2bfc):
     0x835dc addi sp,sp,-16        0x835e0 sd ra,8(sp)       0x835e4 li a3,5        0x835e8 li a2,-1
     0x835ec bltu a3,a0,0x83628    0x835f0 beq a1,zero,0x83628                      0x835f4 li a2,34
     0x835f8 auipc a3,..           0x835fc mul a4,a0,a2      0x83600 addi a3,a3,..  (a3 = GRANT_GROUPB)
     0x83604 not a5,a3             0x83608 bltu a5,a4,0x83638 (unimp)
     0x8360c mul a0,a0,a2          0x83610 add a3,a3,a0      0x83614 li a2,34
     0x83618 mv a0,a1              0x8361c mv a1,a3          0x83620 call __asan_memcpy
     0x83624 li a2,0               0x83628 mv a0,a2          0x8362c ld ra,8(sp)
     0x83630 addi sp,sp,16         0x83634 ret               0x83638 unimp
   Three arms reach the epilogue 0x83628 with a2 = -1 (i >u 5), a2 = -1 (o = 0) and a2 = 0 (after the copy),
   so the walk replays the epilogue per arm.  The o = 0 arm is refuted (twr_ok gives 4096 <= o through
   awr_byte_cases) and the trap branch at 0x83608 is refuted (i <=u 5 gives 34 * i <= 170, and the table's
   image bound gives ~GRANT_GROUPB >= 2 ^ 64 - 1 - 0x5fb000).  No report entry is reachable. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1h ACj1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the address-free facts of the index and of the table's rows ---------------------------------------- *)
Lemma ipb_le5 : forall i, - 2 ^ 31 <= i < 2 ^ 31 -> (i mod 2 ^ 64 <=? 5) = ((0 <=? i) && (i <=? 5))%bool.
Proof.
intros i Hi. destruct (Z_lt_le_dec i 0) as [Hneg|Hpos].
- rewrite <- (Z.mod_add i 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (i + 1 * 2 ^ 64)) by lia.
replace (0 <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
apply Z.leb_gt. lia.
- rewrite (Z.mod_small i) by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. reflexivity.
Qed.
Lemma ipb_gbz_len : forall i, length (GBz i) = 34%nat.
Proof.
intros i. unfold GBz, gb_tail.
repeat (match goal with |- context [if ?c then _ else _] => destruct c end); reflexivity.
Qed.
Lemma ipb_gball_nth : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat ->
nth (Z.to_nat (34 * i) + j)%nat GBallz 0 = nth j (GBz i) 0.
Proof.
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]]; intros j Hj;
(do 34 (destruct j as [|j]; [vm_compute; reflexivity|]); exfalso; lia).
Qed.
Lemma ipb_gbz_rangeb : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat ->
((0 <=? nth j (GBz i) 0) && (nth j (GBz i) 0 <? 256))%bool = true.
Proof.
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]]; intros j Hj;
(do 34 (destruct j as [|j]; [vm_compute; reflexivity|]); exfalso; lia).
Qed.
Lemma ipb_gbz_range : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat -> 0 <= nth j (GBz i) 0 < 256.
Proof.
intros i Hi j Hj. pose proof (ipb_gbz_rangeb i Hi j Hj) as H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma ipb_gball_len : length GBallz = 204%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma ipb_sh_small : forall x, 0 <= x -> x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x H0 H1. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 H0 ltac:(lia)).
assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma ipb_hull_small : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (2147450880 + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
(* `not a5, a3` at 0x83604 is `xori a5, a3, -1`: its unsigned value is the 64-bit complement. *)
Lemma ipb_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|].
apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ipb_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite ipb_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_id. unfold M64. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The entry of image B's reac_ctrl_identity_poll_block.  The stack it needs is
   STK_reac_ctrl_identity_poll_block (GrantBContracts.v): its own 16-byte frame and __asan_memcpy's ESTACK. *)
Definition A_ipb_B : Z := BASE + AF_reac_ctrl_identity_poll_block.
Definition IPB_SB : Z := 0x7fff8000.
(* GRANT_GROUPB of image B: object B_GROUPB = 19, address 0x21080, 204 bytes. *)
Definition A_GROUPB_B : Z := VAL (A_OBJ B_GROUPB).
Lemma ipb_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma ipb_mbyte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* `add a3, a3, a0` at 0x83610, with a3 = GRANT_GROUPB and a0 = 34 * i (the `mul` at 0x8360c).  The walk
   engine's canonical form of that sum names the product first. *)
Lemma ipb_denot_tbl : forall E np ni p i, ew E np = Z_to_bv 64 p -> ew E ni = Z_to_bv 64 i ->
0 <= p -> p + 34 * i + 34 <= 2 ^ 63 -> 0 <= i < 6 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff ni 0) (SLit 34)) (SOff np 0)) = Z_to_bv 64 (p + 34 * i).
Proof.
intros E np ni p i Hp Hi Rp Rpi Ri. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite U_SLit, (U_atom E ni i Hi), (U_atom E np p Hp) by lia.
rewrite (zcanon_id 34) by (unfold M64; lia). rewrite (zcanon_id (i * 34)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ipb_aview_of_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.
Section h.
Variable B : asyms.
Definition IBx : sv := SOff 32 0.
Definition IBspan : Z * Z := (IPB_SB, IPB_SB + 2 ^ 44 - 1).
Definition ipb_regions : smem := [ stack_region 16 ].
Definition ipb_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] [].
Definition ss_ipb : sstate := mkSS AF_reac_ctrl_identity_poll_block sr_atoms ipb_regions None ipb_facts.
Definition ipb_SH : list shent := [].
Definition EI (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma ipb_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_identity_poll_block -> spZ regs <= sp0 ->
st_ok_pi SEGS VAL (EI regs) ss_ipb
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_ipb_B) memc (seg_rom SEGS)))
/\ sh_ok SEGS IBx ipb_SH (EI regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hlo Hhi.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold STK_reac_ctrl_identity_poll_block in Hlo; lia).
rewrite restrict_mkst_fx.
set (E := EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_ipb, A_ipb_B. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ipb_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable SEGS). apply Hpres.
unfold STK_reac_ctrl_identity_poll_block in Hlo. lia.
+ cbn [ipb_regions pairwise_disjoint all_disjoint]. exact (conj I I).
+ split; [|split; [exact I | exact I]].
cbn [ipb_facts f_atoms atoms_ok].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, ipb_SH. apply Forall_nil.
Qed.
(* Every byte the caller let the call write lies outside image B's loaded range: the destination is a client
   byte (the machine stack above alloc_ceiling, a heap block, a side-stack frame, or a frame's shadow) and
   image B's range ends at IMG_TOP_B = 0x5fb000. *)
Lemma ipb_off_img : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
AR_laws SEGS B ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
~ in_img SEGS a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a LAWS HJ Hw.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw)
as (_ & [[Hc1 _] | [[_ (b & n & Hbin & Hr & _)] | (cid & pos & Hown & [[_ Hr] | [Hs Hr]])]]).
- intros Hin. pose proof (pa_img_range a Hin) as Hir. rewrite IMG_TOP_B_val in Hir. lia.
- exact (blk_img SEGS B LAWS lyc Sc W memc mdc b n a HAR Hbin Hr).
- unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
apply (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR
ltac:(rewrite Hfrs; apply in_or_app; left; exact Hown) Hr).
- intros Hin. pose proof (pa_img_range a Hin) as Hir. rewrite IMG_TOP_B_val in Hir.
unfold kLowMemEnd in Hs. lia.
Qed.
Ltac ipb_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].
Ltac ipb_keep K H rg Wx HU :=
lazymatch type of K with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 16 <= a < spZ rg) ->
aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
by (intros a Ha Hn; apply (ipb_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
intros (r & Hin & Hr); vm_compute in Hin;
destruct Hin as [Hin | Hin]; [subst r | destruct Hin];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
rewrite HU in Hr; lia)
end.
(* The call keeps every byte that is present: each run of straight-line code grows the memory, and
   __asan_memcpy's contract keeps what is present across the copy. *)
Ltac ipb_pres0 :=
first [ assumption
| match goal with
| Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- apresent ?Hq ?mB ?x =>
apply (apresent_grows Hq mA mB x Hg); ipb_pres0
| Hp : forall a, apresent ?Hq ?mA a -> apresent ?Hq ?mB a |- apresent ?Hq ?mB ?x =>
apply (Hp x); ipb_pres0
end ].
(* The six conjuncts of tcj_kept, from: KALL (what the call keeps outside its own 16 + ESTACK window and
   outside [o, o + 34)), HARc (the caller's realization), HOFF (the destination is not in image B), HJF (the
   journal at return) and LYC (the caller's layout). *)
Ltac ipb_tcj KALL HARc HOFF HJF LYC :=
unfold tcj_kept;
split;
[ intros aa Haa Hww Hee; apply KALL; [lia | lia | exact Hee] |];
split;
[ intros bb mm ii Hbin Hii Hee;
lazymatch goal with LW : AR_laws _ _ |- _ =>
destruct (al_blocks _ _ LW _ _ _ _ _ bb mm HARc Hbin) as (_ & Hb4096 & Hbceil & _) end;
apply KALL; [lia | lia | exact Hee] |];
split;
[ intros aa Hin _ _; pose proof (pa_img_range aa Hin) as Hir;
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hir;
apply KALL; [lia | lia | intros Hcon; exact (HOFF aa Hcon Hin)] |];
split;
[ intros cid pos aa Hfin Hrr Hee;
lazymatch goal with LW : AR_laws _ _ |- _ =>
destruct (frames_bounds SEGS B LW _ _ _ _ _ cid pos HARc Hfin) as (Hf0 & Hfc & _) end;
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
pose proof (YCbq.shadow_addr_bounds (frame_addr LYC cid pos) ltac:(lia)) as Hs1;
pose proof (YCbq.shadow_addr_bounds (frame_addr LYC cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2;
pose proof (YCbq.shadow_range_end (frame_addr LYC cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply KALL;
[ destruct Hrr as [Hrr|Hrr]; lia | destruct Hrr as [Hrr|Hrr]; lia | exact Hee ] |];
split;
[ intros aa _ _ Hpr; ipb_pres0 |];
intros aa Haa;
pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _);
apply HpresF; lia.

Theorem pb_reac_ctrl_identity_poll_block : walk_reac_ctrl_identity_poll_block B.
Proof.
unfold walk_reac_ctrl_identity_poll_block, hyps_reac_ctrl_identity_poll_block,
tb_reac_ctrl_identity_poll_block_spec.
intros (LAWS & TL & AMEMCPY & HGM & HIMGSH).
unfold RT_LAWS in LAWS. unfold RT_PALIB in TL. unfold RT_MEMCPY in AMEMCPY.
unfold RT_GLOBS in HGM. unfold RT_IMGSH in HIMGSH.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i o
HJ Hra Hra4 Hgp Htp H10 Hi H11 Hal16 Hlo Hhi Hdisj Hwr Hamr HRAo Hhull Hsep Htbl HinG Hm1 Hm2.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_grant) (PI := PI)) as RET.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ipb_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hlo Hhi) as [HS SHOK].
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold twr_ok in Hwr.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold STK_reac_ctrl_identity_poll_block in Hlo; lia).
assert (Ho4096 : 4096 <= o).
{ destruct (Hwr o ltac:(lia)) as [Hw _].
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k o HJ Hw)
as (_ & [[Hc1 _] | [[[Ha1 _] _] | (cid & pos & _ & [[[Ha1 _] _] | [[Hs1 _] _]])]]); lia. }
assert (HOFF : forall a, o <= a < o + 34 -> ~ in_img SEGS a).
{ intros a Ha. exact (ipb_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a LAWS HJ
(proj1 (Hwr a Ha))). }
assert (Ho47 : o + 34 <= 140737488355327)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (HloU : sp0 - STK <= spZ regs - 4112) by (unfold STK_reac_ctrl_identity_poll_block in Hlo; lia).
assert (Hceil2 : alloc_ceiling <= spZ regs - 4112) by lia.
unfold STK_reac_ctrl_identity_poll_block in Hdisj.
(* The contract names image B's table by VAL (A_OBJ B_GROUPB); name it A_GROUPB_B everywhere below. *)
assert (HGBeq : VAL (A_OBJ B_GROUPB) = A_GROUPB_B) by reflexivity.
rewrite HGBeq in Htbl, Hsep, Hm1, Hm2.
rewrite IMG_LO_B_val in Hm1. rewrite IMG_TOP_B_val in Hm2.
assert (Htb0 : 0x10040 <= A_GROUPB_B /\ A_GROUPB_B + 268 <= 0x5fb000) by lia.
assert (Hmod : (spZ regs - 16 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite Hal16 in D1. rewrite Hsp0al in D2.
replace (spZ regs - 16 - sp0) with ((spZ regs / 16 - 1 - sp0 / 16) * 16) by lia.
apply Z_mod_mult. }
remember (EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
by (intros n Hn; subst E; unfold EI; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Eo19 : ew E (A_OBJ B_GROUPB) = Z_to_bv 64 A_GROUPB_B)
by (unfold A_GROUPB_B; subst E; unfold EI; apply Eimg_img; unfold A_OBJ, B_GROUPB, A_TEXT, A_LIM; lia).
assert (Eo19' : ew E 260%nat = Z_to_bv 64 A_GROUPB_B) by exact Eo19.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ui : U E (SOff 10 0) = i mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite Z_to_bv_unsigned. reflexivity. }
assert (Uo : U E (SOff 11 0) = o mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite Z_to_bv_unsigned. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_identity_poll_block)) with (Z_to_bv 64 A_ipb_B).
(* ---- 0x835dc .. 0x835ec: the frame, li a3,5 / li a2,-1, then `bltu a3,a0` ---- *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KA regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* 5 <u i : the index is out of range; the epilogue returns a2 = -1 *)
rewrite branch_ltu_U, U_SLit, Ui in Hc. rewrite (zcanon_id 5) in Hc by (unfold M64; lia).
apply Z.ltb_lt in Hc.
assert (Hout : ((0 <=? i) && (i <=? 5))%bool = false)
by (rewrite <- ipb_le5 by lia; apply Z.leb_gt; lia).
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KB regs W Usp. clear HFr.
lazymatch type of KB with forall a, _ -> _ -> aview _ _ ?mT a = _ =>
assert (KBA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; rewrite (KB a Ha Hn); exact (KA a Ha Hn)) end.
assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
~ (spZ regs - STK_reac_ctrl_identity_poll_block <= a < spZ regs) -> ~ (o <= a < o + 34) ->
aview SEGS (w_H W) _ a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn1 Hn2; unfold STK_reac_ctrl_identity_poll_block in Hn1;
exact (KBA a Ha ltac:(lia))).
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tb_reac_ctrl_identity_poll_block_post. split; [reflexivity|].
eexists _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
| vm_compute; reflexivity]|].
split.
{ cbn [ms_mem]. ipb_tcj KALL HARc HOFF HJ lyc. }
rewrite Hout. split; [cbn [ms_regs]; rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
intros a Ha. cbn [ms_mem]. exact (KBA a ltac:(lia) ltac:(lia)).
- (* 0 <= i <= 5 *)
rewrite branch_ltu_U, U_SLit, Ui in Hc. rewrite (zcanon_id 5) in Hc by (unfold M64; lia).
apply Z.ltb_ge in Hc.
assert (Hin5 : ((0 <=? i) && (i <=? 5))%bool = true)
by (rewrite <- ipb_le5 by lia; apply Z.leb_le; lia).
assert (Hi5 : 0 <= i <= 5).
{ apply andb_prop in Hin5 as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. lia. }
(* ---- 0x835f0: `beq a1,zero` ---- *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KC0 regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK IBspan.
+ (* the destination is 0: impossible, it is a client byte *)
exfalso.
lazymatch goal with H : branch_taken BC_EQ _ _ = true |- _ =>
rewrite branch_eq_U, Uo, U_SLit in H; rewrite (zcanon_id 0) in H by (unfold M64; lia);
apply Z.eqb_eq in H; rewrite (Z.mod_small o) in H by lia; lia end.
+ (* ---- 0x835f4 .. 0x83608: the table address and the overflow guard ---- *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KC1 regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK IBspan.
* (* ~GRANT_GROUPB <u 34 * i: false.  34 * i <= 170 and ~GRANT_GROUPB >= 2 ^ 64 - 1 - 0x5fb000 *)
exfalso.
lazymatch goal with H : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U, ipb_U_not in H;
rewrite (U_atom E 260%nat A_GROUPB_B Eo19') in H by lia;
rewrite U_SMd in H; cbn [zmd_raw] in H;
rewrite U_SLit, (U_atom E 10%nat i E10) in H by lia;
rewrite (zcanon_id 34) in H by (unfold M64; lia);
rewrite (zcanon_id (i * 34)) in H by (unfold M64; lia);
apply Z.ltb_lt in H; lia end.
* (* ---- 0x8360c .. 0x83620: the copy's arguments, then the call of __asan_memcpy ---- *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KC regs W Usp. clear HFr.
lazymatch type of KC with forall a, _ -> _ -> aview _ _ ?mT a = _ =>
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; rewrite (KC a Ha Hn); rewrite (KC1 a Ha Hn); rewrite (KC0 a Ha Hn);
exact (KA a Ha Hn)) end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
prreg HS (3%bv : bv 5) Rgp2. prreg HS (4%bv : bv 5) Rtp2.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (A_GROUPB_B + 34 * i))
(ipb_denot_tbl E 260%nat 10%nat A_GROUPB_B i Eo19' E10 ltac:(lia) ltac:(lia) ltac:(lia)) Ra1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
assert (HspT : spZ rT = spZ regs - 16)
by (unfold spZ at 1; rewrite Rsp2, Usp; rewrite unsigned_lit_small by lia; lia) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W rT mT
STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k o (A_GROUPB_B + 34 * i) 34
(spZ regs - 16 - sp0) _ HJ) end.
- rewrite Ra0, E11. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia.
- lia.
- lia.
- rewrite HspT. lia.
- exact Hmod.
- lia.
- lia.
- rewrite Rgp2, E3. exact Hgp.
- rewrite Rtp2, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
- intros a Ha. split; [exact (proj1 (Hwr a ltac:(lia))) | lia].
- exact Hamr.
- eapply (range_addressable_agree (aview SEGS (w_H W) memc) _ SHADOW_OFF o 34); [|exact HRAo].
intros x Hx. pose proof (ipb_sh_small x ltac:(lia) ltac:(lia)) as Hsx.
apply KT; lia.
- intros _ s Hs. pose proof (ipb_hull_small o 34 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hss.
rewrite (KT s ltac:(lia) ltac:(lia)). apply Hhull. exact Hs.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split.
- rewrite (KT a ltac:(lia) ltac:(lia)).
pose proof (proj1 (Htbl (Z.to_nat (a - A_GROUPB_B)) ltac:(rewrite ipb_gball_len; lia)) 0%nat ltac:(lia)) as V0.
replace (A_GROUPB_B + Z.of_nat (Z.to_nat (a - A_GROUPB_B)) + Z.of_nat 0) with a in V0
by (rewrite Z2Nat.id by lia; lia).
unfold aview. rewrite V0. discriminate.
- rewrite HspT. lia. }
split; [lia|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
lazymatch goal with HJX : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT ?mdT _ |- _ =>
destruct (ro_read_ok_glob SEGS B GRANT_GLOBS_B lyc Sc W mT mdT A_GROUPB_B 204
(A_GROUPB_B + 34 * i) 34 HGM HinG HIMGSH (proj1 HJX)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_LO; rewrite IMG_LO_B_val; lia)
ltac:(unfold IMG_HI; rewrite IMG_TOP_B_val; lia)) as [HRA' HH'] end.
split; [exact HRA' | intros _; exact HH']. }
cbv beta. intros W2 c2 _ Hpost.
destruct Hpost as (HW2 & regs2 & mem2 & md2 & Hc2 & HJX2 & HP2 & Ha0' & Heff & Hfrc & Hpres2).
subst W2. subst c2.
pose proof HJX2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2' & _ & _ & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply Hfrc; lia.
- intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
rewrite Usp in Ha. apply (apresent_writable SEGS). apply Hpres2'. lia. }
specialize (HSX HRKX). rewrite <- restrict_mkst_fx in HSX.
assert (SHOKX : sh_ok SEGS IBx ipb_SH (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
by (unfold sh_ok, ipb_SH; apply Forall_nil).
assert (HEIX : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB)))
by (apply img_env_havoc; [exact HEI | cbv; lia]).
(* ---- 0x83624 .. 0x83634: a2 := 0, the epilogue and the return ---- *)
paj_run_tok RUN HSX HJX2 SHOKX IBspan; [ipb_awr regs Usp|].
clear HF. ipb_keep HFr KD regs W Usp. clear HFr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
~ (spZ regs - STK_reac_ctrl_identity_poll_block <= a < spZ regs) -> ~ (o <= a < o + 34) ->
aview SEGS (w_H W) _ a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn1 Hn2; unfold STK_reac_ctrl_identity_poll_block in Hn1;
rewrite (KD a Ha ltac:(lia)); rewrite (Hfrc a Ha ltac:(lia) ltac:(lia));
exact (KT a Ha ltac:(lia))).
prreg HSX (10%bv : bv 5) R10. prreg HSX (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HSX eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tb_reac_ctrl_identity_poll_block_post. split; [reflexivity|].
eexists _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJX2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HSX);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
| vm_compute; reflexivity]|].
split.
{ cbn [ms_mem]. ipb_tcj KALL HARc HOFF HJX2 lyc. }
rewrite Hin5. split; [cbn [ms_regs]; rewrite R10; reflexivity|].
intros j Hj. rewrite ipb_gbz_len in Hj. split.
{ intros kk Hkk. assert (Hkk0 : kk = 0%nat) by lia. subst kk.
pose proof (proj1 (Htbl (Z.to_nat (34 * i) + j)%nat ltac:(rewrite ipb_gball_len; lia)) 0%nat ltac:(lia)) as V0.
rewrite <- (ipb_gball_nth i Hi5 j Hj). cbn [ms_mem]. rewrite <- V0.
replace (A_GROUPB_B + Z.of_nat (Z.to_nat (34 * i) + j) + Z.of_nat 0)
with (A_GROUPB_B + 34 * i + Z.of_nat j) by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
replace (o + Z.of_nat j + Z.of_nat 0) with (o + Z.of_nat j) by lia.
apply ipb_mbyte_eq.
rewrite (KD (o + Z.of_nat j) ltac:(lia) ltac:(lia)).
rewrite (Heff (Z.of_nat j) ltac:(lia)).
exact (KT (A_GROUPB_B + 34 * i + Z.of_nat j) ltac:(lia) ltac:(lia)).
}
exact (ipb_gbz_range i Hi5 j Hj).
Qed.
End h.
End f.
End d.
(* The flag is set `false' at the top of this file (its own proof is closed under that), with `Local' so the
   setting does not leave the file, and set to `true' on the file's last line (:566), after every proof, again with
   `Local', so that this file exports no setting of the flag. Stdlib's Zify.v defines it `constr:(false)', and its
   ZifyNat and ZifyN redefine it `constr:(true)' when loaded; LinuxProcessSemantics's BvBase loads ZifyNat, so after
   this file's Stdlib and LinuxProcessSemantics Requires `Print Ltac Zify.zify_convert_to_euclidean_division_equations_flag'
   shows `constr:(true)' (Rocq 9.2, the checker image). A requirer sees the value its own Requires leave; one whose
   `lia' needs a given value on a goal with `mod' or `/' sets it `Local' itself. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
