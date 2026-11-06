(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_headamp_record_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlHeadampRecordVerify.v, with its module paths, module names and numbers changed; 601 of its 685 lines of code are new or changed and 226 lines of the source are left out. *)
(* reac_boxreg_find (fuzz_boxreg.asan-ubsan 0x81928, 68 instructions): the contract of the ASan+UBSan build's code.
   The function takes an 80-byte frame on the machine stack (addi sp,sp,-80) and calls mac_is_zero (p) (0x81a38, a
   program function with its own contract, lib/B/Prog/BoxBMacIsZero.v); a nonzero result returns -1. Else it checks
   r against NULL and 4-byte alignment for UBSan, loads n = r->n at r + 280 after the check of that word's shadow
   byte and, for i = 0 .. n - 1, checks the box index (i = 5 traps) and the pointer r + 56 i for overflow, then calls
   bcmp (r + 56 i, mac, 6) through BS___interceptor_trampoline_bcmp (0x41464, the same address as __wrap_bcmp in the
   unstripped image's symbol table); it returns the first i whose result is 0, else -1. It writes nothing outside its
   own frame and the windows of its callees.
   Stack: the own 80-byte frame and below it the deeper of the two callees: mac_is_zero's MAC_IS_ZERO_STKB
   (16 + ESTACK) and the bcmp wrapper's 2 * ESTACK (abcmp_realizes asks for 2 * ESTACK of present stack below the
   caller's sp, CONVENTIONS section 4), so 80 + 2 * ESTACK.
   Read footprint, each byte covered by a premise: the 288-byte registry struct at r, a heap block of the caller
   (In (r, REG_SIZEB) (ablocks ..) and its bytes bs; the code reads r + 280 .. r + 283 and the MACs r + 56 i ..
   r + 56 i + 5 for i < n); the 6 MAC bytes M at p (afobj and their bytes; mac_is_zero reads them too, and this
   premise is the frame case of its premise); the shadow bytes of both (the __asan_report_load4 branch is refuted by
   the block's shadow in AR, the shadow checks of the MAC bytes are mac_is_zero's and bcmp's, discharged from afobj's
   range_addressable). The only image reads are the GOT word of the shadow base and the shadow cell, both fixed by AR
   (AR_const_law, lib/Reusable/YG0d.v); the bcmp wrapper's own reads are inside abcmp_realizes.
   Where the MAC lives: every caller passes the harness's local uint8_t mac[6] of LLVMFuzzerTestOneInput
   (fuzz/fuzz_boxreg.c:206), directly (:312, :336, :365) or as reac_boxreg_add's own argument (src/reac_boxreg.c:95).
   It is at offset 0x20 of the harness's 416-byte ASan frame block (0x801fc .. 0x80204: ld a0,0x18(s1);
   addi a0,a0,0x20; sd a0,0x68(s1)), whose shadow byte 4 the harness sets to 6 at its loop top (0x8028c .. 0x80290),
   so the 6 bytes are addressable at every call. That frame block is the __asan_stack_malloc_3 side-stack frame
   (0x8001c), a frame in frames S: AR fixes the use-after-return flag cell to 1 (AR_const_law), so the harness takes
   the fake-stack path and the MAC is not on the caller's machine stack. Hence the premise afobj SEGS B ly S W mem p 6,
   the form of grant's caller frame objects (fuzz_grant lib/A/Prog/CtrlChecksumVerify.v).
   Hazards: the struct is 288 bytes (rows 0..280, n at +280, fabric at +284; box i's MAC at 56 i); the UBSan traps
   (the unimp word 0xc0001073 at 0x81a24: beqz r at 0x819a4, andi r,3 at 0x819a8, the index test beq s4,280 at
   0x819e8, the overflow test bltu ~r,56 i at 0x819ec) are refuted by the allocator's block law (r is a multiple of 16,
   at least 4096, and r + 288 is below the allocator's ceiling) and by n <= 5 (Pau's boxreg_B1: i <= 4); the bcmp
   entry is the trampoline at 0x41464 (__wrap_bcmp is an alias of the same address), stated with abcmp_realizes, not
   amemcmp_realizes; no f* instruction occurs in the 68 instructions and the only csr word is that trap
   (csrrw zero,cycle,zero, an illegal-instruction trap that writes no FP state, on a refuted path), so the fixed {fx}
   is sound. The old walk's runtime cells (asan_cells, REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254/255, app_mem (p + 7))
   and its r <> 0, r mod 4 = 0, p <> 0 premises leave the statement: the first are premises of the runtime
   hypothesis, the others follow from the block law and from afobj's frame bounds.
   Image difference: the asan build (lib/A/Prog/ReacBoxregFind.v) inlines mac_is_zero, has a 48-byte frame and no
   UBSan checks; the result is the same.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_find_c.v find_result, lib/Prog/Boxreg.v boxreg_B1),
   used as it is. *)
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
(* REG_SIZEB, the size of struct reac_boxreg, is BoxBReacBoxregInit's; MAC_IS_ZERO_STKB is the callee's stack. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBMacIsZero.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_find_c.
(* The walk layer of the build-B listing (tactics, frame regions, the call lemma cl_callS). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h YC85 BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require BoxregRd.
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
(* The function's address in the image and the stack it needs: its own 80-byte frame and below it the deeper of
   mac_is_zero's stack and the bcmp wrapper's 2 * ESTACK. *)
Definition AB_reac_boxreg_findP : Z := BASE + AF_reac_boxreg_find.
Definition REAC_BOXREG_FIND_STKB : Z := 80 + Z.max MAC_IS_ZERO_STKB (2 * ESTACK).
Section h.
Variable B : asyms.
Definition tbreac_boxreg_find_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r p : Z) (bs M : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_FIND_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) /\
(forall i, 0 <= i < 6 ->
  aview SEGS (w_H W') mem' (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) /\
exists z, getr regs' 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z).
Definition tbreac_boxreg_find_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte),
afn_pre SEGS B REAC_BOXREG_FIND_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p ->
In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
(forall i, 0 <= i < 6 ->
  aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (cfg_at SEGS AB_reac_boxreg_findP regs mem md) (tbreac_boxreg_find_post regs ly S W mem md r p bs M).
(* ---------------------------------------------------------------------------------------------------------- *)
(* The walk. Entry state: the 80-byte frame, the GOT word of the shadow base (object 1) and its cell (object 12);
   atom 32 is the shadow base 0x7fff8000, atoms 10 / 11 are r / p. The jal at 0x81968 goes to mac_is_zero's contract
   (fnd_mz_call, cl_callS); a zero MAC returns -1. Else the walk adds the word n = r->n (a literal, one case per
   n = 0 .. 5 of boxreg_B1) and the shadow entry of r's block, which settles the null / alignment UBSan tests and the
   shadow check of r + 280; the scan loop is unrolled (at most five rounds), each round refuting the pointer-overflow
   trap at 0x819ec (r + 288 <= 2^47) and calling the bcmp wrapper (fnd_bcmp_call, aj_bcmp_at); the index trap at
   0x819e8 is never reached because n <= 5 ends the loop first. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes SEGS B (@pa_sigma _ boxb_listing PI BB___interceptor_trampoline_bcmp).
Hypothesis MZ : tbmac_is_zero_spec B.
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
Definition FSB : Z := 0x7fff8000.
Definition FBx : sv := SOff 32 0.
Definition FBspan : Z * Z := (FSB, FSB + 2 ^ 44 - 1).
Definition fnd_regions : smem := [ stack_region 80; got_regionP; bcell_regionP 32 ].
Definition fnd_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
(11%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF FSB FSB 0)] [] [].
Definition ss_fnd : sstate := mkSS AF_reac_boxreg_find sr_atoms fnd_regions None fnd_facts.
Definition fnd_extra : list word := [Z_to_bv 64 FSB].
Definition EF (regs : bvmap 5 word) : env := Eimg (Ereg regs fnd_extra).
Lemma fnd_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z),
afn_pre SEGS B REAC_BOXREG_FIND_STKB ly S W regs mem md ch -> getr regs 10 = w64 r -> getr regs 11 = w64 p ->
In (r, REG_SIZEB) (ablocks B ly S) -> afobj SEGS B ly S W mem p 6 ->
st_ok_pi SEGS VAL (EF regs) ss_fnd
(restrict (w_H W) (mkst regs (Z_to_bv 64 AB_reac_boxreg_findP) mem (seg_rom SEGS)))
/\ sh_ok SEGS FBx [] (EF regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r p HPRE H10 H11 Hin HFO.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZEB) with 288 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := EF regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs fnd_extra) n)
by (intros n Hn; subst E; unfold EF; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 FSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fnd, AB_reac_boxreg_findP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold fnd_regions, stack_region, got_regionP, bcell_regionP.
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
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 FBx FSB);
[cbn [sv_denot FBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold FSB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold fnd_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fnd_facts f_atoms atoms_ok].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 4) with 16;
revert Hr16 Hr4096 Hrceil C1; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E11, unsigned_lit_small by lia; change (2 ^ 3) with 8;
revert Hf4096 Hfceil Hflo Hfhi Hp8 C1; clear; intros; repeat split; lia|].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold FSB; lia).
rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok. apply Forall_nil.
Qed.
(* What the walk's journal keeps: the bytes (and shadow bytes) of the caller's frames and the bytes of the heap
   blocks of the entry state. *)
Lemma fnd_jkept_frame : forall sp0 ly S W mem md memT mdT k cid pos a,
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S W memT mdT k ->
In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a.
Proof.
intros sp0 ly S W mem md memT mdT k cid pos a HJ Hin Hz.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
exact (K4 cid pos a Hin Hz (inFP_nil a)).
Qed.
Lemma fnd_jkept_block : forall sp0 ly S W mem md memT mdT k b m i,
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S W memT mdT k ->
In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
aview SEGS (w_H W) memT (b + i) = aview SEGS (w_H W) mem (b + i).
Proof.
intros sp0 ly S W mem md memT mdT k b m i HJ Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
exact (K2 b m i Hin Hin Hi (inFP_nil _)).
Qed.
Lemma fnd_mac_zone : forall F nb p x, F mod 8 = 0 -> nb mod 8 = 0 -> F <= p -> p + 6 <= F + nb -> p <= x < p + 6 ->
in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr F, nb / 8).
Proof.
intros F nb p x HF Hnb H1 H2 Hx. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod nb 8 ltac:(lia)) as Dn.
rewrite HF, Z.add_0_r in DF. rewrite Hnb, Z.add_0_r in Dn.
assert (F / 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (x / 8 < F / 8 + nb / 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.
Lemma fnd_mac_at : forall sp0 ly S W mem md memT mdT k p (M : list byte),
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S W memT mdT k ->
afobj SEGS B ly S W mem p 6 ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
afobj SEGS B ly S W memT p 6 /\
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) memT (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))).
Proof.
intros sp0 ly S W mem md memT mdT k p M HJ HFO HM.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HJ as (HAR & _).
destruct (frame_al64 SEGS B ly S W memT mdT cid pos HAR Hfin) as (Hal64 & Hb64 & H64).
assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D. rewrite Hb64, Z.add_0_r in D. rewrite D.
replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z.mod_mul. lia. }
split.
- split; [exists cid, pos; auto|]. split; [exact Hp8|].
eapply range_addressable_agree; [|exact HRA].
intros x Hx. apply (fnd_jkept_frame sp0 ly S W mem md memT mdT k cid pos _ HJ Hfin).
right. exact (fnd_mac_zone _ _ p x Hfal Hb8 Hflo Hfhi Hx).
- intros i Hi. rewrite (fnd_jkept_frame sp0 ly S W mem md memT mdT k cid pos _ HJ Hfin); [apply HM; exact Hi |].
left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
(* The call of mac_is_zero (jal at 0x81968): the callee's contract through cl_callS. *)
Lemma fnd_mz_call : forall ly S W mem md sp0 (regsc : bvmap 5 word) memc mdc ch (p : Z) (M : list byte),
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S W memc mdc 0 ->
spZ regsc = sp0 + -80 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsc 1) -> 4096 <= bv_unsigned (getr regsc 1) ->
achain ly (aview SEGS (w_H W) mem) sp0 (s0Z regsc) ch ->
getr regsc 10 = w64 p ->
afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (@pa_sigma _ boxb_listing PI BB_mac_is_zero)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly2 S2 W2 mem2 md2 (0 + 0) /\
ajournal SEGS B MAC_IS_ZERO_STKB (sp0 + -80) [] ly S W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
aregs_preserved regsc regs2 /\
(fun ly' S' W' (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) => ly' = ly /\ S' = S /\ W' = W /\
((M = Boxreg.zero6 /\ getr regs' 10 = w64 1) \/ (M <> Boxreg.zero6 /\ getr regs' 10 = w64 0))) ly2 S2 W2 regs2 mem2 md2).
Proof.
intros ly S W mem md sp0 regsc memc mdc ch p M HJ Hsp Hgp Htp Hra Hra4 Hch H10 HFO HLM HM.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & K1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
assert (WM : MAC_IS_ZERO_STKB = 4112) by reflexivity.
destruct (fnd_mac_at sp0 ly S W mem md memc mdc 0 p M HJ HFO HM) as [HFOc HMc].
rewrite pa_sigma_mac_is_zero.
eapply (cl_callS B LAWS W regsc memc _ REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S mdc 0 MAC_IS_ZERO_STKB [] 0 (-80) (getr regsc 1) ch).
- exact HJ.
- exact Hsp.
- reflexivity.
- lia.
- rewrite WM. lia.
- rewrite WM, WS. lia.
- exact Hgp.
- exact Htp.
- reflexivity.
- exact Hra.
- exact Hra4.
- apply (achain_lower ly _ sp0); [|lia].
apply (achain_kept ly (aview SEGS (w_H W) mem) _ sp0 _ ch sp0 Hch); [lia | lia |].
intros a Ha. apply K1; [pose proof (asan_consts) as (C1 & _); lia | lia].
- intros HPREc. exact (MZ ly S W regsc memc mdc ch p M HPREc H10 HFOc HLM HMc).
- intros a Ha. exfalso. exact (inFP_nil a Ha).
Qed.
(* The post-condition from the journal at the return. *)
Lemma fnd_post : forall ly S W (regs : bvmap 5 word) mem md memF mdF (regsF : bvmap 5 word) r p bs M z,
ajournal SEGS B REAC_BOXREG_FIND_STKB (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
In (r, REG_SIZEB) (ablocks B ly S) -> afobj SEGS B ly S W mem p 6 ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
aregs_preserved regs regsF -> getr regsF 10 = w64 z -> reac_boxreg_find_c.find_result bs M z ->
tbreac_boxreg_find_post regs ly S W mem md r p bs M W (mkCfg (mkst regsF (getr regs 1) memF (seg_rom SEGS)) mdF).
Proof.
intros ly S W regs mem md memF mdF regsF r p bs M z HJ Hin HFO HBS HM HP H10 HR.
unfold tbreac_boxreg_find_post, apost_base. exists ly, S, regsF, memF, mdF.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ intros i Hi. rewrite (fnd_jkept_block (spZ regs) ly S W mem md memF mdF 0 r REG_SIZEB i HJ Hin)
by (change (req_size REG_SIZEB) with 288; unfold REG_SIZEB in Hi; lia). exact (HBS i Hi). }
split; [exact (proj2 (fnd_mac_at (spZ regs) ly S W mem md memF mdF 0 p M HJ HFO HM))|].
exists z. split; [exact H10 | exact HR].
Qed.
(* The four bytes of n = r->n: its little-endian bytes, n being 0 .. 5. *)
Lemma fnd_nth_le_bytes : forall m z k, (k < m)%nat ->
nth k (Z_to_le_bytes m z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction m as [|m IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma fnd_n_bytes : forall bs, length bs = 288%nat -> 0 <= Boxreg.bx_n bs ->
forall k, (k < 4)%nat -> nth (280 + k) bs (Z_to_bv 8 0) = Z_to_bv 8 (le_byte (Boxreg.bx_n bs) 4 k).
Proof.
intros bs HL Hn k Hk.
assert (L : length (Boxreg.bsub bs 280 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
pose proof (Boxreg.rd4_range bs 280) as Hr. change (Boxreg.rd4 bs 280) with (Boxreg.bx_n bs) in Hr.
assert (Hv : bytes_le_to_Z (Boxreg.bsub bs 280 4) = Boxreg.bx_n bs).
{ pose proof (Boxreg.le4_range _ L) as R. unfold Boxreg.bx_n, Boxreg.rd4 in *.
revert Hn R. generalize (bytes_le_to_Z (Boxreg.bsub bs 280 4)). intros v Hn R.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia. }
assert (E2 : nth (280 + k) bs (Z_to_bv 8 0) = nth k (Boxreg.bsub bs 280 4) (Z_to_bv 8 0)).
{ unfold Boxreg.bsub. rewrite nth_firstn. change (Z.to_nat 4) with 4%nat. change (Z.to_nat 280) with 280%nat.
destruct (Nat.ltb_spec k 4); [|lia]. rewrite nth_skipn. reflexivity. }
rewrite E2. rewrite <- (BoxregRd.le_bytes_roundtrip (Boxreg.bsub bs 280 4)). rewrite L, Hv.
rewrite fnd_nth_le_bytes by exact Hk.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (Boxreg.bx_n bs) (2 ^ 32)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* a0 after a call: the fifth clobbered register's atom. *)
Lemma fnd_U_a0 : forall E k (regs2 : bvmap 5 word), U (havoc E k (map (getr regs2) CLOB)) (SOff (k + 4) 0) = bv_unsigned (getr regs2 10).
Proof.
intros E k regs2. rewrite U_SOff. unfold havoc. cbn [ew].
replace (k + 4 <? k)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace (k + 4 - k)%nat with 4%nat by lia. unfold CLOB. cbn [map nth].
rewrite Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as R.
change (bv_modulus 64) with (2 ^ 64) in R. unfold M64. lia.
Qed.
(* The word n = r->n in the current memory. *)
Lemma fnd_n_val : forall sp0 ly S W mem md memT mdT k r bs,
ajournal SEGS B REAC_BOXREG_FIND_STKB sp0 [] ly S W mem md [] ly S W memT mdT k ->
In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
0 <= Boxreg.bx_n bs ->
val_mem SEGS (mrestrict (w_H W) memT) (r + 280) 4 (Boxreg.bx_n bs).
Proof.
intros sp0 ly S W mem md memT mdT k r bs HJ Hin HL HBS Hn kk Hkk.
assert (HA : aview SEGS (w_H W) memT (r + (280 + Z.of_nat kk)) = Some (bv_unsigned (nth (280 + kk) bs (Z_to_bv 8 0)))).
{ rewrite (fnd_jkept_block sp0 ly S W mem md memT mdT k r REG_SIZEB (280 + Z.of_nat kk) HJ Hin)
by (change (req_size REG_SIZEB) with 288; lia).
rewrite (HBS (280 + Z.of_nat kk)) by (unfold REG_SIZEB; lia).
replace (Z.to_nat (280 + Z.of_nat kk)) with (280 + kk)%nat by lia. reflexivity. }
destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
replace (r + 280 + Z.of_nat kk) with (r + (280 + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
replace b with (nth (280 + kk) bs (Z_to_bv 8 0)) by (apply bv_eq; lia). exact (fnd_n_bytes bs HL Hn kk Hkk).
Qed.
Definition RN (nz : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SLit nz))].
Definition FSH : list shent := [mkSHE 10 0 288].
(* ~r, the UBSan pointer-overflow bound of the scan loop (s5 = not s2 at 0x819d4). *)
Lemma fnd_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = Z.ones 64 - x.
Proof.
intros x Hx.
assert (L : Z.ldiff x (Z.ones 64) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 64).
- rewrite Z.ones_spec_low by lia. apply andb_false_r.
- rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x L).
apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.lt_ge_cases n 64).
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma fnd_U_not : forall E r, ew E 10 = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) = 2 ^ 64 - 1 - r.
Proof.
intros E r H Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 r H Hr), U_SLit.
replace (zcanon (-1)) with (Z.ones 64) by reflexivity. rewrite fnd_lxor_ones by exact Hr.
replace (Z.ones 64) with (2 ^ 64 - 1) by reflexivity. apply zcanon_id. unfold M64. lia.
Qed.
(* box i's MAC against the six bytes, byte by byte. *)
Lemma fnd_mac_eq : forall bs M i, length bs = 288%nat -> length M = 6%nat -> 0 <= i < 5 ->
(Boxreg.bx_mac bs i = M <->
forall j, 0 <= j < 6 -> nth (Z.to_nat (56 * i + j)) bs (Z_to_bv 8 0) = nth (Z.to_nat j) M (Z_to_bv 8 0)).
Proof.
intros bs M i HL HLM Hi.
assert (Lm : length (Boxreg.bx_mac bs i) = 6%nat) by (unfold Boxreg.bx_mac; apply Boxreg.bsub_length; lia).
assert (Hn : forall j, 0 <= j < 6 -> nth (Z.to_nat j) (Boxreg.bx_mac bs i) (Z_to_bv 8 0) = nth (Z.to_nat (56 * i + j)) bs (Z_to_bv 8 0)).
{ intros j Hj. unfold Boxreg.bx_mac, Boxreg.bsub. rewrite nth_firstn.
destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat 6)); [|lia]. rewrite nth_skipn. f_equal. lia. }
split.
- intros <- j Hj. symmetry. exact (Hn j Hj).
- intros H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite Lm, HLM; reflexivity|].
intros k Hk. rewrite Lm in Hk. rewrite <- (Nat2Z.id k). rewrite (Hn (Z.of_nat k)) by lia. apply H. lia.
Qed.
Lemma fnd_inv_step : forall bs M (e : Z), (forall j, 0 <= j < e -> Boxreg.bx_mac bs j <> M) ->
Boxreg.bx_mac bs e <> M -> forall j, 0 <= j < e + 1 -> Boxreg.bx_mac bs j <> M.
Proof. intros bs M e H Ne j Hj. destruct (Z.eq_dec j e) as [->|Hne]; [exact Ne | apply H; lia]. Qed.
(* The call of the bcmp wrapper (jal at 0x819fc) on box i's MAC and the six bytes at p. *)
Lemma fnd_bcmp_call : forall ly S W (regs : bvmap 5 word) mem md k r p bs M (regsT : bvmap 5 word) memT mdT i,
ajournal SEGS B REAC_BOXREG_FIND_STKB (spZ regs) [] ly S W mem md [] ly S W memT mdT k ->
In (r, REG_SIZEB) (ablocks B ly S) -> afobj SEGS B ly S W mem p 6 -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
length M = 6%nat ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
0 <= i < 5 ->
getr regsT 10 = w64 (r + 56 * i) -> getr regsT 11 = w64 p -> getr regsT 12 = w64 6 ->
spZ regsT = spZ regs + -80 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsT 1) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (@pa_sigma _ boxb_listing PI BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B REAC_BOXREG_FIND_STKB (spZ regs) [] ly S W mem md [] ly S W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(bv_unsigned (getr regs2 10) = 0 <-> Boxreg.bx_mac bs i = M) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -80 - 2 * ESTACK <= a < spZ regs + -80) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros ly S W regs mem md k r p bs M regsT memT mdT i HJ Hin HFO HL HBS HLM HM Hi H10 H11 H12 Hsp Hgp Htp Hra.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZEB) with 288 in *.
destruct (fnd_mac_at (spZ regs) ly S W mem md memT mdT k p M HJ HFO HM) as [HFOc HMc].
pose proof HFOc as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRAc).
destruct (frames_bounds SEGS B LAWS ly S W memT mdT cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
assert (HX : forall j, 0 <= j < 6 -> aview SEGS (w_H W) memT (r + 56 * i + j) = Some (bv_unsigned (nth (Z.to_nat (56 * i + j)) bs (Z_to_bv 8 0)))).
{ intros j Hj. replace (r + 56 * i + j) with (r + (56 * i + j)) by lia.
rewrite (fnd_jkept_block (spZ regs) ly S W mem md memT mdT k r REG_SIZEB (56 * i + j) HJ Hin) by (change (req_size REG_SIZEB) with 288; lia).
apply HBS. unfold REG_SIZEB. lia. }
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs _ ABCMP W regsT memT REAC_BOXREG_FIND_STKB (spZ regs) [] ly S W mem md [] ly S mdT k
(r + 56 * i) p 6 (-80) (getr regsT 1) HJ).
- exact H10.
- exact H11.
- exact H12.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Hsp.
- reflexivity.
- lia.
- rewrite WS, Hes. lia.
- exact Hgp.
- exact Htp.
- reflexivity.
- exact Hra.
- intros a Ha. split; [replace a with (r + 56 * i + (a - (r + 56 * i))) by lia; rewrite HX by lia; discriminate|].
rewrite Hsp, Hes. lia.
- intros a Ha. split; [replace a with (p + (a - p)) by lia; rewrite HMc by lia; discriminate|].
rewrite Hsp, Hes. lia.
- intros a Ha. rewrite Hes. lia.
- intros a Ha. rewrite Hes. lia.
- eapply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZEB); [exact HAR | exact Hin | lia | change (req_size REG_SIZEB) with 288; lia].
- exact (amem_range_sub_app _ _ p 6 Happ Hfceil Hflo Hfhi ltac:(lia)).
- eapply (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZEB); [exact HAR | exact Hin | lia | change (req_size REG_SIZEB) with 288; lia].
- intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT r REG_SIZEB); [exact HAR | exact Hin | lia | change (req_size REG_SIZEB) with 288; lia | lia].
- exact HRAc.
- intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S W memT mdT cid pos p 6 HAR Hfin Hflo Hfhi ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [|exact Hfr].
rewrite Hv. rewrite (fnd_mac_eq bs M i HL HLM Hi). split.
- intros H0 j Hj. assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
pose proof (proj1 Hcmp Hv0 j Hj) as Q. rewrite HX, HMc in Q by lia. injection Q as Q. apply bv_eq. exact Q.
- intros Q. assert (Hv0 : v = w64 0).
{ apply Hcmp. intros j Hj. rewrite HX, HMc by lia. rewrite (Q j Hj). reflexivity. }
rewrite Hv0. reflexivity.
Qed.
(* The index of the frame region (base atom 2) in a symbolic memory. *)
Fixpoint fnd_sidx (rs : smem) (i : nat) : list nat :=
match rs with
| [] => []
| r0 :: t => match YP09.r_base r0 with Some 2%nat => [i] | _ => fnd_sidx t (S i) end
end.
Theorem pbb_reac_boxreg_find : tbreac_boxreg_find_spec.
Proof.
unfold tbreac_boxreg_find_spec.
intros ly S W regs mem md ch r p bs M HPRE H10 H11 Hin HL HBS HB1 HFO HLM HM.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (fnd_entry ly S W regs mem md ch r p HPRE H10 H11 Hin HFO) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_FIND_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
remember (EF regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EF; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs fnd_extra) n)
by (intros n Hn; subst E; unfold EF; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 FSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZEB) with 288 in *.
assert (HnB : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs fnd_extra) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 AB_reac_boxreg_findP) with (Z_to_bv 64 AB_reac_boxreg_findP).
(* entry -> the call of mac_is_zero *)
paj_run_tok RUN HS HJ SHOK FBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
clear HF HFr HG.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
assert (HspT : spZ rT = spZ regs + -80)
by (unfold spZ at 1; rewrite Rsp, Usp; rewrite unsigned_lit_small by lia; lia) end.
eapply SRr_bind.
{ eapply (fnd_mz_call ly S W mem md (spZ regs) _ _ _ ch p M HJ HspT).
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite Rra. rewrite unsigned_lit_small by lia. lia.
- unfold s0Z. rewrite Rs0, E8. exact Hch.
- rewrite Ra0, E11. reflexivity.
- exact HFO.
- exact HLM.
- exact HM. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJi & HP2 & (-> & -> & -> & HMZ)).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & Ki1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
lazymatch type of HS2 with ?T -> _ => assert (HRK : T) end.
{ constructor; [|apply Forall_nil]. split.
- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply Ki1; [lia|]. change MAC_IS_ZERO_STKB with 4112. lia.
- intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
rewrite Usp in Ha. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear HJ HJi Ki1 Hpres2.
assert (HEI2 : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB))) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (SHOK2 : sh_ok SEGS FBx [] (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
clear SHOK. rewrite Rra.
paj_run_tok RUN HS HJ2 SHOK2 FBspan;
[awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Usp |].
clear HF HFr HG.
pose proof (fnd_U_a0 E 33 regs2) as UA. cbn [Nat.add] in UA.
psrr_branch_tok RUN BR HS SHOK2 FBspan.
- (* a0 = 0: the MAC is not zero *)
rewrite branch_eq_U, UA, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
assert (HMN : M <> Boxreg.zero6).
{ destruct HMZ as [[_ Ha1] | [HMn _]]; [|exact HMn]. rewrite Ha1 in Hc. vm_compute in Hc. discriminate. }
clear HMZ UA Hc.
assert (HN : Boxreg.bx_n bs = 0 \/ Boxreg.bx_n bs = 1 \/ Boxreg.bx_n bs = 2 \/ Boxreg.bx_n bs = 3 \/
Boxreg.bx_n bs = 4 \/ Boxreg.bx_n bs = 5) by lia.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
assert (HVN : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (r + 280) 4 (Boxreg.bx_n bs))
by (exact (fnd_n_val (spZ regs) ly S W mem md _ _ _ r bs HJ2 Hin HL HBS ltac:(lia)));
assert (SHOK3 : sh_ok SEGS FBx FSH Ex (mrestrict (w_H W) (ms_mem msx)))
end.
{ unfold sh_ok, FSH. constructor; [|constructor].
eapply (shent_ok_of_range SEGS (w_H W) _ _ FBx 10 r 288 r 0 288).
- eapply (range_addressable_of_block SEGS B LAWS ly S W _ _ r REG_SIZEB r 288 (proj1 HJ2) Hin); change (req_size REG_SIZEB) with 288; lia.
- unfold FBx. rewrite U_SOff, ew_havoc_old, E32 by lia. rewrite unsigned_lit_small by (unfold FSB; lia). reflexivity.
- rewrite U_SOff, ew_havoc_old, E10 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
- lia.
- intros x Hx. revert Hria Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
clear SHOK2.
destruct HN as [HN|[HN|[HN|[HN|[HN|HN]]]]]; rewrite HN in HVN.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
lazymatch type of HVN with val_mem _ _ _ _ ?nz =>
assert (HR : region_ok SEGS Ex (ms_mem (restrict Hh msx)) (RN nz));
[ cbn [restrict ms_mem]; unfold RN, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite ew_havoc_old, E10 by lia; rewrite unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
constructor; [|constructor];
apply (chunk_ok_val SEGS Ex _ r 280 4 (SLit nz) nz); [reflexivity | zside | zside | exact HVN]
| pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) (RN nz) HS ltac:(vm_compute; reflexivity) HR
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, RN;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite !ew_havoc_old by lia; rewrite E10, E2; rewrite !unsigned_lit_small by lia;
change (bv_unsigned (getr regs 2)) with (spZ regs);
revert Hslo Hceil Hrceil Hr4096 C1 C3 WS; clear; intros;
repeat match goal with |- _ /\ _ => split end; first [exact I | lia])) as HS3;
clear HS HR; rename HS3 into HS ] end end.
all: assert (INV : forall j, 0 <= j < 0 -> Boxreg.bx_mac bs j <> M) by (intros j Hj; lia).
all: let fnd_awr := idtac; awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); exact Usp in
let leaf := idtac;
lazymatch goal with HS' : st_ok_pi _ _ _ ?ss _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let v := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
let z := lazymatch v with SLit 18446744073709551615 => constr:(-1) | SLit ?z0 => z0 end in
let R10 := fresh "R10" in let R1 := fresh "R1" in let mat := fresh "mat" in
prreg HS' (10%bv : bv 5) R10; prreg HS' (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity));
intros mat; cbn [ms_regs ms_mem]; rewrite R1, E1, Hra;
eapply (fnd_post ly S W regs mem md _ _ _ r p bs M z);
[ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx
| exact Hin | exact HFO | exact HBS | exact HM
| eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs fnd_extra HS'); [| vm_compute; reflexivity];
split; [intros n Hn; rewrite ?ew_havoc_old by lia; exact (proj1 HAE n Hn) | cbn [havoc ed]; exact (proj2 HAE)]
| rewrite R10; apply bv_eq; vm_compute; reflexivity
| unfold reac_boxreg_find_c.find_result, reac_boxreg_find_c.first_mac;
lazymatch goal with INV : forall j, 0 <= j < _ -> Boxreg.bx_mac _ j <> _ |- _ =>
first
[ right; right; split; [exact HMN|]; split; [reflexivity|]; intros j Hj; apply INV; lia
| right; left; split; [exact HMN|]; split; [lia|];
split; [assumption|];
intros j Hj; apply INV; lia ] end ]
end in
let bcmp_step := idtac;
lazymatch goal with HSc : st_ok _ ?Ex ?ssc (restrict _ ?msc), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
SHx : sh_ok _ _ _ _ _ |- _ =>
let iv := eval vm_compute in (sr_get (ss_regs ssc) (19%bv : bv 5)) in
let i := lazymatch iv with SLit ?z0 => z0 end in
let k := eval vm_compute in (Nat.max 33 (ss_atom_bound_lo A_TEXT ssc)) in
let idxs := eval vm_compute in (fnd_sidx (ss_mem ssc) 0) in
let Ra0 := fresh "Ra" in let Ra1 := fresh "Ra" in let Ra2 := fresh "Ra" in let Rra := fresh "Rra" in
let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
pmkst HSc;
prreg HSc (10%bv : bv 5) Ra0; prreg HSc (11%bv : bv 5) Ra1; prreg HSc (12%bv : bv 5) Ra2;
prreg HSc (1%bv : bv 5) Rra; prreg HSc (2%bv : bv 5) Rsp; prreg HSc (3%bv : bv 5) Rgp; prreg HSc (4%bv : bv 5) Rtp;
eapply SRr_bind;
[ eapply (fnd_bcmp_call ly S W regs mem md _ r p bs M _ _ _ i HJx Hin HFO HL HBS HLM HM);
[ lia
| rewrite Ra0; rewrite ?E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia
| rewrite Ra1, E11; reflexivity
| rewrite Ra2; reflexivity
| unfold spZ at 1; rewrite Rsp, Usp; rewrite unsigned_lit_small by lia; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity] ]
| ];
cbv beta;
let W2 := fresh "W" in let c2 := fresh "c" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ3 := fresh "HJ" in let HP3 := fresh "HP" in let HCMP := fresh "HCMP" in
let Hfr3 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP3 & HCMP & Hfr3);
let Hpres3 := fresh "Hpres" in
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _);
let HS2 := fresh "HS" in
jafter_call_keep_pi HSc k regs2 (mrestrict (w_H W) mem2) HP3 idxs HS2;
let T := lazymatch type of HS2 with ?T -> _ => T end in
let HRK := fresh "HRK" in
assert (HRK : T);
[ constructor; [|apply Forall_nil]; split;
[ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?ew_havoc_old in Ha by lia;
rewrite Usp in Ha; apply (mbyte_of_aview SEGS); apply Hfr3; [lia|]; change ESTACK with 4096; lia
| intros a Ha _; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_havoc_old in Ha by lia;
rewrite Usp in Ha; apply (apresent_writable SEGS); apply Hpres3; rewrite WS; lia ]
| ];
specialize (HS2 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS2; clear HSc Hpres3 Hfr3;
let HEIn := fresh "HEI" in
assert (HEIn : img_env VAL A_LIM (havoc Ex k (map (getr regs2) CLOB))) by (apply img_env_havoc; [assumption | cbv; lia]);
let SHn := fresh "SHOK" in
assert (SHn : sh_ok SEGS FBx [] (havoc Ex k (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil);
clear SHx HJx;
let UA := fresh "UA" in pose proof (fnd_U_a0 Ex k regs2) as UA; cbn [Nat.add] in UA;
rewrite Rra; clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp
end in
let rec go := idtac;
lazymatch goal with HS' : st_ok_pi _ _ _ _ _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SH' : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS' HJx SH' FBspan; [fnd_awr |];
clear HF HFr HG;
lazymatch goal with
| HSc : st_ok _ _ _ _ |- _ => bcmp_step; go
| HS2 : st_ok_pi _ _ ?Ex2 ?ss _, SH2 : sh_ok _ _ ?SHl _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM FBx SHl ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K FBx FBspan SHl (start K FBx FBspan SHl ss) end in
lazymatch why with
| SR_jalr _ => leaf
| SR_branch BC_LTU _ _ =>
psrr_branch_tok RUN BR HS2 SH2 FBspan;
[ exfalso; lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite branch_ltu_U, U_lit in Hc by lia;
rewrite (fnd_U_not Ex2 r ltac:(rewrite ?ew_havoc_old by lia; exact E10) ltac:(lia)) in Hc;
apply Z.ltb_lt in Hc; lia end
| lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end; go ]
| SR_branch BC_EQ (SOff ?a 0) (SLit 0) =>
psrr_branch_tok RUN BR HS2 SH2 FBspan;
[ lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ (SOff a 0) = _,
HCMP : bv_unsigned _ = 0 <-> Boxreg.bx_mac _ ?i = _ |- _ =>
rewrite branch_eq_U, UA, U_lit in Hc by lia; apply Z.eqb_eq in Hc;
let MT := fresh "MT" in pose proof (proj1 HCMP Hc) as MT; clear Hc UA HCMP; go end
| lazymatch goal with Hc : branch_taken _ _ _ = false, UA : U _ (SOff a 0) = _,
HCMP : bv_unsigned _ = 0 <-> Boxreg.bx_mac _ ?i = _ |- _ =>
rewrite branch_eq_U, UA, U_lit in Hc by lia; apply Z.eqb_neq in Hc;
let NV := fresh "NV" in assert (NV : Boxreg.bx_mac bs i <> M) by (intros X; apply Hc; exact (proj2 HCMP X));
lazymatch goal with INV : forall j, 0 <= j < _ -> Boxreg.bx_mac _ j <> _ |- _ =>
let INV2 := fresh "INV" in
assert (INV2 : forall j, 0 <= j < i + 1 -> Boxreg.bx_mac bs j <> M)
by (apply fnd_inv_step; [intros j Hj; apply INV; lia | exact NV]);
clear INV NV Hc UA HCMP end; go end ]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end
end in
go.
- (* a0 <> 0: the MAC is zero, return -1 *)
rewrite branch_eq_U, UA, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
assert (HMZ0 : M = Boxreg.zero6).
{ destruct HMZ as [[HMz _] | [_ Ha0]]; [exact HMz|]. rewrite Ha0 in Hc. vm_compute in Hc. exfalso. exact (Hc eq_refl). }
clear HMZ UA Hc.
paj_run_tok RUN HS HJ2 SHOK2 FBspan;
[awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Usp |].
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem]. rewrite R1, E1, Hra.
eapply (fnd_post ly S W regs mem md _ _ _ r p bs M (-1)).
+ apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2.
+ exact Hin.
+ exact HFO.
+ exact HBS.
+ exact HM.
+ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs fnd_extra HS); [| vm_compute; reflexivity].
split; [intros n Hn; rewrite ?ew_havoc_old by lia; exact (proj1 HAE n Hn) | cbn [havoc ed]; exact (proj2 HAE)].
+ rewrite R10. apply bv_eq. vm_compute. reflexivity.
+ left. split; [exact HMZ0 | reflexivity].
Qed.
End h.
End f.
End d.
