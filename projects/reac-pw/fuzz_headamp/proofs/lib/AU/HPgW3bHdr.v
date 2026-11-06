(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 589 of its 629 lines of code are new or changed and 250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3b.v at c7151e1be458, ported to
   reac-pw/fuzz_rate image A: module paths and prefixes (RPg* -> RtPg*, rm_ -> rtm_, rl_ -> rt_, e_ -> q_) changed;
   rate's pcs, its shadow base s2 (x18), &pp->len in s7 (x23) and the shadow address of &pp->len in s6 (x22, pinned
   to its expression, as the code loads the shadow byte of pp->len through s6 and not through a cell); the Object
   header reads the shape and -0x3ffd from R+0xd8 and R+0x130; the start fact list has rate's five conjuncts; the
   image facts come from lib/A/RtPgSteps.v; the frame's shadow has 56 bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v, with its module paths, module names, addresses and numbers changed; 234 of its 375 lines of code are new or changed and 488 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3b.v at c7151e1be45 (its BO piece,
   image A of fuzz_role) for reac-pw/fuzz_headamp's image B: B's own code walked again (its second header word
   out of line at 0x82d14, s9 = pp, s11 = K, a3 = the shape, the UBSan tests, &pp->len and its shadow address read
   from R+0x138 / R+0x150, R+0xf8 written), the statement lib/AU/HPgSeg.v's; the helper lemmas reg_kept, chunk1,
   img_ph, len_hdr and ph_img taken with rm_ renamed to hm_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the Object header piece
   of the build (M01) of LLVMFuzzerTestOneInput 0x80c40, BO 0x81200 -> PH 0x8137c (pod.h:392-395, shape <> 7), the
   piece statement lib/AU/HPgSeg.v hsu_piece_W3b_hdr_stmt at image B's record headamp_himg_B and builder pcs
   headamp_bld_B. Proves no function (kind: segment lemma).

   THE CODE (0x81200 .. 0x81378, 95 words, and 0x82d14 .. 0x82d9c, 35 words). Three pod_put32 at pp + 4, pp + 8,
   pp + 12, each with its capacity test (`bltu len - 0x3ffd, -0x4001`: 0x81208, 0x8129c, 0x812cc), its two UBSan
   tests (len < 0x4001: 0x81214, 0x82d1c, 0x812d8; ~pp >= len from R+0xf0: 0x81220, 0x82d24, 0x812e4), the two
   shadow checks of its first and last byte (base s11) and the shadow check of &pp->len through R+0x150; then
   POD_OBJECT = 15 at pp + 4 (0x81258 ..), the second word 0x40002 - (shape == 6) out of line at 0x82d50 ..
   (POD_OBJECT_PROPINFO 0x40001 when the shape is 6, else POD_OBJECT_PROPS 0x40002; entered by `j` 0x812a0, back by
   `j` 0x82d9c to 0x812bc), POD_PARAM_PROPS = 2 at pp + 12 (0x8131c ..), len += 4 each time through R+0x138;
   R+0xf8 := 0 (0x8136c) and is_props := (shape <> 6) at pp + 0x4008 with its shadow check (0x81350 .. 0x81378).
   len is 4 at BO, so every capacity test and every UBSan test is decided on literals and the cut's ranges: no
   UBSan trap (`j 0x83a14`) is reached.

   REGISTERS AND R-CELLS this file reads (the role port renames these): s1 = R (x9), s9 = pp (x25), s11 = K
   (x27), a0 = 4 (x10), a2 = 4 - 0x3ffd (x12), a3 = the shape (x13); R+0xf0 = ~pp, R+0x108 = -0x3ffd, R+0x138 =
   pp + 0x4000, R+0x150 = the shadow address of pp + 0x4000; it writes a0, a2 .. a5 (x10, x12 .. x15), R+0xf8,
   pp + 4 .. pp + 16 and pp + 0x4000 .. pp + 0x400c.

   HOW. As HPgW3bB7.v: the symbolic state is rebuilt from BO's cut over the token engine, ~pp the extra atom 32
   with its range, the R-relative cells one region of base s1 with R+0xf8's write window, pp's two written ranges
   two regions of base s9, the shadow base s11 with one shadow entry (pp on s9). The values the header writes
   depend on the shape; the run leaves them as expressions in a3's atom, and the end splits the shape into its
   seven values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the engine's context ===================================== *)
Definition HWO_BO : Z := 0x81200.
Definition HWO_PH : Z := 0x8137c.
(* the 95 instruction words 0x81200 .. 0x81378 and the 35 words 0x82d14 .. 0x82d9c (the second header word) *)
Definition hwo_tbl : ctable := build_table rsegs 0x82d14 35 (build_table rsegs 0x81200 95 TEmpty).
Lemma hwo_tbl_ok : table_ok rsegs hwo_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok0; lia]. Qed.
(* the shadow base is s11 (x27) *)
Definition hwo_Bx : sv := SOff 27 0.
Definition hwo_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of &pp->len as the code keeps it in R+0x150 (0x81088 .. 0x81090) *)
Definition hwo_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0x4000) (SLit 3)) (SOff 27 0).
(* pp on s9 (19744 bytes) *)
Definition hwo_SH : list shent := [mkSHE 25 0 19744].
Definition HWO_PPHI : Z := 0x7fffff800000 - 19744.
(* R on the stack, pp in the heap, K, and ~pp (the extra atom 32) *)
Definition hwo_atoms : list (nat * afact) :=
[(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (25%nat, mkAF 4096 HWO_PPHI 0);
 (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF (2 ^ 64 - HWO_PPHI - 1) (2 ^ 64 - 4097) 0)].
Definition HWO_A2 : Z := 0xffffffffffffc007.    (* 4 - 0x3ffd mod 2^64 *)
Definition HWO_M3FFD : Z := 0xffffffffffffc003.  (* -0x3ffd mod 2^64 *)
Definition hwo_regs : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit 4)) (Z_to_bv 5 12) (SLit HWO_A2).
Definition hwo_slot : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xf0 0x158 0xf8 0x100
[YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x108 (CVal 8 (SLit HWO_M3FFD));
 YP09.mkChunk 0x138 (CVal 8 (SOff 25 0x4000)); YP09.mkChunk 0x150 (CVal 8 hwo_shx)].
Definition hwo_hdr_r : YP09.region := YP09.mkRegion (Some 25%nat) 4 16 4 16 [].
Definition hwo_len_r : YP09.region :=
YP09.mkRegion (Some 25%nat) 0x4000 0x400c 0x4000 0x400c [YP09.mkChunk 0x4000 (CVal 8 (SLit 4))].
Definition hwo_ss : sstate :=
mkSS HWO_BO hwo_regs [hwo_slot; hwo_hdr_r; hwo_len_r] None (mkFacts hwo_atoms [] []).

(* every hypothesis H : A /\ B /\ .. split into one hypothesis per conjunct *)
Ltac hwo_split H :=
  repeat lazymatch type of H with _ /\ _ => let c := fresh "Cn" in destruct H as [c H] end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma hwo_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

(* one byte a run stored, as the walk reads it back: a CVal 1 chunk of a final region at base + off *)
Lemma hwo_chunk1 : forall E (H : word -> bool) ms base off e (b : byte),
YP09.chunk_ok rsegs E (ms_mem (restrict H ms)) base (YP09.mkChunk off (CVal 1 e)) ->
byte_of_word (sv_denot E e) 0 = b -> forall a, a = base + off -> aview rsegs H (ms_mem ms) a = Some (bv_unsigned b).
Proof.
intros E H ms base off e b C Hb a ->. destruct (C 0 ltac:(cbn; lia)) as (b' & H1 & H2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1, H2. injection H1 as <-. rewrite Z.add_0_r in H2.
unfold aview. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite H2, Hb. reflexivity.
Qed.

(* the registers the run leaves alone: all but a0 and a2 .. a5 *)
Definition HWO_KEPT : list Z :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Ltac hwo_kept_regs HS HAE E ms regs extra W :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [HWO_KEPT] in Hr;
repeat (destruct Hr as [<-|Hr];
  [eapply (hwo_reg_kept E _ ms regs extra (w_H W)); [exact HS | exact HAE | vm_compute; reflexivity] |]);
destruct Hr.

(* ===================================== BO -> PH =====================================
   Entry facts: s1 = R, a0 = len = 4, a2 = len - 0x3ffd, a3 = sh, s9 = pp, s11 = K; the cells R+0xf0 (~pp),
   R+0x108 (-0x3ffd), R+0x138 (&pp->len) and R+0x150 (its shadow address); len = 4 in pp. At 0x8137c: a0 and
   a2 .. a5 changed, the twelve header bytes at pp + 4, len = 16, is_props = (sh <> 6), R+0xf8 = 0, every other
   byte as before. *)
Lemma hwo_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k
(regs : bvmap 5 word) (R pp sh : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
sp0 - STK <= R -> R + 0x158 <= sp0 -> 0 <= sh <= 6 ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 4 ->
getr regs (Z_to_bv 5 12) = w64 (4 - 0x3ffd) -> getr regs (Z_to_bv 5 13) = w64 sh ->
getr regs (Z_to_bv 5 25) = w64 pp -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (-0x3ffd mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 ((pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 4 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
 same_io mdc md2 ->
 (forall r, In r HWO_KEPT -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 4 <= a < pp + 16) -> ~ (pp + 0x4000 <= a < pp + 0x400c) ->
  ~ (R + 0xf8 <= a < R + 0x100) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 hm_bytes rsegs (w_H W) mem2 (pp + 4) (hdr_bytes sh) ->
 hm_bytes rsegs (w_H W) mem2 (pp + 0x4000) (le64 16) ->
 val_mem rsegs (mrestrict (w_H W) mem2) (pp + 0x4008) 4 (Z.b2z (negb (sh =? 6))) ->
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 0 ->
 SRr rsegs W (cfg_at rsegs HWO_PH regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs HWO_BO regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp sh Q HJ Hin Hout HR0 HR1 Hsh
  R9 R10 R12 R13 R25 R27 Vf0 V108 V138 V150 Vlen KONT.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
assert (Hnp : ((- pp - 1) mod 2 ^ 64) = 2 ^ 64 - pp - 1).
{ rewrite <- (Z.mod_add (- pp - 1) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
remember (Ereg regs [Z_to_bv 64 (- pp - 1)]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 (- pp - 1)]) n)
  by (intros; subst E; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 (- pp - 1)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = 2 ^ 64 - pp - 1) by (rewrite E32, Z_to_bv_unsigned; exact Hnp).
assert (E13 : ew E 13 = Z_to_bv 64 sh) by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl), R13; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = R)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pp)
  by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), R25; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E25 : ew E 25 = Z_to_bv 64 pp) by (rewrite <- U25; symmetry; apply Z_to_bv_bv_unsigned).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- U27; symmetry; apply Z_to_bv_bv_unsigned).
(* the symbolic state at BO *)
assert (HS : st_ok rsegs E hwo_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 HWO_BO) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold hwo_ss. apply (entry_st_ok_full rsegs).
  - unfold hwo_regs. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite R10. reflexivity.
    + rewrite R12. unfold w64. cbn [sv_denot]. apply Z_to_bv64_eq_mod. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, hwo_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hstkp; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 32 0) ((- pp - 1) mod 2 ^ 64)); [| | cbn; lia | exact Vf0].
        -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_bv64_mod.
        -- rewrite Hnp. cbn. lia.
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SLit HWO_M3FFD) (-0x3ffd mod 2 ^ 64));
          [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact V108].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 25 0x4000) ((pp + 0x4000) mod 2 ^ 64)); [| | cbn; lia | exact V138].
        -- cbn [sv_denot]. rewrite U25. symmetry. apply Z_to_bv64_mod.
        -- pose proof (Z.mod_pos_bound (pp + 0x4000) (2 ^ 64) ltac:(lia)). cbn. lia.
      * apply (chunk_ok_val rsegs E _ R 0x150 8 hwo_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64)); [| | cbn; lia | exact V150].
        -- unfold hwo_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
           rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, !U_SOff, U25, U27, !Z.add_0_r.
           change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
           rewrite (Z.mod_small (pp + 0x4000)) by lia. rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
           rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
           rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
           rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
           unfold shadow_addr. rewrite Z.mod_mod by lia. f_equal. lia.
        -- pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)). cbn. lia.
    + unfold region_ok, hwo_hdr_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (Hppr (pp + o) ltac:(lia))).
    + unfold region_ok, hwo_len_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SLit 4) 4);
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact Vlen].
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hwo_slot hwo_hdr_r hwo_len_r]. rewrite U9, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms hwo_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U25, U27, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HWO_PPHI, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs hwo_Bx hwo_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, hwo_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart, hwo_Bx; cbn [she_m she_lo she_hi];
  rewrite ?(U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 25 pp E25) by lia.
  split.
  - change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
    apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear HE.
unfold cfg_at. change (w64 HWO_BO) with (Z_to_bv 64 HWO_BO).
aj_run_to_tok hwo_tbl_ok HS HJ SHOK hwo_Bspan HWO_PH.
{ (* the run writes R+0xf8 (the segment's stack window), pp's three header words, &pp->len and is_props (pp is a
     block made since the journal's start) *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
    apply (hd_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (hd_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
(* ---- the state at 0x8137c ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv HOK) as (_ & _ & _ & Cs).
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Ch).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOK))) as (_ & _ & _ & Cl).
cbn [YP09.r_base YP09.r_chunks base_val] in Cs, Ch, Cl. rewrite U9 in Cs. rewrite U25 in Ch, Cl. clear HOK.
repeat rewrite Forall_cons_iff in Cs. repeat rewrite Forall_cons_iff in Ch. repeat rewrite Forall_cons_iff in Cl.
hwo_split Cs. hwo_split Ch. hwo_split Cl.
assert (Hs7 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply (KONT (ms_regs ms) (ms_mem ms)).
- exact HJ.
- apply same_io_wvb.
- hwo_kept_regs HS HAE E ms regs [Z_to_bv 64 (- pp - 1)] W.
- intros a Ha Ha1 Ha2 Ha3. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U25 in Hb; lia | ]).
  destruct Hr.
- (* the twelve header bytes, one CVal 1 chunk each, at each of the seven shapes *)
  apply (proj2 (hm_bytes_aview rsegs (w_H W) (ms_mem ms) (pp + 4) (hdr_bytes sh))). intros i Hi.
  destruct Hs7 as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn in Hi;
  (do 12 (destruct i as [|i];
    [ match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 _)) |- _ =>
        eapply (hwo_chunk1 E (w_H W) ms pp o _ _ C);
        [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia];
        cbn [sv_denot]; rewrite ?E13; vm_compute; reflexivity end | ])); lia.
- (* len = 16 *)
  apply hm_bytes_of_val.
  match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 16384 (CVal 8 (SLit 16))) |- _ =>
    exact (val_of_chunk_ok rsegs E _ pp 16384 8 (SLit 16) 16 C eq_refl
      ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)) end.
- (* is_props = (sh <> 6) *)
  match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 16392 (CVal 4 ?e)) |- _ =>
    apply (val_of_chunk_ok rsegs E _ pp 16392 4 e _ C) end.
  + destruct Hs7 as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [sv_denot]; rewrite E13; vm_compute; reflexivity.
  + destruct (negb (sh =? 6)); cbn; lia.
  + cbn; lia.
- (* R+0xf8 = 0 *)
  match goal with C : YP09.chunk_ok _ _ _ R (YP09.mkChunk 248 (CVal 8 (SLit 0))) |- _ =>
    exact (val_of_chunk_ok rsegs E _ R 248 8 (SLit 0) 0 C eq_refl
      ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)) end.
Qed.
End d.

(* ===================================== the block's bytes at PH =====================================
   pc_image of the empty record of shape sh (sh <> 7): the start image (the top size word only) with the twelve
   header bytes at 4, len = 16 at 0x4000 and is_props at 0x4008. *)
Lemma hwo_img_ph : forall sh, 0 <= sh <= 6 ->
pc_image (PbCut sh [] None) =
overwrite (hm_slice hsu_img_hdr 0 16384) 4 (hdr_bytes sh) ++ le64 16 ++ le32 (Z.b2z (negb (sh =? 6))) ++
hm_slice hsu_img_hdr 16396 3348.
Proof.
intros sh Hsh. assert (H : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
Qed.
Lemma hwo_len_hdr : forall sh, sh <> 7 -> length (hdr_bytes sh) = 12%nat.
Proof. intros sh Hsh. unfold hdr_bytes. rewrite (proj2 (Z.eqb_neq sh 7) Hsh). reflexivity. Qed.
Lemma hwo_ph_img : forall H mem H' mem' pp sh, 0 <= sh <= 6 ->
hm_bytes rsegs H mem pp hsu_img_hdr ->
hm_bytes rsegs H' mem' (pp + 4) (hdr_bytes sh) ->
hm_bytes rsegs H' mem' (pp + 16384) (le64 16) ->
hm_bytes rsegs H' mem' (pp + 16392) (le32 (Z.b2z (negb (sh =? 6)))) ->
(forall y, pp <= y < pp + 19744 -> ~ (pp + 4 <= y < pp + 16) -> ~ (pp + 16384 <= y < pp + 16396) ->
 aview rsegs H' mem' y = aview rsegs H mem y) ->
hm_bytes rsegs H' mem' pp (pc_image (PbCut sh [] None)).
Proof.
intros H mem H' mem' pp sh Hsh B0 Bh Bl Bi K.
rewrite (hwo_img_ph sh Hsh).
assert (L0 : length hsu_img_hdr = 19744%nat) by (vm_compute; reflexivity).
assert (L1 : length (hm_slice hsu_img_hdr 0 16384) = 16384%nat) by (vm_compute; reflexivity).
assert (L2 : length (hm_slice hsu_img_hdr 16396 3348) = 3348%nat) by (vm_compute; reflexivity).
pose proof (hwo_len_hdr sh ltac:(lia)) as Lh.
assert (Lo : length (overwrite (hm_slice hsu_img_hdr 0 16384) 4 (hdr_bytes sh)) = 16384%nat)
  by (rewrite length_overwrite; [exact L1 | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity]).
apply hm_bytes_app. split.
- pose proof (hm_bytes_slice rsegs H mem pp hsu_img_hdr 0 16384 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bb.
  change (Z.of_nat 0) with 0 in Bb. rewrite Z.add_0_r in Bb.
  apply (hm_bytes_patch rsegs H mem H' mem' pp _ 4 _ Bb);
    [exact Bh | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity |].
  rewrite Lh, L1. intros y Hy Hn. change (Z.of_nat 16384) with 16384 in Hy.
  change (Z.of_nat 4) with 4 in Hn. change (Z.of_nat (4 + 12)) with 16 in Hn. apply K; lia.
- rewrite Lo. change (Z.of_nat 16384) with 16384. apply hm_bytes_app. split; [exact Bl|].
  change (length (le64 16)) with 8%nat. change (Z.of_nat 8) with 8. apply hm_bytes_app. split.
  + replace (pp + 16384 + 8) with (pp + 16392) by lia. exact Bi.
  + change (length (le32 (Z.b2z (negb (sh =? 6))))) with 4%nat. change (Z.of_nat 4) with 4.
    pose proof (hm_bytes_slice rsegs H mem pp hsu_img_hdr 16396 3348 B0
      ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bt.
    change (Z.of_nat 16396) with 16396 in Bt. replace (pp + 16384 + 8 + 4) with (pp + 16396) by lia.
    apply (hm_bytes_kept rsegs H mem H' mem' _ _ Bt). rewrite L2. change (Z.of_nat 3348) with 3348.
    intros y Hy. apply K; lia.
Qed.

(* ===================================== the piece statement ===================================== *)
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

Ltac hwo_in_kept := unfold HWO_KEPT; cbn [In]; lia.

(* BO -> PH at image B's record and builder pcs *)
Lemma hsu_piece_W3b_hdr_B : hsu_piece_W3b_hdr_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros cx POST rest HST HPH ly2 S2 W2 regs2 mem2 md2 r sh np [HC [Hsh7 HA13]].
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HST as (HPRE & _ & _ & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & Hppc & Hfresh).
cbn [hi_rsz hi_cid headamp_himg_B] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
(* the bounds of R, pp and F *)
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
  by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
assert (Hin2 : In (e_pp (x_e rsegs cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppc]).
assert (HFd : 0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hsh : 0 <= sh <= 6)
  by (assert (0 <= sh < 8) by (rewrite Esh; unfold hsu_sh; apply Z.mod_pos_bound; lia); lia).
(* the facts of BO's location list *)
unfold hsu_at_cx, hsu_at in HA13. apply Forall_inv in HA13. cbn [fst snd hd_at] in HA13.
unfold hsu_at_cx, hsu_at, hsu_L_hdr in HAT. cbv zeta in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A10 & A11 & A12 & A16 & A17 & A8 & A9 & A19 & A27 & A21 & A23 & A24 & A25 & C38 & C48 & Cf0
  & C100 & C108 & C138 & C150 & A18 & A28 & _).
cbn [fst snd] in A10, A11, A12, A16, A17, A8, A9, A19, A27, A21, A23, A24, A25, C38, C48, Cf0, C100, C108, C138,
  C150, A18, A28.
pose proof A9 as R9. pose proof A10 as R10. pose proof A12 as R12. pose proof A25 as R25. pose proof A27 as R27.
pose proof Cf0 as Vf0. pose proof C108 as V108. pose proof C138 as V138. pose proof C150 as V150.
cbn [hd_at hd_xv] in R9, R10, R12, R25, R27, Vf0, V108, V138, V150.
unfold Layout.OFF_LEN in V138, V150.
pose proof (hm_pp_len rsegs (le32 0) false false false [] false ltac:(unfold POD_BUF_MAX; cbn; lia)
  ltac:(cbn; lia) ltac:(constructor) (w_H W2) mem2 (e_pp (x_e rsegs cx)) HPP) as Vlen.
unfold Layout.OFF_LEN in Vlen. change (Z.of_nat (length (le32 0))) with 4 in Vlen.
eapply (hwo_core B _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 _ regs2 (e_R (x_e rsegs cx)) (e_pp (x_e rsegs cx)) sh POST
  HJ Hin2 Hfresh); try eassumption; try lia.
intros regs3 mem3 md3 HJ3 Hio3 HK3 HM3 Bh Bl Bi Vf8.
apply (HPH ly2 S2 W2 regs3 mem3 md3 r sh np).
unfold hsu_cut_PH. split; [|split; [|split; [|split]]].
- (* the journal and the kept bytes *)
  unfold hsu_core, hsu_mid. split; [exact HJ3|].
  split; [intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]]; apply HK3; hwo_in_kept|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
  split; [exact Hmo|].
  intros a Ha HnS HnE. rewrite <- (Hkeep a Ha HnS HnE).
  apply HM3; [exact Ha | | |]; intros X; apply HnE; unfold hsu_E1.
  + right. unfold PP_SIZE. lia.
  + right. unfold PP_SIZE. lia.
  + left. unfold hd_inw. cbn [hi_w1 headamp_himg_B]. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
    cbn [fst snd hd_xv]. lia.
- (* PH's location list: BO's without a0 and a2, with R+0xf8 = 0 *)
  unfold hsu_at_cx, hsu_at, hsu_L_PH. cbv zeta. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  lazymatch goal with
  | |- hd_at _ _ _ _ _ (LCell XR 248) _ =>
      cbn [hd_at hd_xv]; rewrite (proj2 (Z.eqb_neq sh 7) Hsh7); change (0 mod 2 ^ 64) with 0; exact Vf8
  | |- hd_at _ _ _ _ _ ?l ?v =>
      match goal with A : hd_at _ _ mem2 regs2 _ l v |- _ =>
        apply (hm_at_kept rsegs _ _ _ _ _ _ _ _ _ A); cbn [hm_keeps hd_xv];
        first [ apply HK3; hwo_in_kept | intros i Hi; apply HM3; lia ]
      end
  end.
- (* the frame's shadow: no byte of it is written *)
  apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ _ HFSH).
  intros i Hi. unfold hsu_P0 in Hi. cbn [hi_shA headamp_himg_B] in Hi.
  change (length headamp_B_shA) with 116%nat in Hi.
  apply HM3; unfold shadow_addr, SHADOW_OFF; lia.
- (* the block holds the empty record of this shape *)
  apply (hwo_ph_img (w_H W2) mem2 (w_H W2) mem3 _ sh Hsh HPP Bh Bl);
    [apply hm_bytes_of_val; exact Bi |].
  intros y Hy Hn1 Hn2. apply HM3; lia.
- split; [exact HIN|]. split; [exact HSUF|]. split; [exact Esh|]. split; [exact Enp | exact Er].
Qed.
End e.
End b.

Print Assumptions hsu_piece_W3b_hdr_B.
