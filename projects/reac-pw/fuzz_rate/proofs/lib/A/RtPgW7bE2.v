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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 204 of its 234 lines of code are new or changed and 260 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, which holds the same loaded bytes): block E2 of
   the walk of LLVMFuzzerTestOneInput from G 0x8150c to J 0x81e00 (lib/A/RtPgW7bBase.v). Proves no function (kind:
   segment lemma).

   E2, 0x815f8 .. 0x81664 (pod.h:214-217, the end of ent_text inlined at pod.h:261: the NUL, e->type and e->size;
   then pod.h:262, t and ch out of scope):
     sb zero,0(a0); ld a0,0x138(s1); addi a1,zero,8; sw a1,0(a0); sw s9,4(a0)
     addi a0,zero,-8; sb a0 at s4 + 0x14,0x15,0x16,8,9,0xa,0xb,4,5,6,7,0xc,0xd,0xe,0xf (0x81610 .. 0x81648)
     ld s11,0xc0(s1); ld s6,0xe8(s1); mv s9,s7; ld s7,0xb0(s1); mv s8,s10; ld s10,0x118(s1); j 0x81e00
   No instrumented check: one run of the plain engine (aj_run_to), which follows the `j` to J. The start state keeps
   every register as its own atom (a0 = the NUL's address ev + 8 + n, s1 = R, s4 = shv, the frame's shadow base) and
   gives the five frame cells the block reads, R+0x138 (e), R+0xc0, R+0xe8, R+0xb0 and R+0x118, as the extra atoms
   32 .. 36 in chunks of one read-only region based on s1 (atom 9). The writable regions: the NUL's byte (based on
   atom 10), e's first 8 bytes (based on atom 32, the value of R+0x138) and the shadow granules s4 + 4 .. s4 + 0xf and
   s4 + 0x14 .. s4 + 0x16 as two regions based on atom 20, so that s4 + 0x10 .. s4 + 0x13, which the block does not
   store, are kept. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* the engine's start state at 0x815f8: the extra atoms 32 .. 36 are the cells R+0x138 (e), R+0xc0, R+0xe8, R+0xb0,
   R+0x118 *)
Definition e2_extra (ev vc0 ve8 vb0 v118 : Z) : list word := [w64 ev; w64 vc0; w64 ve8; w64 vb0; w64 v118].
Definition ss_E2 : sstate :=
mkSS W7_E2 sr_atoms
[YP09.mkRegion (Some 10%nat) 0 1 0 1 [];
 YP09.mkRegion (Some 9%nat) 0xb0 0x140 0xb0 0xb0
   [YP09.mkChunk 0xb0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x118 (CVal 8 (SOff 36 0));
    YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))];
 YP09.mkRegion (Some 32%nat) 0 8 0 8 [];
 YP09.mkRegion (Some 20%nat) 4 16 4 16 [];
 YP09.mkRegion (Some 20%nat) 20 23 20 23 []] None
(mkFacts [] [] []).

(* the leaf's helpers: an atom's own value, a register of the engine's last state, a chunk in a region's list, and
   a byte the shadow stores left (`sb a0` with a0 = -8) *)
Lemma e2_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Ltac e2_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.
Ltac e2_in := solve [cbv [In]; repeat (first [left; reflexivity | right])].
Lemma e2_f8 : forall E H mem k b lo hi wlo whi cs o,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = b ->
In (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) cs -> aview rsegs H mem (b + o) = Some 0xf8.
Proof.
intros E H mem k b lo hi wlo whi cs o HR Hk Hin.
pose proof (RtPgSteps.rts_chunks E _ k b cs lo hi wlo whi HR Hk _ Hin) as Hc.
destruct (Hc 0 ltac:(cbn; lia)) as (bt & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (b + o) = Some bt) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
first [reflexivity | (vm_compute; reflexivity)].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w7_E2_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  R ev n shv vb0 vc0 ve8 v118,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> R + 0x1e0 <= 2 ^ 47 ->
getr regs 10 = w64 (ev + 8 + n) -> 0 <= n <= 95 -> getr regs 20 = w64 shv ->
4096 <= ev -> ev + 0x68 <= R ->
0 <= shv -> (shv + 23 <= ev \/ ev + 0x68 <= shv) -> shv + 23 <= R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 ev ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 vc0 -> 0 <= vc0 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ve8 -> 0 <= ve8 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 vb0 -> 0 <= vb0 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 v118 -> 0 <= v118 < 2 ^ 64 ->
(forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
st_ok rsegs (Ereg regs (e2_extra ev vc0 ve8 vb0 v118)) ss_E2
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7_E2) memc (seg_rom rsegs))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv vb0 vc0 ve8 v118
HJ H9 HR1 H10 Hn H20 Hev HevR Hshv Hsh HshR V138 Vc0 Hc0 Ve8 He8 Vb0 Hb0 V118 H118 HWIN.
set (X := e2_extra ev vc0 ve8 vb0 v118).
assert (B9 : bv_unsigned (ew (Ereg regs X) 9) = R)
by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew (Ereg regs X) 10) = ev + 8 + n)
by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew (Ereg regs X) 20) = shv)
by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (X32 : ew (Ereg regs X) 32 = w64 ev) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 vc0) by exact (ew_Ereg_extra regs X 1).
assert (X34 : ew (Ereg regs X) 34 = w64 ve8) by exact (ew_Ereg_extra regs X 2).
assert (X35 : ew (Ereg regs X) 35 = w64 vb0) by exact (ew_Ereg_extra regs X 3).
assert (X36 : ew (Ereg regs X) 36 = w64 v118) by exact (ew_Ereg_extra regs X 4).
assert (B32 : bv_unsigned (ew (Ereg regs X) 32) = ev) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
assert (HW : forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
  writable_at rsegs (mrestrict (w_H W) memc) a).
{ intros a Ha. apply apresent_writable. eapply proj1. eapply (awr_byte_present rsegs B LAWS); [exact HJ | exact (HWIN a Ha)]. }
rewrite restrict_mkst_fx. unfold ss_E2. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite B10. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ R 0xb0 8 (SOff 35 0) vb0);
      [ apply (RtPgSteps.rts_den_atom _ 35 vb0 X35 Hb0) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vb0 ].
    * apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SOff 33 0) vc0);
      [ apply (RtPgSteps.rts_den_atom _ 33 vc0 X33 Hc0) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vc0 ].
    * apply (chunk_ok_val rsegs _ _ R 0xe8 8 (SOff 34 0) ve8);
      [ apply (RtPgSteps.rts_den_atom _ 34 ve8 X34 He8) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Ve8 ].
    * apply (chunk_ok_val rsegs _ _ R 0x118 8 (SOff 36 0) v118);
      [ apply (RtPgSteps.rts_den_atom _ 36 v118 X36 H118) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V118 ].
    * apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) ev);
      [ apply (RtPgSteps.rts_den_atom _ 32 ev X32 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V138 ].
  + rewrite B32. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B10, B20, B32.
  destruct Hsh as [Hsh|Hsh]; repeat split; lia.
- split; [exact I|split; exact I].
Qed.

Lemma w7_E2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  R ev n shv cur left vb0 vc0 ve8 v118,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 10 = w64 (ev + 8 + n) -> getr regs 25 = w64 (n + 1) -> 0 <= n <= 95 ->
getr regs 20 = w64 shv -> getr regs 23 = w64 cur -> getr regs 26 = w64 left ->
4096 <= ev -> ev mod 8 = 0 -> ev + 0x68 <= R ->
0 <= shv -> (shv + 23 <= ev \/ ev + 0x68 <= shv) -> shv + 23 <= R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 ev ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 vc0 -> 0 <= vc0 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ve8 -> 0 <= ve8 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 vb0 -> 0 <= vb0 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 v118 -> 0 <= v118 < 2 ^ 64 ->
(forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_E2) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_J regs memc mdc [10; 11; 22; 23; 24; 25; 26; 27]%bv
(fun a => a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23)
(fun regs2 mem2 => getr regs2 27 = w64 vc0 /\ getr regs2 22 = w64 ve8 /\ getr regs2 25 = w64 cur /\
 getr regs2 23 = w64 vb0 /\ getr regs2 24 = w64 left /\ getr regs2 26 = w64 v118 /\
 aview rsegs (w_H W) mem2 (ev + 8 + n) = Some 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) ev 4 8 /\ val_mem rsegs (mrestrict (w_H W) mem2) (ev + 4) 4 (n + 1) /\
 (forall j, 4 <= j < 16 \/ 20 <= j < 23 -> aview rsegs (w_H W) mem2 (shv + j) = Some 0xf8))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv cur left vb0 vc0 ve8 v118
HJ H9 HR0 HR1 HR16 H10 H25 Hn H20 H23 H26 Hev Hev8 HevR Hshv Hsh HshR V138 Vc0 Hc0 Ve8 He8 Vb0 Hb0 V118 H118 HWIN.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof (w7_E2_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv vb0 vc0 ve8 v118
  HJ H9 HR1 H10 Hn H20 Hev HevR Hshv Hsh HshR V138 Vc0 Hc0 Ve8 He8 Vb0 Hb0 V118 H118 HWIN) as HS.
set (X := e2_extra ev vc0 ve8 vb0 v118) in HS.
assert (B10 : bv_unsigned (ew (Ereg regs X) 10) = ev + 8 + n)
by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew (Ereg regs X) 20) = shv)
by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (X32 : ew (Ereg regs X) 32 = w64 ev) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 vc0) by exact (ew_Ereg_extra regs X 1).
assert (X34 : ew (Ereg regs X) 34 = w64 ve8) by exact (ew_Ereg_extra regs X 2).
assert (X35 : ew (Ereg regs X) 35 = w64 vb0) by exact (ew_Ereg_extra regs X 3).
assert (X36 : ew (Ereg regs X) 36 = w64 v118) by exact (ew_Ereg_extra regs X 4).
assert (B32 : bv_unsigned (ew (Ereg regs X) 32) = ev) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
(* the start state's write windows lie in the block's write set *)
assert (HWR : forall a, in_wrange (Ereg regs X) (ss_mem ss_E2) a ->
  a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23).
{ intros a (r & Hin & Ha). cbn [ss_E2 ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?B10, ?B20, ?B32 in Ha; lia. }
aj_run_to w7_tbl_ok HS HJ W7_J.
(* the start state's regions: the NUL's byte, the five cells (read only), e's first 8 bytes, the two shadow
   windows, each writable by the hypothesis on [ev, ev + 0x68) and [shv + 4, shv + 23) *)
- unfold ss_E2; cbn [ss_mem].
  apply (w7_awr_cons _ _ _ _ _ _ _ _ _ _ 10%nat (ev + 8 + n));
  [reflexivity | exact B10 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (w7_awr_cons _ _ _ _ _ _ _ _ _ _ 32%nat ev);
  [reflexivity | exact B32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply (w7_awr_cons _ _ _ _ _ _ _ _ _ _ 20%nat shv);
  [reflexivity | exact B20 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply (w7_awr_cons _ _ _ _ _ _ _ _ _ _ 20%nat shv);
  [reflexivity | exact B20 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply awr_ok_nil.
(* the leaf: w7_post from the engine's last state at J *)
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs X (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7_kept_run (fun a => a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23)
      _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr HWR a Ha Hz).
  + cbv beta.
    (* the regions the run left: 0 the NUL's byte, 2 e's head, 3 and 4 the shadow windows *)
    lazymatch type of HS with st_ok _ _ ?ssv (restrict _ ?msv) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r4 := eval vm_compute in (nth 4 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (RG0 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r0)
    by exact (w7_region_nth _ ssv (restrict (w_H W) msv) 0%nat r0 HS ltac:(vm_compute; reflexivity));
    assert (RG2 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r2)
    by exact (w7_region_nth _ ssv (restrict (w_H W) msv) 2%nat r2 HS ltac:(vm_compute; reflexivity));
    assert (RG3 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r3)
    by exact (w7_region_nth _ ssv (restrict (w_H W) msv) 3%nat r3 HS ltac:(vm_compute; reflexivity));
    assert (RG4 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r4)
    by exact (w7_region_nth _ ssv (restrict (w_H W) msv) 4%nat r4 HS ltac:(vm_compute; reflexivity))
    end.
    (* s11, s6, s9, s7, s8, s10 *)
    split; [e2_reg HS; rewrite e2_den0; exact X33|].
    split; [e2_reg HS; rewrite e2_den0; exact X34|].
    split; [e2_reg HS; rewrite e2_den0, (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23|].
    split; [e2_reg HS; rewrite e2_den0; exact X35|].
    split; [e2_reg HS; rewrite e2_den0, (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26|].
    split; [e2_reg HS; rewrite e2_den0; exact X36|].
    (* the NUL *)
    split.
    { pose proof (RtPgSteps.rts_chunk0 _ (w_H W) (ms_mem ms) (ev + 8 + n) 0
        (RtPgSteps.rts_chunks _ _ 10%nat (ev + 8 + n) _ 0 1 0 1 RG0 B10 (YP09.mkChunk 0 (CVal 1 (SLit 0))) ltac:(e2_in)))
      as Z0.
      rewrite Z.add_0_r in Z0. exact Z0. }
    (* e.type = 8, e.size = n + 1 (the low 32 bits of s9) *)
    split.
    { pose proof (w7_field _ _ 32%nat ev _ 0 8 0 8 0 4%N (SLit 8) 8 RG2 B32 ltac:(e2_in) eq_refl ltac:(cbn; lia) ltac:(lia))
      as V0.
      rewrite Z.add_0_r in V0. exact V0. }
    split.
    { refine (w7_field _ _ 32%nat ev _ 0 8 0 8 4 4%N (SOff 25 0) (n + 1) RG2 B32 _ _ _ _);
      [ e2_in
      | rewrite e2_den0, (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
      | lia ]. }
    (* the 15 shadow bytes 0xf8 *)
    intros j Hj.
    assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/
      j = 14 \/ j = 15 \/ j = 20 \/ j = 21 \/ j = 22) by lia.
    clear Hj.
    repeat (destruct Hj' as [-> | Hj'];
      [ first [ refine (e2_f8 _ _ _ _ _ _ _ _ _ _ _ RG3 B20 _); e2_in
              | refine (e2_f8 _ _ _ _ _ _ _ _ _ _ _ RG4 B20 _); e2_in ] | ]).
    subst j. refine (e2_f8 _ _ _ _ _ _ _ _ _ _ _ RG4 B20 _). e2_in.
Qed.
End d.
End b.

Print Assumptions w7_E2_entry.
Print Assumptions w7_E2.
