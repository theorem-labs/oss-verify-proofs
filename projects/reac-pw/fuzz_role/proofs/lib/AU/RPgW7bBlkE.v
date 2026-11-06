(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 181 of its 205 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bE2.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; E2 is image B's 0x81718 .. 0x81770: e62's address is in s6 (loaded by E1) instead of a reload from a cell, the frame's shadow base is s3, the one cell the block reads is R+0x128 (the cursor, into s10), and the input left goes back from s8 to t1; lib/A/RtPgW7bBase.v / RtPgSteps.v are lib/AU/RtPgW7bBaseB.v / RtPgStepsB.v; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bE2B.v, with its module paths, module names, addresses and numbers changed; 52 of its 217 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bE2.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; E2 is image B's 0x81718 .. 0x81770: e62's address is in s6 (loaded by E1) instead of a reload from a cell, the frame's shadow base is s3, the one cell the block reads is R+0x128 (the cursor, into s10), and the input left goes back from s8 to t1; lib/A/RtPgW7bBase.v / RtPgSteps.v are lib/AU/RtPgW7bBaseB.v / RtPgStepsB.v; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bE2B.v at 9eff5d44f2fd for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan), as RPgW7bBlkE.v: module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; E2 is role B's 0x80ed0 .. 0x80f30: e62's address is reloaded from the cell R+0x158 into a0 (rate: s6, loaded by E1), e62.type's 8 goes through a1, e62.size comes from s6 (rate: s9), the block reads three cells (&e62 R+0x158, the cursor R+0x118 into a3, &pp->len R+0x130 into s6; rate: the cursor R+0x128 into s10) and the input left goes back from s4 to t1 (rate: from s8); lib/AU/RtPgW7bBaseB.v / RtPgStepsB.v are lib/AU/RPgW7bBase.v / RPgSteps.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, which holds the same loaded bytes): block E2 of
   the walk of LLVMFuzzerTestOneInput from G 0x80dc8 to J 0x818d8 (lib/AU/RPgW7bBase.v). Proves no function (kind:
   segment lemma).

   E2, 0x80ed0 .. 0x80f30 (pod.h:214-217, the end of ent_text inlined at pod.h:261: the NUL, e->type and e->size;
   then pod.h:262, t and ch out of scope):
     sb zero,0(a0); ld a0,0x158(s1); li a1,8; sw a1,0(a0); sw s6,4(a0)
     li a0,-8; sb a0 at s3 + 0x14,0x15,0x16,8,9,0xa,0xb,4,5,6,7,0xc,0xd,0xe,0xf (0x80ee8 .. 0x80f20)
     ld a3,0x118(s1); ld s6,0x130(s1); mv t1,s4; j 0x818d8
   No instrumented check: one run of the plain engine (aj_run_to), which follows the `j` to J. The start state keeps
   every register as its own atom (a0 = the NUL's address ev + 8 + n, s6 = n + 1, s1 = R, s3 = shv, the frame's
   shadow base, s4 = the input left) and gives the three frame cells the block reads, R+0x158 (&e62 = ev), R+0x118
   (the cursor) and R+0x130 (&pp->len), as the extra atoms 32, 33, 34 in a read-only region based on s1 (atom 9).
   The writable regions: the NUL's byte (based on atom 10), e62's first 8 bytes (based on atom 32, the value the
   `ld a0` reads) and the shadow granules s3 + 4 .. s3 + 0xf and s3 + 0x14 .. s3 + 0x16 as two regions based on
   atom 19, so that s3 + 0x10 .. s3 + 0x13, which the block does not store, are kept. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* the engine's start state at 0x80ed0: the extra atoms 32, 33, 34 are the cells R+0x158 (&e62), R+0x118 (the
   cursor) and R+0x130 (&pp->len) *)
Definition e2b_extra (ev cur v130 : Z) : list word := [w64 ev; w64 cur; w64 v130].
Definition ssb_E2 : sstate :=
mkSS W7B_E2 sr_atoms
[YP09.mkRegion (Some 10%nat) 0 1 0 1 [];
 YP09.mkRegion (Some 9%nat) 0x118 0x160 0x118 0x118
   [YP09.mkChunk 0x118 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 34 0));
    YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))];
 YP09.mkRegion (Some 32%nat) 0 8 0 8 [];
 YP09.mkRegion (Some 19%nat) 4 16 4 16 [];
 YP09.mkRegion (Some 19%nat) 20 23 20 23 []] None
(mkFacts [] [] []).

(* the leaf's helpers: an atom's own value, a register of the engine's last state, a chunk in a region's list, and
   a byte the shadow stores left (`sb a0` with a0 = -8) *)
Lemma e2b_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Ltac e2b_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.
Ltac e2b_in := solve [cbv [In]; repeat (first [left; reflexivity | right])].
Lemma e2b_f8 : forall E H mem k b lo hi wlo whi cs o,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = b ->
In (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) cs -> aview rsegs H mem (b + o) = Some 0xf8.
Proof.
intros E H mem k b lo hi wlo whi cs o HR Hk Hin.
pose proof (RPgSteps.rl_chunks E _ k b cs lo hi wlo whi HR Hk _ Hin) as Hc.
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

Lemma w7b_E2_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  R ev n shv cur v130,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> R + 0x200 <= 2 ^ 47 ->
getr regs 10 = w64 (ev + 8 + n) -> 0 <= n <= 95 -> getr regs 19 = w64 shv ->
4096 <= ev -> ev + 0x68 <= R ->
0 <= shv -> (shv + 23 <= ev \/ ev + 0x68 <= shv) -> shv + 23 <= R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 ev ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 v130 -> 0 <= v130 < 2 ^ 64 ->
(forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
st_ok rsegs (Ereg regs (e2b_extra ev cur v130)) ssb_E2
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_E2) memc (seg_rom rsegs))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv cur v130
HJ H9 HR1 H10 Hn H19 Hev HevR Hshv Hsh HshR V158 V118 Hcur V130 H130 HWIN.
set (X := e2b_extra ev cur v130).
assert (B9 : bv_unsigned (ew (Ereg regs X) 9) = R)
by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew (Ereg regs X) 10) = ev + 8 + n)
by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew (Ereg regs X) 19) = shv)
by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; lia).
assert (X32 : ew (Ereg regs X) 32 = w64 ev) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 cur) by exact (ew_Ereg_extra regs X 1).
assert (X34 : ew (Ereg regs X) 34 = w64 v130) by exact (ew_Ereg_extra regs X 2).
assert (B32 : bv_unsigned (ew (Ereg regs X) 32) = ev) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
assert (HW : forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
  writable_at rsegs (mrestrict (w_H W) memc) a).
{ intros a Ha. apply apresent_writable. eapply proj1. eapply (awr_byte_present rsegs B LAWS); [exact HJ | exact (HWIN a Ha)]. }
rewrite restrict_mkst_fx. unfold ssb_E2. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite B10. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ R 0x118 8 (SOff 33 0) cur);
      [ apply (RPgSteps.rl_den_atom _ 33 cur X33 Hcur) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V118 ].
    * apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 34 0) v130);
      [ apply (RPgSteps.rl_den_atom _ 34 v130 X34 H130) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V130 ].
    * apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) ev);
      [ apply (RPgSteps.rl_den_atom _ 32 ev X32 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V158 ].
  + rewrite B32. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
  + rewrite B19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B10, B32, B19.
  destruct Hsh as [Hsh|Hsh]; repeat split; lia.
- split; [exact I|split; exact I].
Qed.

Lemma w7b_E2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  R ev n shv cur v130 left,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x200 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 10 = w64 (ev + 8 + n) -> getr regs 22 = w64 (n + 1) -> 0 <= n <= 95 ->
getr regs 19 = w64 shv -> getr regs 20 = w64 left ->
4096 <= ev -> ev mod 8 = 0 -> ev + 0x68 <= R ->
0 <= shv -> (shv + 23 <= ev \/ ev + 0x68 <= shv) -> shv + 23 <= R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 ev ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 v130 -> 0 <= v130 < 2 ^ 64 ->
(forall a, ev <= a < ev + 0x68 \/ shv + 4 <= a < shv + 23 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_E2) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_J regs memc mdc [6; 10; 11; 13; 22]%bv
(fun a => a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23)
(fun regs2 mem2 => getr regs2 13 = w64 cur /\ getr regs2 6 = w64 left /\ getr regs2 22 = w64 v130 /\
 aview rsegs (w_H W) mem2 (ev + 8 + n) = Some 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) ev 4 8 /\ val_mem rsegs (mrestrict (w_H W) mem2) (ev + 4) 4 (n + 1) /\
 (forall j, 4 <= j < 16 \/ 20 <= j < 23 -> aview rsegs (w_H W) mem2 (shv + j) = Some 0xf8))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv cur v130 left
HJ H9 HR0 HR1 HR16 H10 H22 Hn H19 H20 Hev Hev8 HevR Hshv Hsh HshR V158 V118 Hcur V130 H130 HWIN.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
pose proof (w7b_E2_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R ev n shv cur v130
  HJ H9 HR1 H10 Hn H19 Hev HevR Hshv Hsh HshR V158 V118 Hcur V130 H130 HWIN) as HS.
set (X := e2b_extra ev cur v130) in HS.
assert (B10 : bv_unsigned (ew (Ereg regs X) 10) = ev + 8 + n)
by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew (Ereg regs X) 19) = shv)
by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small; lia).
assert (X32 : ew (Ereg regs X) 32 = w64 ev) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 cur) by exact (ew_Ereg_extra regs X 1).
assert (X34 : ew (Ereg regs X) 34 = w64 v130) by exact (ew_Ereg_extra regs X 2).
assert (B32 : bv_unsigned (ew (Ereg regs X) 32) = ev) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
(* the start state's write windows lie in the block's write set *)
assert (HWR : forall a, in_wrange (Ereg regs X) (ss_mem ssb_E2) a ->
  a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23).
{ intros a (r & Hin & Ha). cbn [ssb_E2 ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?B10, ?B32, ?B19 in Ha; lia. }
aj_run_to w7b_tbl_ok HS HJ W7B_J.
(* the start state's regions: the NUL's byte, the cells (read only), e62's first 8 bytes, the two shadow windows,
   each writable by the hypothesis on [ev, ev + 0x68) and [shv + 4, shv + 23) *)
- unfold ssb_E2; cbn [ss_mem].
  apply (w7b_awr_cons _ _ _ _ _ _ _ _ _ _ 10%nat (ev + 8 + n));
  [reflexivity | exact B10 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (w7b_awr_cons _ _ _ _ _ _ _ _ _ _ 32%nat ev);
  [reflexivity | exact B32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply (w7b_awr_cons _ _ _ _ _ _ _ _ _ _ 19%nat shv);
  [reflexivity | exact B19 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply (w7b_awr_cons _ _ _ _ _ _ _ _ _ _ 19%nat shv);
  [reflexivity | exact B19 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWIN; lia |].
  apply awr_ok_nil.
(* the leaf: w7b_post from the engine's last state at J *)
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs X (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun a => a = ev + 8 + n \/ ev <= a < ev + 8 \/ shv + 4 <= a < shv + 16 \/ shv + 20 <= a < shv + 23)
      _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr HWR a Ha Hz).
  + cbv beta.
    (* the regions the run left: 0 the NUL's byte, 2 e62's head, 3 and 4 the shadow windows *)
    lazymatch type of HS with st_ok _ _ ?ssv (restrict _ ?msv) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    let r4 := eval vm_compute in (nth 4 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (RG0 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r0)
    by exact (w7b_region_nth _ ssv (restrict (w_H W) msv) 0%nat r0 HS ltac:(vm_compute; reflexivity));
    assert (RG2 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r2)
    by exact (w7b_region_nth _ ssv (restrict (w_H W) msv) 2%nat r2 HS ltac:(vm_compute; reflexivity));
    assert (RG3 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r3)
    by exact (w7b_region_nth _ ssv (restrict (w_H W) msv) 3%nat r3 HS ltac:(vm_compute; reflexivity));
    assert (RG4 : region_ok rsegs (Ereg regs X) (mrestrict (w_H W) (ms_mem msv)) r4)
    by exact (w7b_region_nth _ ssv (restrict (w_H W) msv) 4%nat r4 HS ltac:(vm_compute; reflexivity))
    end.
    (* a3, t1, s6 *)
    split; [e2b_reg HS; rewrite e2b_den0; exact X33|].
    split; [e2b_reg HS; rewrite e2b_den0, (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20|].
    split; [e2b_reg HS; rewrite e2b_den0; exact X34|].
    (* the NUL *)
    split.
    { pose proof (RPgSteps.rl_chunk0 _ (w_H W) (ms_mem ms) (ev + 8 + n) 0
        (RPgSteps.rl_chunks _ _ 10%nat (ev + 8 + n) _ 0 1 0 1 RG0 B10 (YP09.mkChunk 0 (CVal 1 (SLit 0))) ltac:(e2b_in)))
      as Z0.
      rewrite Z.add_0_r in Z0. exact Z0. }
    (* e62.type = 8, e62.size = n + 1 (the low 32 bits of s6) *)
    split.
    { pose proof (w7b_field _ _ 32%nat ev _ 0 8 0 8 0 4%N (SLit 8) 8 RG2 B32 ltac:(e2b_in) eq_refl ltac:(cbn; lia) ltac:(lia))
      as V0.
      rewrite Z.add_0_r in V0. exact V0. }
    split.
    { refine (w7b_field _ _ 32%nat ev _ 0 8 0 8 4 4%N (SOff 22 0) (n + 1) RG2 B32 _ _ _ _);
      [ e2b_in
      | rewrite e2b_den0, (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
      | lia ]. }
    (* the 15 shadow bytes 0xf8 *)
    intros j Hj.
    assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/
      j = 14 \/ j = 15 \/ j = 20 \/ j = 21 \/ j = 22) by lia.
    clear Hj.
    repeat (destruct Hj' as [-> | Hj'];
      [ first [ refine (e2b_f8 _ _ _ _ _ _ _ _ _ _ _ RG3 B19 _); e2b_in
              | refine (e2b_f8 _ _ _ _ _ _ _ _ _ _ _ RG4 B19 _); e2b_in ] | ]).
    subst j. refine (e2b_f8 _ _ _ _ _ _ _ _ _ _ _ RG4 B19 _). e2b_in.
Qed.
End d.
End b.

Print Assumptions w7b_E2_entry.
Print Assumptions w7b_E2.
