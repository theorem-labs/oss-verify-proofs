(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 246 of its 275 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the registers (n in s9, the part string in s8, t in s5, the part pointer in s6), the frame slots (parts[1..3] at R+0x160.., e.body at R+0x108) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkB.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the registers (n in s9, the part string in s10, t in s11, the part pointer in s2, the part's length in s6), the frame slots (parts[1..3] at R+0x1a0.., e62.body at R+0x130) and the frame bound (R + 0x220 <= 2^47) are image B's; E1 is image B's 0x816fc .. 0x81714: the reloads of R+0x158 and R+0x150 and the UBSan test of e62.body + n against the cell R+0x100 (~(F + 0x218)), decided by the engine from the cell's atom range, before the NUL's address; lib/A/RtPgW7bBase.v is lib/AU/RtPgW7bBaseB.v; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bBlkBB.v, with its module paths, module names, addresses and numbers changed; 47 of its 267 lines of code are new or changed and 55 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the registers (n in s9, the part string in s8, t in s5, the part pointer in s6), the frame slots (parts[1..3] at R+0x160.., e.body at R+0x108) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkB.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the registers (n in s9, the part string in s10, t in s11, the part pointer in s2, the part's length in s6), the frame slots (parts[1..3] at R+0x1a0.., e62.body at R+0x130) and the frame bound (R + 0x220 <= 2^47) are image B's; E1 is image B's 0x816fc .. 0x81714: the reloads of R+0x158 and R+0x150 and the UBSan test of e62.body + n against the cell R+0x100 (~(F + 0x218)), decided by the engine from the cell's atom range, before the NUL's address; lib/A/RtPgW7bBase.v is lib/AU/RtPgW7bBaseB.v; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bBlkBB.v at 9eff5d44f2fd for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; the pcs, the registers (n in s6, the part string in s10, t in s9, the part pointer in s2, the part's length in s8), the frame slots (parts[1..3] at R+0x180 .., e62.body at R+0x110) and the frame bound (R + 0x200 <= 2^47) are role B's; D loads e62.body into s2 (rate: s10); E1 is role B's 0x80eb8 .. 0x80ecc: the reload of pp (R+0x140) into a5 and of the cell R+0xf0 (~(F + 0x218)), the UBSan test of e62.body + n against that cell, decided by the engine from the cell's atom range, and the NUL's address (rate's E1 reloads &pp->len and &e62 instead of pp; role B's E2 reloads them); lib/AU/RtPgW7bBaseB.v is lib/AU/RPgW7bBase.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, which holds the same loaded bytes): blocks B, C,
   D and E1 of the walk of LLVMFuzzerTestOneInput from 0x80dc8 (lib/AU/RPgW7bBase.v). Proves no function (kind:
   segment lemma).

   No block holds an instrumented check, so each is one run of the plain engine (aj_run_to); every branch is
   decided by the start state's atom facts or by literal offsets of one atom.
   B,  0x80e64 .. 0x80e84 (pod.h:256-258, one turn's clamp and memcpy(t + n, parts[i], l)):
     mv s8,a0; add a0,a0,s6; li a1,95; bgeu a1,a0 -> 0x80e78 (taken: l <= 21, n <= 40)
     add a0,s9,s6; mv a1,s10; mv a2,s8; jal __asan_memcpy
   C,  0x80e88 .. 0x80e60 (i = 0 .. 2: n += l, the next part, strlen(parts[i+1])):
     addi s2,s2,8; add s6,s8,s6; addi a0,s1,0x198; bne s2,a0 -> 0x80e58 (taken: s2 = R + 0x180 + 8 i)
     ld s10,0(s2); mv a0,s10; jal strlen
   D,  0x80e88 .. 0x80eb4 (i = 3: n += l, the 95 clamp of ent_text, memcpy(e62.body, t, n)):
     addi s2,s2,8; add s6,s8,s6; addi a0,s1,0x198; bne s2,a0 (not taken: s2 = R + 0x198)
     li a0,95; bltu s6,a0 -> 0x80ea4 (taken: n + l <= 61); ld s2,0x110(s1); mv a0,s2; mv a1,s9;
     mv a2,s6; jal __asan_memcpy
   E1, 0x80eb8 .. 0x80ecc (the reloads, the UBSan test, the NUL's address):
     ld a5,0x140(s1); ld a0,0xf0(s1); bgeu a0,s6 -> 0x80ec8 (taken; the other arm `j` 0x82604, the `unimp`)
     add a0,s2,s6; addi s6,s6,1
   A frame slot the block reads (parts[i+1] at R + 0x180 + 8 i, e62.body at R + 0x110) is a read-only region of
   atom 9 (s1 = R) whose one chunk holds the extra atom 32, the slot's value; E1's two cells are the extra atoms
   32 (R+0x140, pp) and 33 (R+0xf0) of one such region, and the cell R+0xf0 (which holds ~(F + 0x218)) carries the
   closed range [2^63, 2^64 - 1], so that `bgeu a0,s6` 0x80ec0 against n in [0, 95] is decided by computation and
   the trap arm is never run. *)
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


Lemma w7b_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* the register r of the engine's last state: its symbolic value, computed *)
Ltac w7b_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.

(* a read-only 8-byte slot of the frame at R + lo whose chunk holds the extra atom 32 *)
Definition w7b_slot (lo : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo (lo + 8) lo lo [YP09.mkChunk lo (CVal 8 (SOff 32 0))].
(* the start state of C and D: s2 = R + c, the slot at R + so, the facts on R, n and l *)
Definition ssb_CD (c so : Z) : sstate :=
mkSS W7B_AFTER_MEMCPY (sr_set sr_atoms 18%bv (SOff 9 c)) [w7b_slot so] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x200) 4); (22%nat, mkAF 0 40 0); (24%nat, mkAF 0 21 0)] [] []).
Lemma w7b_CD_nowr : forall E c so a, ~ in_wrange E (ss_mem (ssb_CD c so)) a.
Proof. intros E c so a (r & [<-|[]] & Hb). cbn [w7b_slot YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.
Lemma w7b_slot_wf : forall so, regions_wf [w7b_slot so] = true.
Proof.
intros so. cbn [regions_wf]. unfold region_wf, chunk_inside, YP09.c_len, cv_len, w7b_slot.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val forallb].
repeat match goal with |- context [?a <=? ?b] =>
  let H := fresh in assert (H : (a <=? b) = true) by (apply Z.leb_le; lia); rewrite H; clear H end.
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7b_CD_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) R n l v c so,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x200 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + c) -> 0 <= c <= 0x200 ->
getr regs 22 = w64 n -> getr regs 24 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
0 <= so -> so + 8 <= 0x200 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + so) 8 v -> 0 <= v < 2 ^ 64 ->
st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (ssb_CD c so)
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs))).
Proof.
intros W memc regs R n l v c so H9 HR1 HR2 HR3 H18 Hc H22 H24 Hn Hl Hso1 Hso2 Hval Hv.
assert (E9 : ew (Ereg regs [Z_to_bv 64 v]) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E22 : ew (Ereg regs [Z_to_bv 64 v]) 22 = w64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew (Ereg regs [Z_to_bv 64 v]) 24 = w64 l) by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
rewrite restrict_mkst_fx. unfold ssb_CD. apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  rewrite H18, denot_lit_U, (U_atom_off _ 9 R c E9) by lia. reflexivity.
- apply w7b_slot_wf.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, w7b_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R so 8 (SOff 32 0) v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hval].
  rewrite w7b_den0. exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E24. unfold w64. rewrite !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
  repeat split; first [exact HR3 | lia].
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================== B: 0x80e64 -> 0x5116c ======================== *)
Definition ssb_B : sstate :=
mkSS W7B_AFTER_STRLEN sr_atoms [] None (mkFacts [(10%nat, mkAF 0 21 0); (22%nat, mkAF 0 40 0)] [] []).

Lemma w7b_B : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) l n x t,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 l -> 0 <= l <= 21 -> getr regs 22 = w64 n -> 0 <= n <= 40 ->
getr regs 26 = w64 x -> getr regs 25 = w64 t -> 0 <= t -> t + 0x80 <= 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_STRLEN) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_MEMCPY regs memc mdc [1; 10; 11; 12; 24]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_MEMCPY /\ getr regs2 10 = w64 (t + n) /\ getr regs2 11 = w64 x /\
 getr regs2 12 = w64 l /\ getr regs2 24 = w64 l)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs l n x t HJ H10 Hl H22 Hn H26 H25 Ht Ht2.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = w64 l) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E22 : ew (Ereg regs []) 22 = w64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew (Ereg regs []) 26 = w64 x) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E25 : ew (Ereg regs []) 25 = w64 t) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (HS : st_ok rsegs (Ereg regs []) ssb_B (restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_STRLEN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ssb_B f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E22. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
aj_run_to w7b_tbl_ok HS HJ W7B_MEMCPY.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; reflexivity|].
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 t E25), (U_atom _ 22 n E22) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E26|].
    split; w7b_reg HS; rewrite w7b_den0; exact E10.
Qed.

(* ======================== C: 0x80e88 -> 0x41b60 (i = 0 .. 2) ======================== *)
Lemma w7b_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i : nat) R n l x',
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> (i < 3)%nat ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x200 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x178 + 8 * Z.of_nat i) -> getr regs 22 = w64 n -> getr regs 24 = w64 l ->
0 <= n <= 40 -> 0 <= l <= 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x180 + 8 * Z.of_nat i) 8 x' -> 0 <= x' < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_STRLEN regs memc mdc [1; 10; 18; 22; 26]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_STRLEN /\ getr regs2 10 = w64 x' /\ getr regs2 26 = w64 x' /\
 getr regs2 18 = w64 (R + 0x180 + 8 * Z.of_nat i) /\ getr regs2 22 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i R n l x' HJ Hi H9 HR1 HR2 HR3 H18 H22 H24 Hn Hl Hval Hx.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (Ho : 8 * Z.of_nat i = 0 \/ 8 * Z.of_nat i = 8 \/ 8 * Z.of_nat i = 16) by lia.
remember (8 * Z.of_nat i) as o eqn:Hoi. clear Hoi Hi i.
assert (E9 : ew (Ereg regs [Z_to_bv 64 x']) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E22 : ew (Ereg regs [Z_to_bv 64 x']) 22 = w64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew (Ereg regs [Z_to_bv 64 x']) 24 = w64 l) by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew (Ereg regs [Z_to_bv 64 x']) 32 = w64 x') by exact (ew_Ereg_extra regs [Z_to_bv 64 x'] 0).
assert (H18' : getr regs 18 = w64 (R + (0x178 + o))) by (rewrite H18; unfold w64; f_equal; lia).
assert (Hval' : val_mem rsegs (mrestrict (w_H W) memc) (R + (0x180 + o)) 8 x')
  by (replace (R + (0x180 + o)) with (R + 0x180 + o) by lia; exact Hval).
pose proof (w7b_CD_entry W memc regs R n l x' (0x178 + o) (0x180 + o) H9 HR1 HR2 HR3 H18' ltac:(lia) H22 H24 Hn Hl
  ltac:(lia) ltac:(lia) Hval' Hx) as HS.
clear H18 Hval H18' Hval'.
destruct Ho as [-> | [-> | ->]].
all: aj_run_to w7b_tbl_ok HS HJ W7B_STRLEN; [awr_ok_tac |
  eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ];
  [ eapply (w7b_regs_kept _ _ ms regs [Z_to_bv 64 x'] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity]
  | intros a Ha Hz;
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_CD_nowr _ _ _ a Hw) a Ha Hz)
  | cbv beta;
    split; [w7b_reg HS; reflexivity|];
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|];
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|];
    split; [w7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 9 R _ E9) by lia; unfold w64; f_equal; lia|];
    w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 22 n E22), (U_atom _ 24 l E24) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia ] ].
Qed.

(* ======================== D: 0x80e88 -> 0x5116c (i = 3) ======================== *)
Lemma w7b_D : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R n l t eb,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x200 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x190) -> getr regs 22 = w64 n -> getr regs 24 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
getr regs 25 = w64 t ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 eb -> 0 <= eb < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_MEMCPY regs memc mdc [1; 10; 11; 12; 18; 22]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_TEXT /\ getr regs2 10 = w64 eb /\ getr regs2 11 = w64 t /\
 getr regs2 12 = w64 (n + l) /\ getr regs2 18 = w64 eb /\ getr regs2 22 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R n l t eb HJ H9 HR1 HR2 HR3 H18 H22 H24 Hn Hl H25 Hval Heb.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E22 : ew (Ereg regs [Z_to_bv 64 eb]) 22 = w64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E25 : ew (Ereg regs [Z_to_bv 64 eb]) 25 = w64 t) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E24 : ew (Ereg regs [Z_to_bv 64 eb]) 24 = w64 l) by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew (Ereg regs [Z_to_bv 64 eb]) 32 = w64 eb) by exact (ew_Ereg_extra regs [Z_to_bv 64 eb] 0).
pose proof (w7b_CD_entry W memc regs R n l eb 0x190 0x110 H9 HR1 HR2 HR3 H18 ltac:(lia) H22 H24 Hn Hl
  ltac:(lia) ltac:(lia) Hval Heb) as HS.
aj_run_to w7b_tbl_ok HS HJ W7B_MEMCPY.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [Z_to_bv 64 eb] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_CD_nowr _ _ _ a Hw) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; reflexivity|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E25|].
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 22 n E22), (U_atom _ 24 l E24) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|].
    w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 22 n E22), (U_atom _ 24 l E24) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia.
Qed.

(* ======================== E1: 0x80eb8 -> 0x80ed0 ======================== *)
(* the two cells E1 reads, R+0x140 (pp) and R+0xf0 (~(F + 0x218)), as the extra atoms 32, 33 of one read-only
   region based on s1 (atom 9); the closed range of atom 33 decides the UBSan test *)
Definition e1b_extra (v140 vf0 : Z) : list word := [w64 v140; w64 vf0].
Definition ssb_E1 : sstate :=
mkSS W7B_AFTER_TEXT sr_atoms
[YP09.mkRegion (Some 9%nat) 0xf0 0x148 0xf0 0xf0
   [YP09.mkChunk 0xf0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x140 (CVal 8 (SOff 32 0))]] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x200) 4); (22%nat, mkAF 0 95 0);
          (33%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] []).
Lemma w7b_E1_nowr : forall E a, ~ in_wrange E (ss_mem ssb_E1) a.
Proof. intros E a (r & [<-|[]] & Hb). cbn [YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.

Lemma w7b_E1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R eb n v140 vf0,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x200 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 eb -> getr regs 22 = w64 n -> 0 <= eb -> 0 <= n <= 95 -> eb + n + 1 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 v140 -> 0 <= v140 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 vf0 -> 2 ^ 63 <= vf0 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_TEXT) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_E2 regs memc mdc [10; 15; 22]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (eb + n) /\ getr regs2 22 = w64 (n + 1) /\ getr regs2 15 = w64 v140)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R eb n v140 vf0
HJ H9 HR1 HR2 HR3 H18 H22 Heb Hn Hsum V140 H140 Vf0 Hf0.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
set (X := e1b_extra v140 vf0).
assert (E9 : ew (Ereg regs X) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew (Ereg regs X) 18 = w64 eb) by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E22 : ew (Ereg regs X) 22 = w64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (X32 : ew (Ereg regs X) 32 = w64 v140) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 vf0) by exact (ew_Ereg_extra regs X 1).
assert (B9 : bv_unsigned (ew (Ereg regs X) 9) = R) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs X) ssb_E1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_TEXT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssb_E1. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ R 0xf0 8 (SOff 33 0) vf0);
      [ apply (RPgSteps.rl_den_atom _ 33 vf0 X33 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vf0 ].
    + apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 32 0) v140);
      [ apply (RPgSteps.rl_den_atom _ 32 v140 X32 H140) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V140 ].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E22, X33. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat split; first [exact HR3 | lia]. }
aj_run_to w7b_tbl_ok HS HJ W7B_E2.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs X (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_E1_nowr _ a Hw) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 18 eb E18), (U_atom _ 22 n E22) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 22 n 1 E22) by lia; reflexivity|].
    w7b_reg HS; rewrite w7b_den0; exact X32.
Qed.
End d.
End b.

Print Assumptions w7b_B.
Print Assumptions w7b_C.
Print Assumptions w7b_D.
Print Assumptions w7b_E1.
