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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 203 of its 237 lines of code are new or changed and 256 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the registers (n in s9, the part string in s8, t in s5, the part pointer in s6), the frame slots (parts[1..3] at R+0x160.., e.body at R+0x108) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkB.v, with its module paths, addresses and numbers changed; 140 of its 241 lines of code are new or changed and 136 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638; its blocks B, C and D
   walked again on fuzz_headamp.asan-ubsan's own code (B's registers s4, s7, s10, s2 and cells R+0x178 .., R+0x118),
   its E1 replaced by image B's own E1 (three cell loads and a UBSan bound test), the post HPgCaseB.cb_post, the
   statements HPgW7bBase's, w7_ -> hw7b_, module paths. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): blocks B, C, D and E1 of
   the walk of LLVMFuzzerTestOneInput from G 0x81afc to J 0x82618 (lib/AU/HPgW7bBase.v). Proves no function (kind:
   segment lemma).

   No block holds an instrumented check, so each is one run of the plain engine (aj_run_to); every branch is
   decided by the start state's atom facts or by literal offsets of one atom.
   B,  0x81b98 .. 0x81bb8 (pod.h:255-257, one turn's clamp and memcpy(t + n, parts[i], l)):
     mv s4,a0; add a0,a0,s10; addi a1,zero,0x5f; bgeu a1,a0 -> 0x81bac (taken: l <= 21, n <= 40)
     add a0,s9,s10; mv a1,s7; mv a2,s4; jal memcpy 0x51d8c
   C,  0x81bbc .. 0x81b94 (i = 0 .. 2: n += l, the next part, strlen(parts[i+1])):
     addi s2,s2,8; add s10,s4,s10; addi a0,s1,0x198; bne s2,a0 -> 0x81b8c (taken: s2 = R + 0x180 + 8 i)
     ld s7,0(s2); mv a0,s7; jal strlen 0x41c18
   D,  0x81bbc .. 0x81be8 (i = 3: n += l, the 95 clamp of ent_text, memcpy(e62.body, t, n)):
     addi s2,s2,8; add s10,s4,s10; addi a0,s1,0x198; bne s2,a0 (not taken: s2 = R + 0x198)
     addi a0,zero,0x5f; bltu s10,a0 -> 0x81bd8 (taken: n + l <= 61); ld s7,0x118(s1); mv a0,s7; mv a1,s9;
     mv a2,s10; jal memcpy 0x51d8c
   E1, 0x81bec .. 0x81c04 (pod.h:258, the NUL's address):
     ld s2,0x138(s1); ld s4,0x130(s1); ld a0,0xe8(s1); bgeu a0,s10 -> 0x81c00 (the UBSan bound test, taken:
     a0 >= 95 >= n); add a0,s7,s10; addi s10,s10,1
   A frame cell a block loads (parts[i+1] at R + 0x180 + 8 i, e62 + 8 at R + 0x118; E1's three cells) is a
   read-only region of atom 9 (s1 = R) whose chunks hold extra atoms (32, 33, 34), the cells' values.
   REGISTERS: s1 = R (x9), s2 (x18), s4 (x20), s7 (x23), s9 = t (x25), s10 = n (x26), a0 .. a2 (x10 .. x12), ra
   (x1); CELLS read: R+0x180 .. R+0x190, R+0x118, R+0x130, R+0x138, R+0xe8; none written. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgPropKit HPgW7bBase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma hw7b_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* the register r of the engine's last state: its symbolic value, computed *)
Ltac hw7b_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.

(* a read-only 8-byte slot of the frame at R + lo whose chunk holds the extra atom 32 *)
Definition hw7b_slot (lo : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo (lo + 8) lo lo [YP09.mkChunk lo (CVal 8 (SOff 32 0))].
(* the start state of C and D: s2 = R + c, the slot at R + so, the facts on R, n and l *)
Definition ss_CD (c so : Z) : sstate :=
mkSS HW7B_AFTER_MEMCPY (sr_set sr_atoms 18%bv (SOff 9 c)) [hw7b_slot so] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x220) 4); (26%nat, mkAF 0 40 0); (20%nat, mkAF 0 21 0)] [] []).
Lemma hw7b_CD_nowr : forall E c so a, ~ in_wrange E (ss_mem (ss_CD c so)) a.
Proof. intros E c so a (r & [<-|[]] & Hb). cbn [hw7b_slot YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.
Lemma hw7b_slot_wf : forall so, regions_wf [hw7b_slot so] = true.
Proof.
intros so. cbn [regions_wf]. unfold region_wf, chunk_inside, YP09.c_len, cv_len, hw7b_slot.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val forallb].
repeat match goal with |- context [?a <=? ?b] =>
  let H := fresh in assert (H : (a <=? b) = true) by (apply Z.leb_le; lia); rewrite H; clear H end.
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hw7b_CD_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) R n l v c so,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + c) -> 0 <= c <= 0x220 ->
getr regs 26 = w64 n -> getr regs 20 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
0 <= so -> so + 8 <= 0x220 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + so) 8 v -> 0 <= v < 2 ^ 64 ->
st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (ss_CD c so)
(restrict (w_H W) (mkst regs (Z_to_bv 64 HW7B_AFTER_MEMCPY) memc (seg_rom rsegs))).
Proof.
intros W memc regs R n l v c so H9 HR1 HR2 HR3 H18 Hc H26 H20 Hn Hl Hso1 Hso2 Hval Hv.
assert (E9 : ew (Ereg regs [Z_to_bv 64 v]) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew (Ereg regs [Z_to_bv 64 v]) 26 = w64 n) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E20 : ew (Ereg regs [Z_to_bv 64 v]) 20 = w64 l) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
rewrite restrict_mkst_fx. unfold ss_CD. apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  rewrite H18, denot_lit_U, (U_atom_off _ 9 R c E9) by lia. reflexivity.
- apply hw7b_slot_wf.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, hw7b_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R so 8 (SOff 32 0) v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hval].
  rewrite hw7b_den0. exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E9, E26, E20. unfold w64. rewrite !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
  repeat split; first [exact HR3 | lia].
Qed.

(* ======================== B: 0x81b98 -> 0x51d8c ======================== *)
Definition ss_B : sstate :=
mkSS HW7B_AFTER_STRLEN sr_atoms [] None (mkFacts [(10%nat, mkAF 0 21 0); (26%nat, mkAF 0 40 0)] [] []).

Lemma hw7b_B : forall B, hw7b_B_stmt B.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs l n x t HJ H10 Hl H26 Hn H23 H25 Ht Ht2.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hw7b_wx as Hwx. pose proof hw7b_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = w64 l) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E26 : ew (Ereg regs []) 26 = w64 n) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E23 : ew (Ereg regs []) 23 = w64 x) by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E25 : ew (Ereg regs []) 25 = w64 t) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (HS : st_ok rsegs (Ereg regs []) ss_B (restrict (w_H W) (mkst regs (Z_to_bv 64 HW7B_AFTER_STRLEN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_B f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E26. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
aj_run_to hw7b_tbl_ok HS HJ HW7B_MEMCPY.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + cbv beta.
    split; [hw7b_reg HS; reflexivity|].
    split; [hw7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 t E25), (U_atom _ 26 n E26) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E23|].
    split; hw7b_reg HS; rewrite hw7b_den0; exact E10.
Qed.

(* ======================== C: 0x81bbc -> 0x41c18 (i = 0 .. 2) ======================== *)
Lemma hw7b_C : forall B, hw7b_C_stmt B.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i R n l x' HJ Hi H9 HR1 HR2 HR3 H18 H26 H20 Hn Hl Hval Hx.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hw7b_wx as Hwx. pose proof hw7b_segs_low as Hsegs.
assert (Ho : 8 * Z.of_nat i = 0 \/ 8 * Z.of_nat i = 8 \/ 8 * Z.of_nat i = 16) by lia.
remember (8 * Z.of_nat i) as o eqn:Hoi. clear Hoi Hi i.
assert (E9 : ew (Ereg regs [Z_to_bv 64 x']) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew (Ereg regs [Z_to_bv 64 x']) 26 = w64 n) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E20 : ew (Ereg regs [Z_to_bv 64 x']) 20 = w64 l) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew (Ereg regs [Z_to_bv 64 x']) 32 = w64 x') by exact (ew_Ereg_extra regs [Z_to_bv 64 x'] 0).
assert (H18' : getr regs 18 = w64 (R + (0x178 + o))) by (rewrite H18; unfold w64; f_equal; lia).
assert (Hval' : val_mem rsegs (mrestrict (w_H W) memc) (R + (0x180 + o)) 8 x')
  by (replace (R + (0x180 + o)) with (R + 0x180 + o) by lia; exact Hval).
pose proof (hw7b_CD_entry W memc regs R n l x' (0x178 + o) (0x180 + o) H9 HR1 HR2 HR3 H18' ltac:(lia) H26 H20 Hn Hl
  ltac:(lia) ltac:(lia) Hval' Hx) as HS.
clear H18 Hval H18' Hval'.
destruct Ho as [-> | [-> | ->]].
all: aj_run_to hw7b_tbl_ok HS HJ HW7B_STRLEN; [awr_ok_tac |
  eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ];
  [ eapply (regs_kept_of_st_ok rsegs _ _ ms regs [Z_to_bv 64 x'] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity]
  | intros a Ha Hz;
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => hw7b_CD_nowr _ _ _ a Hw) a Ha Hz)
  | cbv beta;
    split; [hw7b_reg HS; reflexivity|];
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E32|];
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E32|];
    split; [hw7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 9 R _ E9) by lia; unfold w64; f_equal; lia|];
    hw7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 20 l E20), (U_atom _ 26 n E26) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia ] ].
Qed.

(* ======================== D: 0x81bbc -> 0x51d8c (i = 3) ======================== *)
Lemma hw7b_D : forall B, hw7b_D_stmt B.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R n l t eb HJ H9 HR1 HR2 HR3 H18 H26 H20 Hn Hl H25 Hval Heb.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hw7b_wx as Hwx. pose proof hw7b_segs_low as Hsegs.
assert (E26 : ew (Ereg regs [Z_to_bv 64 eb]) 26 = w64 n) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E25 : ew (Ereg regs [Z_to_bv 64 eb]) 25 = w64 t) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E20 : ew (Ereg regs [Z_to_bv 64 eb]) 20 = w64 l) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew (Ereg regs [Z_to_bv 64 eb]) 32 = w64 eb) by exact (ew_Ereg_extra regs [Z_to_bv 64 eb] 0).
pose proof (hw7b_CD_entry W memc regs R n l eb 0x190 0x118 H9 HR1 HR2 HR3 H18 ltac:(lia) H26 H20 Hn Hl
  ltac:(lia) ltac:(lia) Hval Heb) as HS.
aj_run_to hw7b_tbl_ok HS HJ HW7B_MEMCPY.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [Z_to_bv 64 eb] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => hw7b_CD_nowr _ _ _ a Hw) a Ha Hz).
  + cbv beta.
    split; [hw7b_reg HS; reflexivity|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E32|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E25|].
    split; [hw7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 20 l E20), (U_atom _ 26 n E26) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E32|].
    hw7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 20 l E20), (U_atom _ 26 n E26) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia.
Qed.

(* ======================== E1: 0x81bec -> 0x81c08 ======================== *)
(* the three cells E1 loads, as one read-only region on s1 (atom 9): R+0xe8 (vc, atom 34), R+0x130 (ea, atom 33),
   R+0x138 (vlen, atom 32) *)
Definition hw7b_e1_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xe8 0x140 0xe8 0xe8
[YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 33 0));
 YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))].
Definition ss_E1 : sstate :=
mkSS HW7B_AFTER_TEXT sr_atoms [hw7b_e1_region] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x220) 4); (26%nat, mkAF 0 95 0); (34%nat, mkAF 95 (2 ^ 64 - 1) 0)]
 [] []).
Lemma hw7b_E1_nowr : forall E a, ~ in_wrange E (ss_mem ss_E1) a.
Proof. intros E a (r & [<-|[]] & Hb). cbn [hw7b_e1_region YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.

Lemma hw7b_E1 : forall B, hw7b_E1_stmt B.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R eb n vlen ea vc
  HJ H9 HR1 HR2 HR3 H23 H26 Heb Hn Hsum Vlen Hvlen Vea Hea Vvc Hvc.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hw7b_wx as Hwx. pose proof hw7b_segs_low as Hsegs.
set (ex := [Z_to_bv 64 vlen; Z_to_bv 64 ea; Z_to_bv 64 vc]).
assert (E9 : ew (Ereg regs ex) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew (Ereg regs ex) 23 = w64 eb) by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E26 : ew (Ereg regs ex) 26 = w64 n) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew (Ereg regs ex) 32 = w64 vlen) by exact (ew_Ereg_extra regs ex 0).
assert (E33 : ew (Ereg regs ex) 33 = w64 ea) by exact (ew_Ereg_extra regs ex 1).
assert (E34 : ew (Ereg regs ex) 34 = w64 vc) by exact (ew_Ereg_extra regs ex 2).
assert (HS : st_ok rsegs (Ereg regs ex) ss_E1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HW7B_AFTER_TEXT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_E1. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, hw7b_e1_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs _ _ R 0xe8 8 (SOff 34 0) vc); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vvc].
      rewrite hw7b_den0. exact E34.
    + apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 33 0) ea); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vea].
      rewrite hw7b_den0. exact E33.
    + apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) vlen); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vlen].
      rewrite hw7b_den0. exact E32.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E26, E34. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat split; first [exact HR3 | lia]. }
aj_run_to hw7b_tbl_ok HS HJ HW7B_E2.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => hw7b_E1_nowr _ a Hw) a Ha Hz).
  + cbv beta.
    split; [hw7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 23 eb E23), (U_atom _ 26 n E26) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E32|].
    split; [hw7b_reg HS; rewrite hw7b_den0; exact E33|].
    hw7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 26 n 1 E26) by lia. reflexivity.
Qed.
End b.

Print Assumptions hw7b_B.
Print Assumptions hw7b_C.
Print Assumptions hw7b_D.
Print Assumptions hw7b_E1.
