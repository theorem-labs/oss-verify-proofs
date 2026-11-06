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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 598 of its 650 lines of code are new or changed and 238 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC3h.v at e4c0f4bfc262; ported to
   reac-pw/fuzz_rate's image A: module paths changed; rate's pcs, floats table (0x21140) and registers (the input left
   in s8, the cursor in s9, the input left before the kind byte in a5, the shadow offset in s2, the reloaded shadow
   address in s6); one frame cell [R+0xe8] read instead of role's [R+0xb0] and [R+0xf8]; the post is RtPgSteps.v's
   rts_blk_post and the chaining its rts_blk_seq; AR_laws comes from the kit's AR_laws_ok instead of a Section
   hypothesis; the copy of RtPgSteps' st_ok_pin_sv is dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aC3h.v, with its module paths, addresses and numbers changed; 94 of its 658 lines of code are new or changed and 86 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC3h.v at 876d0cb3d0d; for reac-pw/fuzz_headamp image A: module paths and the rl_ prefix renamed to hd_, every pc moved by +0xd20, the real-frame cells [R+0xb0] / [R+0xf8] moved to [R+0xd0] / [R+0x118] (the plan's slot map); floats at 0x21060 (decimal 135264) and the constant 0xc30c30c30c30c31 at 0x10310 are the same in both images. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the proof of w6_c3h
   (lib/A/HPgW6aBase.v), the head of ent_build's case 3 (pod.h:304-324) in LLVMFuzzerTestOneInput (0x80bc0), from
   0x81c3c to 0x82174 (m odd) or 0x8235c (m even). Proves no function (kind: segment lemma).

   THE CODE (listing of the twin):
     0x81c3c  beqz s9 -> 0x81f64                 no byte left: 0x81f64 a1 := 0, a2 := 0, s4 := [R+0xd0]; j 0x82284
     0x81c40 .. 0x81c50  the shadow check of s8 (NE-SLOW, slow block 0x82710), s4 := [R+0xd0] inside it
     0x81c54  lbu a2,0(s8); a1 := [R+0x118] - 2; a3 := a2 & 1; s8 := a4 + 2; 0x81c68 bnez a3 -> 0x82174 (m odd)
     0x81c6c  a3 := 0xfe; beq a2,a3 -> 0x82278: a2 := 0x7fc00000; j 0x8235c
     0x81c74  a3 := 0xfc; bne a2,a3 -> 0x82280; 0x81c7c a2 := 0x7f800000; j 0x8235c
     0x82280  a2 := a2 >> 1
     0x82284 .. 0x822a8  a0 := 0x21060 + 4 ((a2 - mulhu(a2, [0x10310]) * 21)) = &floats[(m >> 1) % 21]
     0x822ac .. 0x822b8  the shadow check of a0, 4 bytes (NE-SLOW, slow block 0x82774, taken at floats[20])
     0x822bc  lw a2,0(a0); j 0x8235c
   THE BLOCKS. The engine's shadow token needs the checked address in the form (x >> 3) + s7 with x an atom; a
   literal index folds that sum into s7's atom plus a literal, and a symbolic index leaves the run without an address.
   So the head is cut at 0x82284 (m = 0 or m even, not 0xfe / 0xfc) and the table part is two blocks:
     c3_blkT  0x82284 -> 0x822ac   a2 = j (an atom, 0 <= j < 128): a0 = 0x21060 + 4 (j % 21) (base-free image region
                                    over the constant at 0x10310; the value from the code's arithmetic for all 128 j)
     c3_blkL  0x822ac -> 0x8235c   a0 = &floats[idx] as the register's own atom, the entry as a fresh atom in a
                                    4-byte region at a0: the token engine follows the slow block and leaves the
                                    obligation range_addressable a0 4, paid from range_addressable W6_FLOATS 84.
   The head runs over a one-byte region at the cursor s8 (the byte m a fresh atom) and the cells [R+0xd0] and
   [R+0x118] as regions at s1; its three branches on m stop the engine and are split (srr_branch_tok), each arm
   rerun with the branch's condition as a fact. The shadow base is s7 itself (SOff 23 0). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the engine's context ======================================== *)
Definition C3Bx : sv := SOff 23 0.
Definition C3span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition C3_T : Z := 0x82284.   (* the table part: a2 = j *)
Definition C3_L : Z := 0x822ac.   (* the table entry's check: a0 = &floats[idx] *)

(* ======================================== arithmetic and image facts ======================================== *)
Lemma c3_all : forall (n : Z) (f g : Z -> Z),
forallb (fun j => f j =? g j) (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall j, 0 <= j < n -> f j = g j.
Proof.
intros n f g H j Hj. rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia].
Qed.
Lemma c3_float_range : forall idx, 0 <= idx < 21 -> 0 <= nth (Z.to_nat idx) Tables.float_bits 0 < 2 ^ 32.
Proof.
intros idx Hidx.
assert (H1 : forall j, 0 <= j < 21 -> (fun j => if (0 <=? nth (Z.to_nat j) Tables.float_bits 0) &&
  (nth (Z.to_nat j) Tables.float_bits 0 <? 2 ^ 32) then 1 else 0) j = (fun _ => 1) j)
  by (apply (c3_all 21); vm_compute; reflexivity).
specialize (H1 idx Hidx). cbv beta in H1.
destruct (0 <=? nth (Z.to_nat idx) Tables.float_bits 0) eqn:A; [|discriminate H1].
destruct (nth (Z.to_nat idx) Tables.float_bits 0 <? 2 ^ 32) eqn:B'; [|discriminate H1].
apply Z.leb_le in A. apply Z.ltb_lt in B'. lia.
Qed.
(* the image's bytes of floats[idx] (.rodata 0x21060 + 4 idx) *)
Definition c3_fbyte_ok (idx : Z) (k : nat) : bool :=
let a := W6_FLOATS + 4 * idx + Z.of_nat k in
in_rom_b a && YP08.img_byte_ok rsegs a &&
match img_byte rsegs a with
| Some b => bv_unsigned b =? bv_unsigned (Z_to_bv 8 (le_byte (nth (Z.to_nat idx) Tables.float_bits 0) 4 k))
| None => false
end.
Lemma c3_fbytes : forall idx, 0 <= idx < 21 -> forall k, (k < 4)%nat -> c3_fbyte_ok idx k = true.
Proof.
intros idx Hidx k Hk.
assert (H1 : forall j, 0 <= j < 21 -> (fun j => if forallb (c3_fbyte_ok j) (seq 0 4) then 1 else 0) j = (fun _ => 1) j)
  by (apply (c3_all 21); vm_compute; reflexivity).
specialize (H1 idx Hidx). cbv beta in H1.
destruct (forallb (c3_fbyte_ok idx) (seq 0 4)) eqn:A; [|discriminate H1].
rewrite forallb_forall in A. apply A. apply in_seq. lia.
Qed.
(* (m >> 1) % 21 as 0x82284 .. 0x822a8 compute it, the engine's form of a0 at 0x822ac *)
Definition c3_a0T : sv :=
SAlu ALU_ADD (SLit 135264) (SAlu ALU_SLL (SAlu ALU_SUB (SOff 12 0)
  (SMd M_MUL (SMd M_MULHU (SOff 12 0) (SLit 878416384462359601)) (SLit 21))) (SLit 2)).
Lemma c3_a0T_val : forall E j, ew E 12 = Z_to_bv 64 j -> 0 <= j < 128 -> U E c3_a0T = W6_FLOATS + 4 * (j mod 21).
Proof.
intros E j H12 Hj. unfold c3_a0T. rewrite !U_SAlu, !U_SMd, !U_SLit, (U_atom E 12 j H12) by lia.
clear H12. revert j Hj. apply (c3_all 128). vm_compute. reflexivity.
Qed.

Lemma c3_allb : forall (n : Z) (f g : Z -> bool),
forallb (fun j => Bool.eqb (f j) (g j)) (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall j, 0 <= j < n -> f j = g j.
Proof.
intros n f g H j Hj. rewrite forallb_forall in H. apply Bool.eqb_prop. apply H.
apply in_map_iff. exists (Z.to_nat j). split; [lia | apply in_seq; lia].
Qed.
(* case 3's value on the table path (m even, not 0xfe / 0xfc), on m = 0xfe / 0xfc, and with no byte (m = 0) *)
Lemma c3_fe_tbl : forall m, 0 <= m < 256 -> Z.odd m = false -> m <> 254 -> m <> 252 ->
w6_float_even m = nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.
Proof.
intros m Hm Ho H1 H2.
pose proof (c3_all 256 (fun m => if negb (Z.odd m) && negb (m =? 254) && negb (m =? 252) then w6_float_even m
  else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0) (fun m => nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0)
  ltac:(vm_compute; reflexivity) m Hm) as A.
cbv beta in A. rewrite Ho, (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2) in A. exact A.
Qed.
Lemma c3_fe_254 : w6_float_even 254 = 0x7fc00000.
Proof. vm_compute. reflexivity. Qed.
Lemma c3_fe_252 : w6_float_even 252 = 0x7f800000.
Proof. vm_compute. reflexivity. Qed.
Lemma c3_fe_0 : w6_float_even 0 = nth (Z.to_nat (0 mod 21)) Tables.float_bits 0.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== engine helpers ======================================== *)
Section gen. Context {fx : YK11.FPState}.
Variable segs : list Segment.
(* a register pinned to any sv whose value it holds [HPgSteps st_ok_pin_lit] *)
Lemma c3_pin_sv : forall E ss ms (r : bv 5) e,
st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 Hr.
apply (st_ok_regs segs E ss ms (sr_set (ss_regs ss) r e) HS).
intros rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End gen.
Lemma c3_agree_ewset : forall k E n v, (k <= n)%nat -> env_agree k E (ewset E n v).
Proof. intros k E n v Hk. split; [intros i Hi; apply ew_ewset_other; lia | reflexivity]. Qed.
Lemma c3_agree_trans : forall k E1 E2 E3, env_agree k E1 E2 -> env_agree k E2 E3 -> env_agree k E1 E3.
Proof. intros k E1 E2 E3 [A1 D1] [A2 D2]. split; [intros n Hn; rewrite A2 by lia; apply A1; lia | congruence]. Qed.
Lemma c3_agree_le : forall k k' E E', (k <= k')%nat -> env_agree k' E E' -> env_agree k E E'.
Proof. intros k k' E E' Hk [A D]. split; [intros n Hn; apply A; lia | exact D]. Qed.
(* the token atoms of a run sit at K and above: the env agrees with the run's start below K *)
Ltac c3_agree :=
lazymatch goal with
| |- env_agree ?k ?E (ewset ?X ?n ?v) =>
  apply (c3_agree_trans k E X (ewset X n v)); [c3_agree | apply c3_agree_ewset; lia]
| |- env_agree ?k ?E ?E1 => split; [intros; reflexivity | reflexivity]
end.
(* the lowest token atom of an env made by a run (dflt if the run made none) *)
Ltac c3_kof E1 dflt :=
lazymatch E1 with
| ewset ?X ?n _ => lazymatch X with ewset _ _ _ => c3_kof X dflt | _ => n end
| _ => dflt
end.
Lemma c3_den : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = w64 v.
Proof. intros E e v H Hv. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia. exact H. Qed.
Lemma c3_sext32_mod : forall fv, 0 <= fv < 2 ^ 32 -> zcanon (bv_swrap 32 fv) mod 2 ^ 32 = fv.
Proof.
intros fv Hfv. unfold zcanon, M64.
rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2 ^ 32); reflexivity].
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. replace (fv + 2 ^ 31 - 2 ^ 31) with fv by lia. apply Z.mod_small. lia.
Qed.
Lemma c3_bt_eq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by assumption. reflexivity. Qed.
Lemma c3_bt_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by assumption. reflexivity. Qed.
Lemma c3_U_lt : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. pose proof (U_range E e) as H. unfold M64 in H. exact H. Qed.
(* the three branches on the byte m (atom 32) *)
Lemma c3_par : forall E m, ew E 32 = Z_to_bv 64 m -> 0 <= m < 256 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 1))) (sv_denot E (SLit 0)) = Z.odd m.
Proof.
intros E m H Hm. rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SLit 0)), c3_bt_ne by apply c3_U_lt.
rewrite U_SAlu, !U_SLit, (U_atom E 32 m H) by lia. clear H. revert m Hm.
apply (c3_allb 256). vm_compute. reflexivity.
Qed.
Lemma c3_bt_lit : forall E m k, ew E 32 = Z_to_bv 64 m -> 0 <= m < 256 -> 0 <= k < 256 ->
branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SLit k)) = (m =? k) /\
branch_taken BC_NE (sv_denot E (SOff 32 0)) (sv_denot E (SLit k)) = negb (m =? k).
Proof.
intros E m k H Hm Hk. rewrite (denot_lit_U E (SOff 32 0)), (denot_lit_U E (SLit k)).
rewrite c3_bt_eq, c3_bt_ne by apply c3_U_lt. rewrite U_SLit, (U_atom E 32 m H) by lia.
rewrite (zcanon_id k) by (unfold M64; lia). split; reflexivity.
Qed.
Lemma c3_srl1 : forall E m, ew E 32 = Z_to_bv 64 m -> 0 <= m < 256 -> U E (SAlu ALU_SRL (SOff 32 0) (SLit 1)) = m / 2.
Proof.
intros E m H Hm. rewrite U_SAlu, U_SLit, (U_atom E 32 m H) by lia. clear H. revert m Hm.
apply (c3_all 256). vm_compute. reflexivity.
Qed.
Lemma c3_if_true : forall W c (P Q : world rsegs -> config -> Prop) (bb : bool),
bb = true -> SRr rsegs W c P -> SRr rsegs W c (fun W2 c2 => if bb then P W2 c2 else Q W2 c2).
Proof. intros W c P Q bb -> H. eapply SRr_mono; [exact H | intros W2 c2 _ HP; exact HP]. Qed.
Lemma c3_if_false : forall W c (P Q : world rsegs -> config -> Prop) (bb : bool),
bb = false -> SRr rsegs W c Q -> SRr rsegs W c (fun W2 c2 => if bb then P W2 c2 else Q W2 c2).
Proof. intros W c P Q bb -> H. eapply SRr_mono; [exact H | intros W2 c2 _ HP; exact HP]. Qed.
(* a run over regions without write windows keeps every byte *)
Lemma c3_kept : forall E rs (H : word -> bool) (m1 m2 : word -> option byte),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 HF Hw a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). rewrite forallb_forall in Hw. specialize (Hw r Hin). apply Z.leb_le in Hw. lia.
Qed.
Lemma c3_rom_kept : forall (W W1 : world rsegs) m m1, rom_view rsegs W m ->
(forall a, aview rsegs (w_H W1) m1 a = aview rsegs (w_H W) m a) -> rom_view rsegs W1 m1.
Proof. intros W W1 m m1 HR K a Ha. rewrite K. exact (HR a Ha). Qed.
Lemma c3_ra_kept : forall (rd1 rd2 : reader) a n,
range_addressable rd1 SHADOW_OFF a n -> (forall x, rd2 x = rd1 x) -> range_addressable rd2 SHADOW_OFF a n.
Proof. intros rd1 rd2 a n H K x Hx. rewrite K. exact (H x Hx). Qed.
(* side conditions on register names *)
Ltac c3_nz := let X := fresh "X" in intros X; cbv in X; discriminate X.
Ltac c3_notin :=
let X := fresh "X" in intros X; cbn [app In] in X;
repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; cbv in X; discriminate X|]); exact X.

(* the value of floats[idx] in memory, from rom_view *)
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c3_floats_val : forall (W : world rsegs) memc idx, rom_view rsegs W memc -> 0 <= idx < 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (W6_FLOATS + 4 * idx) 4 (nth (Z.to_nat idx) Tables.float_bits 0).
Proof.
intros W memc idx HR Hidx k Hk.
pose proof (c3_fbytes idx Hidx k Hk) as Hb. unfold c3_fbyte_ok in Hb.
apply andb_prop in Hb as [Hb Hv]. apply andb_prop in Hb as [Hr Hi].
destruct (mbyte_rom W memc _ HR Hr Hi) as (b & Eb & Mb). rewrite Eb in Hv. apply Z.eqb_eq in Hv.
rewrite Mb. f_equal. apply bv_eq. exact Hv.
Qed.
End b0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the engine's last state at a block's end pc gives hd_blk_post *)
Lemma c3_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob (Rr : bvmap 5 word -> Prop)
E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rr (ms_regs ms) ->
SRr rsegs W (mkCfg ms md) (hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr E ss ms md HS Hrv Hpc HJ Hio Hregs Hkept HR.
apply SRr_ret. exists lyc, Sc, (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hregs|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split; [exact Hio|]. split; [apply mo_le_refl; exact MTL|]. split; [exact Hkept | exact HR].
Qed.
(* a block run from an intermediate state, read back against the block's start *)
Lemma c3_then : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc clob1 clob2 clob
(R1 R2 : bvmap 5 word -> Prop) regs1 mem1 md1,
same_io mdc md1 ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
(forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
(forall r, In r clob1 -> In r clob) -> (forall r, In r clob2 -> In r clob) ->
(forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob2 -> getr regs2 r = getr regs1 r) -> R1 regs2 -> R2 regs2) ->
SRr rsegs W (cfg_at rsegs pc0 regs1 mem1 md1)
  (hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 lyc Sc W mem1 md1 pc clob2 R1) ->
SRr rsegs W (cfg_at rsegs pc0 regs1 mem1 md1)
  (hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc clob1 clob2 clob R1 R2 regs1 mem1 md1
Hio1 Hr1 Hk1 Hc1 Hc2 HRR H.
eapply SRr_mono; [exact H|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr r Hr0 ltac:(intros X; apply Hn; apply Hc2; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply Hc1; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [eapply same_io_trans; [exact Hio1 | exact Hio]|].
split; [exact Hmo|]. split; [intros a; rewrite (Hm a); apply Hk1|].
exact (HRR regs2 Hr HR).
Qed.

(* ===================== c3_blkL: 0x822ac .. 0x8235c, the check of &floats[idx] and its load ===================== *)
Definition c3_fl : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition c3_GL : facts :=
mkFacts [(10%nat, mkAF W6_FLOATS (W6_FLOATS + 80) 2); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition c3_ssL : sstate := mkSS C3_L sr_atoms [c3_fl] None c3_GL.
Definition c3_RL (idx : Z) (regs2 : bvmap 5 word) : Prop :=
exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat idx) Tables.float_bits 0.
Lemma c3_blkL : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (idx : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= idx < 21 ->
getr regs 10 = w64 (W6_FLOATS + 4 * idx) -> getr regs 23 = w64 SHADOW_OFF ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs C3_L regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc W6_T3 [12; 13]%bv (c3_RL idx)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs idx HJ HR Hidx H10 H23 Hra.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
set (fv := nth (Z.to_nat idx) Tables.float_bits 0).
assert (Hfv : 0 <= fv < 2 ^ 32) by (apply c3_float_range; exact Hidx).
pose proof (c3_floats_val W memc idx HR Hidx) as Hval. fold fv in Hval.
set (E := Ereg regs [w64 fv]).
assert (E10 : ew E 10 = Z_to_bv 64 (W6_FLOATS + 4 * idx)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 fv) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok rsegs E c3_ssL (restrict (w_H W) (mkst regs (Z_to_bv 64 C3_L) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs [w64 fv]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, c3_fl. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by (unfold W6_FLOATS; lia).
    split; [unfold W6_FLOATS; lia|]. split; [unfold W6_FLOATS; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ _ 0 4 (SOff 32 0) fv).
    + apply c3_den; [apply (U_atom E 32 fv E32); lia | lia].
    + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact Hval.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [c3_GL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10, E23, !unsigned_lit_small by (unfold W6_FLOATS, SHADOW_OFF; lia).
    change (2 ^ 2) with 4. change (2 ^ 0) with 1. unfold W6_FLOATS, SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r.
    replace (135264 + 4 * idx) with ((33816 + idx) * 4) by lia. apply Z.mod_mul. lia. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HB : U E C3Bx = SHADOW_OFF) by (apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
assert (HA0 : U E (SOff 10 0) = W6_FLOATS + 4 * idx) by (apply (U_atom E 10 _ E10); unfold W6_FLOATS; lia).
unfold cfg_at. change (w64 C3_L) with (Z_to_bv 64 C3_L).
aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_T3.
- cbn [ms_mem mkst]. rewrite HA0.
  apply (obl_of_range rsegs (w_H W) memc E C3Bx (W6_FLOATS + 4 * idx) 4 W6_FLOATS 84 Hra HB); lia.
- awr_ok_tac.
- assert (HAE : env_agree 32 (Ereg regs [w64 fv]) E) by (subst E; split; [intros; reflexivity | reflexivity]).
  lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA1 : env_agree 33 E E1) by c3_agree end.
  eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | apply same_io_wvb | | |].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [w64 fv] (w_H W) _ HS);
      [exact (c3_agree_trans 32 _ _ _ HAE (c3_agree_le 32 33 _ _ ltac:(lia) HA1)) | vm_compute; reflexivity].
  + exact (c3_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
  + unfold c3_RL. rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e end.
    lazymatch type of HS with st_ok _ ?E1 _ _ =>
      exists (U E1 (SExt true 32 (SOff 32 0))) end.
    split; [rewrite <- denot_lit_U; reflexivity|].
    rewrite U_SExt. cbv iota.
    destruct HA1 as [HA1 _]. rewrite (U_atom _ 32 fv) by (try rewrite HA1 by lia; first [exact E32 | lia]).
    change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small fv) by lia. apply c3_sext32_mod. exact Hfv.
Qed.

(* ===================== c3_blkT: 0x82284 .. 0x822ac, &floats[j % 21] ===================== *)
Definition c3_k21 : YP09.region := YP09.mkRegion None 0x10310 (0x10310 + 8) 0 0 [YP09.mkChunk 0x10310 (CImg 8)].
Definition c3_GT : facts := mkFacts [(12%nat, mkAF 0 127 0)] [] [].
Definition c3_ssT : sstate := mkSS C3_T sr_atoms [c3_k21] None c3_GT.
Definition c3_RT (j : Z) (regs2 : bvmap 5 word) : Prop := getr regs2 10 = w64 (W6_FLOATS + 4 * (j mod 21)).
Lemma c3_k21_rom : rom_run_b 0x10310 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c3_blkT : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (j : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= j < 128 -> getr regs 12 = w64 j ->
SRr rsegs W (cfg_at rsegs C3_T regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc C3_L [10; 12; 13]%bv (c3_RT j)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs j HJ HR Hj H12.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
set (E := Ereg regs []).
assert (E12 : ew E 12 = Z_to_bv 64 j) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (HS : st_ok rsegs E c3_ssT (restrict (w_H W) (mkst regs (Z_to_bv 64 C3_T) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact c3_k21_rom].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [c3_GT f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 C3_T) with (Z_to_bv 64 C3_T).
aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span C3_L.
- awr_ok_tac.
- assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros; reflexivity | reflexivity]).
  eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | apply same_io_wvb | | |].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS HAE). vm_compute. reflexivity.
  + exact (c3_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
  + unfold c3_RT. rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e end.
    change (SAlu ALU_ADD (SLit 135264) _) with c3_a0T.
    apply c3_den; [apply (c3_a0T_val E j E12 Hj) | pose proof (Z.mod_pos_bound j 21 ltac:(lia)); unfold W6_FLOATS; lia].
Qed.

(* ===================== c3_blkTL: 0x82284 .. 0x8235c ===================== *)
Definition c3_RTL (j : Z) (regs2 : bvmap 5 word) : Prop :=
exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat (j mod 21)) Tables.float_bits 0.
Lemma c3_blkTL : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (j : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
rom_view rsegs W memc -> 0 <= j < 128 -> getr regs 12 = w64 j -> getr regs 23 = w64 SHADOW_OFF ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs C3_T regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc W6_T3 ([10; 12; 13] ++ [12; 13])%bv (c3_RTL j)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs j HJ HR Hj H12 H23 Hra.
eapply (w6_blk_seq B MT MTL); [exact (c3_blkT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs j HJ HR Hj H12)|].
intros W1 ly1 S1 regs1 mem1 md1 Hw HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1.
pose proof (Z.mod_pos_bound j 21 ltac:(lia)) as Hjm.
exact (c3_blkL STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k0 regs1 (j mod 21) HJ1
  (c3_rom_kept W W1 memc mem1 HR Hm1) Hjm HR1
  (eq_trans (Hr1 23%bv ltac:(c3_nz) ltac:(c3_notin)) H23)
  (c3_ra_kept _ _ W6_FLOATS 84 Hra Hm1)).
Qed.

(* ===================== the head: 0x81c3c .. 0x82174 / 0x8235c / 0x82284 ===================== *)
Definition C3_CLOB : list (bv 5) := [10; 11; 12; 13; 20; 24]%bv.
(* a table-path leaf: from 0x82284 with a2 = j the two table blocks end the case at 0x8235c *)
Lemma c3_to_tbl : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (Rr : bvmap 5 word -> Prop) E ss ms md j,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = C3_T ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r C3_CLOB -> getr (ms_regs ms) r = getr regs r) ->
(forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
rom_view rsegs W memc -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_FLOATS 84 ->
0 <= j < 128 -> getr (ms_regs ms) 12 = w64 j -> getr regs 23 = w64 SHADOW_OFF ->
(forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r ([10; 12; 13] ++ [12; 13])%bv -> getr regs2 r = getr (ms_regs ms) r) ->
  c3_RTL j regs2 -> Rr regs2) ->
SRr rsegs W (mkCfg ms md) (hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_T3 C3_CLOB Rr).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc Rr E ss ms md j HS Hrv Hpc HJ Hio Hregs Hkept HR Hra
Hj H12 H23 HRR.
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 C3_T) (ms_mem ms) (seg_rom rsegs))
  by (rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv)).
rewrite Ems at 1.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 C3_T) (ms_mem ms) (seg_rom rsegs)) md)
  with (cfg_at rsegs C3_T (ms_regs ms) (ms_mem ms) md).
apply (c3_then STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C3_T W6_T3 C3_CLOB ([10; 12; 13] ++ [12; 13])%bv
  C3_CLOB (c3_RTL j) Rr (ms_regs ms) (ms_mem ms) md Hio Hregs Hkept (fun r H => H)); [|exact HRR|].
- intros r Hr. cbn [app In] in Hr. unfold C3_CLOB. cbn [In]. tauto.
- exact (c3_blkTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k (ms_regs ms) j HJ
    (c3_rom_kept W W memc (ms_mem ms) HR Hkept) Hj H12
    (eq_trans (Hregs 23%bv ltac:(c3_nz) ltac:(unfold C3_CLOB; c3_notin)) H23) (c3_ra_kept _ _ _ _ Hra Hkept)).
Qed.

Definition c3_vb : YP09.region := YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0 0 [YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0))].
Definition c3_n : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x120 0 0 [YP09.mkChunk 0x118 (CVal 8 (SOff 34 0))].
Definition c3_in : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition c3_G1 : facts := mkFacts [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, mkAF 2 (2 ^ 47 - 2) 0);
  (25%nat, mkAF 1 (2 ^ 47) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition c3_ss1 : sstate := mkSS W6_D3 sr_atoms [c3_vb; c3_n; c3_in] None c3_G1.
Definition c3_G0 : facts :=
mkFacts [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 0 0 0)] [mkAC BC_EQ (SOff 25 0) (SLit 0)] [].
Definition c3_ss0 : sstate := mkSS W6_D3 sr_atoms [c3_vb] None c3_G0.
Definition c3_extra (m vb n : Z) : list word := [w64 m; w64 vb; w64 n].

Ltac c3_kio := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* after a run: fold the run's frame into KE (every byte kept since the block's start) *)
Ltac c3_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, aview _ _ _ a = aview _ _ _ a |- _ =>
  let KS := fresh "KS" in
  pose proof (fun a => eq_trans (c3_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a) (KE a)) as KS;
  clear KE; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the symbolic value of register r in the run's last state *)
Ltac c3_regs HS :=
rewrite !(st_ok_restrict_reg rsegs (w_H _) _ _ _ _ HS);
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  repeat match goal with |- context [sr_get (ss_regs ssf) ?r] =>
    let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end end.
Ltac c3_ew HA1 H := first [exact H | rewrite (proj1 HA1) by lia; exact H].
Ltac c3_side HA H := first [c3_ew HA H | lia].
Ltac c3_rk HS HAE :=
eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H _) _ HS);
[ eapply c3_agree_trans; [exact HAE | c3_agree] | vm_compute; reflexivity ].
Ltac c3_rkept HS HAE HA1 :=
eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H _) _ HS);
[ eapply c3_agree_trans; [exact HAE | eapply c3_agree_le; [| exact HA1]; lia]
| vm_compute; reflexivity ].

(* no byte left: s9 = 0, 0x81f64 a1 := 0, a2 := 0, s4 := vb, to 0x82284, then floats[0] *)
Lemma c3_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z),
w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6_head_in W memc regs R c vb [] ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs W6_D3 regs memc mdc)
(fun W2 c2 => if Z.odd 0 then
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_U3 C3_CLOB
  (fun regs2 => getr regs2 11 = w64 (Z.of_nat (length (@nil byte))) /\ getr regs2 12 = w64 0 /\
     getr regs2 24 = w64 (c + 1) /\ getr regs2 20 = w64 vb) W2 c2
 else
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_T3 C3_CLOB
  (fun regs2 => (exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = w6_float_even 0 mod 2 ^ 32) /\
     getr regs2 11 = w64 (Z.of_nat (length (@nil byte))) /\
     getr regs2 24 = w64 (c + Z.of_nat (length (@nil byte) - length (@nil byte))) /\ getr regs2 20 = w64 vb) W2 c2).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb
(HJ & HR16 & HRsp & HRstk & Hown & HF & HR) (H9 & H23 & H24 & H25 & H14 & Hn & Hvb & Hvb64 & Hc1 & Hin) Hra.
eapply c3_if_false; [reflexivity|].
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in HRstk.
set (E := Ereg regs (c3_extra 0 vb 1)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E33 : ew E 33 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 1)).
destruct Hin as (_ & _ & Hc0 & Hchi & Hamem & _). cbn [length] in Hchi.
assert (HS : st_ok rsegs E c3_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_D3) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs (c3_extra 0 vb 1)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, c3_vb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ _ 0xd0 8 (SOff 33 0) vb).
    + apply c3_den; [apply (U_atom E 33 vb E33); lia | lia].
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + exact Hvb.
  - cbn. tauto.
  - split; [|split; [|exact I]].
    + cbn [c3_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E25, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. unfold SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r.
    + cbn [c3_G0 f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (denot_lit_U E (SOff 25 0)), (denot_lit_U E (SLit 0)), c3_bt_eq by apply c3_U_lt.
      rewrite U_SLit, (U_atom E 25 0 E25) by lia. reflexivity. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (c3_extra 0 vb 1)) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 W6_D3) with (Z_to_bv 64 W6_D3).
aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span C3_T.
- awr_ok_tac.
- c3_keep.
  lazymatch type of HS with st_ok _ ?E1 _ _ => let kk := c3_kof E1 33%nat in assert (HA1 : env_agree kk E E1) by c3_agree end.
  eapply c3_to_tbl with (j := 0);
    [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rkept HS HAE HA1 | exact KE | exact HR
    | exact Hra | lia | | exact H23 |].
  + c3_regs HS. reflexivity.
  + intros regs2 Hk (v & Hv12 & Hvm).
    rewrite (Hk 11%bv ltac:(c3_nz) ltac:(c3_notin)), (Hk 20%bv ltac:(c3_nz) ltac:(c3_notin)),
      (Hk 24%bv ltac:(c3_nz) ltac:(c3_notin)).
    c3_regs HS. cbn [length]. replace (c + Z.of_nat (0 - 0)) with c by lia.
    split; [exists v; split; [exact Hv12 | rewrite Hvm; vm_compute; reflexivity]|].
    split; [reflexivity|]. split.
    * apply c3_den; [|lia]. apply (U_atom _ 24 c); [c3_ew HA1 E24 | lia].
    * apply c3_den; [|lia]. apply (U_atom _ 33 vb); [c3_ew HA1 E33 | lia].
Qed.

(* a byte left: the check of s8, m = lbu, the three branches on m *)
Lemma c3_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z)
(bb : byte) (r' : list byte),
w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6_head_in W memc regs R c vb (bb :: r') ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_FLOATS 84 ->
SRr rsegs W (cfg_at rsegs W6_D3 regs memc mdc)
(fun W2 c2 => if Z.odd (bv_unsigned bb) then
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_U3 C3_CLOB
  (fun regs2 => getr regs2 11 = w64 (Z.of_nat (length r')) /\ getr regs2 12 = w64 (bv_unsigned bb) /\
     getr regs2 24 = w64 (c + 1) /\ getr regs2 20 = w64 vb) W2 c2
 else
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_T3 C3_CLOB
  (fun regs2 => (exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = w6_float_even (bv_unsigned bb) mod 2 ^ 32) /\
     getr regs2 11 = w64 (Z.of_nat (length r')) /\
     getr regs2 24 = w64 (c + Z.of_nat (length (bb :: r') - length r')) /\ getr regs2 20 = w64 vb) W2 c2).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb bb r'
(HJ & HR16 & HRsp & HRstk & Hown & HF & HR) (H9 & H23 & H24 & H25 & H14 & Hn & Hvb & Hvb64 & Hc1 & Hin) Hra.
assert (Hm : 0 <= bv_unsigned bb < 256) by apply Cursor.byte_range.
assert (Hj2 : 0 <= bv_unsigned bb / 2 < 128)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hjm : 0 <= (bv_unsigned bb / 2) mod 21 < 21) by (apply Z.mod_pos_bound; lia).
assert (Hlen : Z.of_nat (length (bb :: r')) = Z.of_nat (length r') + 1) by (cbn [length]; lia).
destruct Hin as (Hg & Hrin & Hc0 & Hchi & Hamem & Hdisj).
rewrite Hlen in H25, Hn, Hrin, Hchi, Hamem, Hdisj.
replace (Z.of_nat (length r') + 1 + 1) with (Z.of_nat (length r') + 2) in Hn by lia.
assert (Hnl0 : 0 <= Z.of_nat (length r')) by lia.
set (m := bv_unsigned bb) in *. set (nl := Z.of_nat (length r')) in *.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in HRstk.
assert (Hbnd : c + (nl + 1) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem; lia).
assert (Hmv : val_mem rsegs (mrestrict (w_H W) memc) c 1 m).
{ destruct (Hg 0%nat ltac:(rewrite length_map; cbn [length]; lia)) as [Hv _].
  rewrite Z.add_0_r in Hv. cbn [map nth] in Hv. exact Hv. }
pose proof (Hdisj c ltac:(lia)) as Hdc. unfold T_SEG_STK, ASTACK in Hdc.
set (E := Ereg regs (c3_extra m vb (nl + 2))).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E14 : ew E 14 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 (nl + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nl + 2)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs E c3_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_D3) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs). all: change (Ereg regs (c3_extra m vb (nl + 2))) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok, c3_vb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0xd0 8 (SOff 33 0) vb);
        [apply c3_den; [apply (U_atom E 33 vb E33); lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvb].
    + unfold region_ok, c3_n. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0x118 8 (SOff 34 0) (nl + 2));
        [apply c3_den; [apply (U_atom E 34 (nl + 2) E34); lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia | exact Hn].
    + unfold region_ok, c3_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E24, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ _ 0 1 (SOff 32 0) m);
        [apply c3_den; [apply (U_atom E 32 m E32); lia | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia
        | rewrite Z.add_0_r; exact Hmv].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c3_vb, c3_n, c3_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E24, !unsigned_lit_small by lia.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]]. cbn [c3_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E23, E24, E25, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. unfold SHADOW_OFF. repeat split; try lia; try apply Z.mod_1_r. }
assert (SHOK : sh_ok rsegs C3Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HB : U E C3Bx = SHADOW_OFF) by (apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
assert (HAE : env_agree 32 (Ereg regs (c3_extra m vb (nl + 2))) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 W6_D3) with (Z_to_bv 64 W6_D3).
aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_U3.
- cbn [ms_mem mkst]. rewrite (U_atom E 24 c E24) by lia.
  apply (obl_of_range rsegs (w_H W) memc E C3Bx c 1 c (nl + 1) Hrin HB); lia.
- awr_ok_tac.
- (* stuck at 0x81c68: m odd? *)
  c3_keep.
  lazymatch type of HS with st_ok _ ?E1 _ _ =>
    assert (HA : env_agree 35 E E1) by c3_agree;
    assert (F32 : ew E1 32 = Z_to_bv 64 m) by (c3_ew HA E32) end.
  srr_branch_tok w6_tbl_ok HS SHOK C3span.
  + (* m odd: stop at 0x82174 *)
    lazymatch type of HS with st_ok _ ?E1 _ _ => rewrite (c3_par E1 m F32 Hm) in Hc end.
    eapply c3_if_true; [exact Hc|].
    aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_U3.
    * awr_ok_tac.
    * c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 35 E E1) by c3_agree end.
      eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
      c3_regs HS. split; [|split; [|split]].
      -- apply c3_den; [rewrite (U_atom_off _ 34 (nl + 2) (-2)) by c3_side HA E34; lia | lia].
      -- apply c3_den; [apply (U_atom _ 32 m); [c3_ew HA E32 | lia] | lia].
      -- apply c3_den; [rewrite (U_atom_off _ 14 (c - 1) 2) by c3_side HA E14; lia | lia].
      -- apply c3_den; [apply (U_atom _ 33 vb); [c3_ew HA E33 | lia] | lia].
  + (* m even *)
    lazymatch type of HS with st_ok _ ?E1 _ _ => rewrite (c3_par E1 m F32 Hm) in Hc end.
    eapply c3_if_false; [exact Hc|]. rename Hc into Hodd.
    aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_T3; [awr_ok_tac|]. c3_keep.
    srr_branch_tok w6_tbl_ok HS SHOK C3span.
    * (* m = 0xfe *)
      lazymatch type of HS with st_ok _ ?E1 _ _ =>
        rewrite (proj1 (c3_bt_lit E1 m 254 F32 Hm ltac:(lia))) in Hc end.
      apply Z.eqb_eq in Hc.
      aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_T3.
      -- awr_ok_tac.
      -- c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 35 E E1) by c3_agree end.
         eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
         c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
         split; [|split; [|split]].
         ++ exists 2143289344. split; [reflexivity|]. rewrite Hc. vm_compute. reflexivity.
         ++ apply c3_den; [rewrite (U_atom_off _ 34 (nl + 2) (-2)) by c3_side HA E34; lia | lia].
         ++ apply c3_den; [rewrite (U_atom_off _ 14 (c - 1) 2) by c3_side HA E14; lia | lia].
         ++ apply c3_den; [apply (U_atom _ 33 vb); [c3_ew HA E33 | lia] | lia].
    * (* m <> 0xfe *)
      lazymatch type of HS with st_ok _ ?E1 _ _ =>
        rewrite (proj1 (c3_bt_lit E1 m 254 F32 Hm ltac:(lia))) in Hc end.
      apply Z.eqb_neq in Hc. rename Hc into H254.
      aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_T3; [awr_ok_tac|]. c3_keep.
      srr_branch_tok w6_tbl_ok HS SHOK C3span.
      -- (* m <> 0xfc: the table *)
         lazymatch type of HS with st_ok _ ?E1 _ _ =>
           rewrite (proj2 (c3_bt_lit E1 m 252 F32 Hm ltac:(lia))) in Hc end.
         apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. rename Hc into H252.
         aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span C3_T.
         ++ awr_ok_tac.
         ++ c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 35 E E1) by c3_agree end.
            eapply c3_to_tbl with (j := m / 2);
              [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE | exact HR
              | exact Hra | | | exact H23 |].
            ** exact Hj2.
            ** c3_regs HS. apply c3_den; [apply (c3_srl1 _ m); [c3_ew HA E32 | lia] | lia].
            ** intros regs2 Hk (v & Hv12 & Hvm).
               rewrite (Hk 11%bv ltac:(c3_nz) ltac:(c3_notin)), (Hk 20%bv ltac:(c3_nz) ltac:(c3_notin)),
                 (Hk 24%bv ltac:(c3_nz) ltac:(c3_notin)).
               c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
               split; [|split; [|split]].
               --- exists v. split; [exact Hv12|]. rewrite Hvm, (c3_fe_tbl m Hm Hodd H254 H252).
                   symmetry. apply Z.mod_small. apply c3_float_range. exact Hjm.
               --- apply c3_den; [rewrite (U_atom_off _ 34 (nl + 2) (-2)) by c3_side HA E34; lia | lia].
               --- apply c3_den; [rewrite (U_atom_off _ 14 (c - 1) 2) by c3_side HA E14; lia | lia].
               --- apply c3_den; [apply (U_atom _ 33 vb); [c3_ew HA E33 | lia] | lia].
      -- (* m = 0xfc *)
         lazymatch type of HS with st_ok _ ?E1 _ _ =>
           rewrite (proj2 (c3_bt_lit E1 m 252 F32 Hm ltac:(lia))) in Hc end.
         apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
         aj_run_to_tok w6_tbl_ok HS HJ SHOK C3span W6_T3.
         ++ awr_ok_tac.
         ++ c3_keep. clear HA. lazymatch type of HS with st_ok _ ?E1 _ _ => assert (HA : env_agree 35 E E1) by c3_agree end.
            eapply c3_leaf; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | c3_kio | c3_rk HS HAE | exact KE |].
            c3_regs HS. replace (Z.of_nat (length (bb :: r') - length r')) with 1 by (cbn [length]; lia).
            split; [|split; [|split]].
            ** exists 2139095040. split; [reflexivity|]. rewrite Hc. vm_compute. reflexivity.
            ** apply c3_den; [rewrite (U_atom_off _ 34 (nl + 2) (-2)) by c3_side HA E34; lia | lia].
            ** apply c3_den; [rewrite (U_atom_off _ 14 (c - 1) 2) by c3_side HA E14; lia | lia].
            ** apply c3_den; [apply (U_atom _ 33 vb); [c3_ew HA E33 | lia] | lia].
Qed.

(* ===================== the theorem ===================== *)
Theorem w6_c3h : w6_c3h_stmt B MT.
Proof using MTL LAWS.
unfold w6_c3h_stmt, w6_case_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb r Hctx Hin Hra.
destruct r as [|bb r'].
- exact (c3_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb Hctx Hin Hra).
- exact (c3_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb bb r' Hctx Hin Hra).
Qed.

End b.

Print Assumptions w6_c3h.
