(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 220 of its 261 lines of code are new or changed and 592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_range_A.v, with its module names changed; 261 of its 301 lines of code are new or changed and 221 lines of the source are left out. *)
(* check_text_masks (fuzz_codec.c:492-519) at image A 0x842b0, 55 instructions, real frame 48, no instrumented check,
   against lib/A/Prog/CPgChkC.v's cdc_check_masks_specX; a0 = n (arg_u32A), a1 = mask (arg_zxA 16).
   0x842b0-0x842d4 open the frame and save ra and s0-s3 into [sp - 48, sp), the walk's only stores (cw_awr_stk /
   cw_kwr_stk); s0 = n, s1 = mask. 0x842d8 bltu a0,14 clamps s3 = min(n, 14): both arms join at 0x842e0 with s3 pinned
   to atom 33 (= min(n, 14), an extra of the entry environment) and the branch condition dropped (CONT1).
   Four calls of frameless leaves through their contracts (CPgEncC.v, each T = 0 and cno_wr) by CPgWalkCall's
   cpw_call_reseat: 0x842e4 diginet_meter_mask, 0x842fc diginet_meter_segments, 0x84328 diginet_ring_dot, 0x84348
   diginet_ring_fill; the re-seat keeps the save area (the callee's window is empty and below it) and the two image
   cells, and what the walk kept since its entry (KT) is composed with each callee's tcj_kept.
   Each comparison's taken side jumps to the abort call at 0x84384 and is refuted: 0x842f4 by ctm_chk1, 0x84340 by
   ctm_chk3 (ring_dot), 0x84364 by ctm_chk4 (ring_fill). The inlined spec_segments loop 0x84308-0x84318 is run test by
   test (ctm_iter, fifteen tests: ctm_seg reads the engine's test at index j as mask = 2^j - 1); each of its sixteen
   exits reaches 0x84320 bne a0,a1, whose taken side is refuted by HE2 (meter_segments(mask) = spec_seg_go mask j ..),
   and joins at 0x84324 with a1 and a3 (dead) moved to fresh atoms (CONT2). The arithmetic lemmas follow the plain
   proof's lib/Prog/check_text_masks_bits.v. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgWalk CPgWalkKept CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgEncC CPgChkC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the arithmetic ---- *)
Lemma ctm_s32_lo : forall n, n < 2 ^ 31 -> s32 n = n.
Proof. intros n H. unfold s32. rewrite (proj2 (Z.ltb_lt n (2 ^ 31)) H). reflexivity. Qed.
Lemma ctm_s32_hi : forall n, 2 ^ 31 <= n -> s32 n = n - 2 ^ 32.
Proof. intros n H. unfold s32. rewrite (proj2 (Z.ltb_ge n (2 ^ 31)) H). reflexivity. Qed.
(* the register of an unsigned 32-bit argument n, sign-extended from bit 31: n itself below 2^31, else at least 2^63 *)
Lemma ctm_u : forall n, 0 <= n < 2 ^ 32 ->
  (n < 2 ^ 31 /\ bv_unsigned (Z_to_bv 64 (s32 n)) = n) \/
  (2 ^ 31 <= n /\ 2 ^ 63 <= bv_unsigned (Z_to_bv 64 (s32 n))).
Proof.
  intros n Hn. destruct (Z.lt_ge_cases n (2 ^ 31)) as [H|H].
  - left. split; [exact H|]. rewrite ctm_s32_lo by exact H. apply unsigned_lit_small. lia.
  - right. split; [exact H|]. rewrite ctm_s32_hi by exact H. rewrite unsigned_lit.
    unfold zcanon, M64. rewrite <- (Z.mod_add (n - 2 ^ 32) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the atom of a0 read unsigned *)
Lemma ctm_U10 : forall E n, ew E 10 = Z_to_bv 64 (s32 n) -> U E (SOff 10 0) = bv_unsigned (Z_to_bv 64 (s32 n)).
Proof.
intros E n H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (s32 n))) as R. unfold M64. change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
(* check 1 (0x842e8-0x842f4): (sllw -1, lit) xor meter_mask(n) is all ones, lit = min(n, 14) *)
Lemma ctm_chk1 : forall E a b L v, ew E a = Z_to_bv 64 L -> ew E b = Z_to_bv 64 v -> 0 <= L < 15 ->
  v = (2 ^ L - 1) mod 2 ^ 16 ->
  U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff a 0)) (SOff b 0)) = 18446744073709551615.
Proof.
intros E a b L v Ha Hb HL Hv. subst v.
rewrite U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, U_SLit, !U_SOff, Ha, Hb.
replace L with (Z.of_nat (Z.to_nat L)) by lia.
assert (K : (Z.to_nat L < 15)%nat) by lia.
generalize (Z.to_nat L) K. clear. intros j K.
do 15 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
(* an atom holding v read unsigned *)
Lemma ctm_U_atom_mod : forall E m v, ew E m = Z_to_bv 64 v -> U E (SOff m 0) = v mod 2 ^ 64.
Proof.
intros E m v H. rewrite U_SOff, H, Z.add_0_r. unfold zcanon, M64. rewrite unsigned_lit. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
(* the loop's test at index j (0x84308-0x84310): ((sllw -1, j) xor mask == -1) is mask = 2^j - 1; the engine folds the
   shift to the literal 2^64 - 2^j *)
Lemma ctm_seg : forall E c mask j, ew E 11 = Z_to_bv 64 mask -> 0 <= mask < 2 ^ 16 -> 0 <= j < 15 ->
  c = 2 ^ 64 - 2 ^ j ->
  (U E (SAlu ALU_XOR (SLit c) (SOff 11 0)) =? U E (SLit 18446744073709551615)) = (mask =? 2 ^ j - 1).
Proof.
intros E c mask j H Hm Hj Hc. subst c.
assert (P1 : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
assert (P2 : 2 ^ j <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
change (2 ^ 14) with 16384 in P2. change (2 ^ 16) with 65536 in Hm.
rewrite U_SAlu, !U_SLit, U_SOff, H, Z.add_0_r, unsigned_lit_small by lia. cbn [zalu_raw].
set (a := 2 ^ 64 - 2 ^ j).
rewrite (zcanon_id a) by (unfold M64, a; lia).
rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite (zcanon_id mask) by (unfold M64; lia).
assert (Rx : ZBridge.inr64 (Z.lxor a mask)) by (apply ZBridge.zr_lxor; unfold ZBridge.inr64, a; lia).
unfold ZBridge.inr64 in Rx. rewrite (zcanon_id (Z.lxor a mask)) by (unfold M64; lia).
assert (Ea : Z.lxor a 18446744073709551615 = 2 ^ j - 1) by (rewrite ZBridge.zb_lxor_ones by (unfold a; lia); unfold a; lia).
destruct (Z.eqb_spec mask (2 ^ j - 1)) as [E1|E1].
- apply Z.eqb_eq. rewrite E1, <- Ea, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
- apply Z.eqb_neq. intros C. apply E1. rewrite <- Ea, <- C, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.
Lemma spec_seg_go_S : forall m j k,
  spec_seg_go m j (S k) = if m =? 2 ^ Z.of_nat j - 1 then Z.of_nat j else spec_seg_go m (S j) k.
Proof. reflexivity. Qed.
(* check 3 (0x8432c-0x84340): (-(n <u 15)) and (sllw 1, n) is ring_dot(n) *)
Lemma ctm_chk3 : forall E a n v, ew E 10 = Z_to_bv 64 (s32 n) -> 0 <= n < 2 ^ 32 -> ew E a = Z_to_bv 64 v ->
  v = ring_dot_spec n ->
  U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 15))) (SAluw ALU_SLL (SLit 1) (SOff 10 0)))
  = U E (SOff a 0).
Proof.
intros E a n v H10 Hn Ha Hv. rewrite (ctm_U_atom_mod E a v Ha), Hv.
pose proof (ctm_U10 E n H10) as U10.
unfold ring_dot_spec. destruct (Z.ltb_spec n 15) as [L|L].
- rewrite !U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, U10, !U_SLit. cbn [zalu_raw].
  rewrite ctm_s32_lo by lia.
  replace n with (Z.of_nat (Z.to_nat n)) by lia.
  assert (K : (Z.to_nat n < 15)%nat) by lia.
  generalize (Z.to_nat n) K. clear. intros j K.
  do 15 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
- assert (G : 15 <= bv_unsigned (Z_to_bv 64 (s32 n))) by (destruct (ctm_u n Hn) as [[H1 H2]|[H1 H2]]; lia).
  rewrite (U_SAlu E ALU_AND), (U_SAlu E ALU_SUB), (U_SAlu E ALU_SLTU), U10, !U_SLit. cbn [zalu_raw].
  change (zcanon 15) with 15. rewrite (proj2 (Z.ltb_ge _ 15) G).
  replace (zcanon (zcanon 0 - zcanon 0)) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
Qed.
(* check 4 (0x8434c-0x84364): (-(n <u 16)) and not (sllw -1, n) is ring_fill(n) *)
Lemma ctm_chk4 : forall E a n v, ew E 10 = Z_to_bv 64 (s32 n) -> 0 <= n < 2 ^ 32 -> ew E a = Z_to_bv 64 v ->
  v = ring_fill_spec n ->
  U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 16)))
         (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 10 0)) (SLit (-1))))
  = U E (SOff a 0).
Proof.
intros E a n v H10 Hn Ha Hv. rewrite (ctm_U_atom_mod E a v Ha), Hv.
pose proof (ctm_U10 E n H10) as U10.
unfold ring_fill_spec. destruct (Z.leb_spec n 15) as [L|L].
- rewrite !U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, U10, !U_SLit. cbn [zalu_raw].
  rewrite ctm_s32_lo by lia.
  replace n with (Z.of_nat (Z.to_nat n)) by lia.
  assert (K : (Z.to_nat n < 16)%nat) by lia.
  generalize (Z.to_nat n) K. clear. intros j K.
  do 16 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
- assert (G : 16 <= bv_unsigned (Z_to_bv 64 (s32 n))) by (destruct (ctm_u n Hn) as [[H1 H2]|[H1 H2]]; lia).
  rewrite (U_SAlu E ALU_AND), (U_SAlu E ALU_SUB), (U_SAlu E ALU_SLTU), U10, !U_SLit. cbn [zalu_raw].
  change (zcanon 16) with 16. rewrite (proj2 (Z.ltb_ge _ 16) G).
  replace (zcanon (zcanon 0 - zcanon 0)) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
Qed.
(* the state's register r pinned to e (dtac: sv_denot E e = sv_denot E <the engine's value>) *)
Ltac ctm_pin r e dtac :=
lazymatch goal with HS : YP0l.st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
let cur := eval vm_compute in (sr_get (ss_regs ssx) r) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx (restrict Hh msx) r e HS ltac:(intros X; discriminate X)
  ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx r HS);
        change (sv_denot Ev e = sv_denot Ev cur); dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the state's branch conditions dropped *)
Ltac ctm_drop_conds :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx ?msx |- _ =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let al := eval vm_compute in (f_alias (ss_facts ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_facts_incl3 tfibsegs Ev ssx msx fa [] al HS ltac:(intros x Hx; exact Hx) ltac:(intros x [])
  ltac:(intros x Hx; exact Hx)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the callee's argument a0 = s0 = n *)
Ltac ctm_arg_n :=
idtac; lazymatch goal with Hn : arg_u32A _ ?n, E10 : ew ?Ev 10 = Z_to_bv 64 (s32 ?n), HS : YP0l.st_ok _ ?Ev _ _ |- arg_u32A _ _ =>
let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite E10 in R; exact (conj (proj1 Hn) R) end.
(* the callee's argument a0 = s1 = mask *)
Ltac ctm_arg_mask :=
idtac; lazymatch goal with Hm : arg_zxA 16 _ ?m, E11 : ew ?Ev 11 = Z_to_bv 64 ?m, HS : YP0l.st_ok _ ?Ev _ _ |- arg_zxA 16 _ _ =>
let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite E11 in R; exact (conj (proj1 Hm) R) end.
(* the abort call after the loop (0x84320 bne a0,a1 taken), refuted: a0 holds meter_segments(mask), which HG gives *)
Ltac ctm_refute_seg :=
lazymatch goal with Hd : branch_taken BC_NE _ _ = true, EMS : ew _ _ = Z_to_bv 64 (meter_segments_spec ?m),
  HG : meter_segments_spec ?m = _ |- False =>
rewrite branch_ne_U, (ctm_U_atom_mod _ _ _ EMS), HG, U_SLit in Hd; vm_compute in Hd; discriminate Hd end.
(* the join of the loop's sixteen exits at 0x84324: a1 and a3 (dead: the next call clobbers them) moved to the fresh
   atoms 66 / 67, the branch conditions dropped, then CONT2 *)
Ltac ctm_join CONT2 :=
lazymatch goal with HS : YP0l.st_ok tfibsegs ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
let HS1 := fresh "HS1" in
pose proof (st_ok_havoc tfibsegs 66 Ev ssx (restrict Hh msx) [getr (ms_regs msx) 11; getr (ms_regs msx) 13] HS
  ltac:(vm_compute; reflexivity)) as HS1;
clear HS; rename HS1 into HS end;
lazymatch goal with HS : YP0l.st_ok tfibsegs ?Ev ?ssx ?msr |- _ =>
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev (SOff 66 0) = getr (ms_regs msr) 11) by (rewrite sv_denot_SOff0; reflexivity);
let HS1 := fresh "HS1" in
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msr (11%bv : bv 5) (SOff 66 0) HS eq_refl Hv) as HS1;
clear HS Hv; rename HS1 into HS; norm_ss HS end;
lazymatch goal with HS : YP0l.st_ok tfibsegs ?Ev ?ssx ?msr |- _ =>
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev (SOff 67 0) = getr (ms_regs msr) 13) by (rewrite sv_denot_SOff0; reflexivity);
let HS1 := fresh "HS1" in
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msr (13%bv : bv 5) (SOff 67 0) HS eq_refl Hv) as HS1;
clear HS Hv; rename HS1 into HS; norm_ss HS end;
ctm_drop_conds;
lazymatch goal with HS : YP0l.st_ok _ _ _ _ |- _ =>
eapply CONT2; [exact HS | eassumption | eassumption | cpw_io] end.
(* the exit at 0x84320 bne a0,a1 *)
Ltac ctm_exit CONT2 :=
let Hd := fresh "Hd" in cw_branch Hd; [ exfalso; ctm_refute_seg | clear Hd; cw_run_to cw_awr_stk 0x84324; cpw_keep cw_kwr_stk; ctm_join CONT2 ].
(* one test of the loop, at 0x84310 beq a3,s2 with a1 = j: taken (mask = 2^j - 1) to the exit at 0x84320; not taken,
   addiw a1 / bne a1,a2 back to the next test (or, after j = 14, li a1,-1 to the exit) *)
Ltac ctm_iter CONT2 :=
lazymatch goal with HG : meter_segments_spec ?m = spec_seg_go ?m ?j (S ?k), E11 : ew _ 11 = Z_to_bv 64 ?m,
  Hm : arg_zxA 16 _ ?m |- _ =>
let Hc := fresh "Hc" in cw_branch Hc;
[ rewrite branch_eq_U in Hc; erewrite (ctm_seg _ _ m (Z.of_nat j)) in Hc;
  [ | exact E11 | exact (proj1 Hm) | lia | vm_compute; reflexivity ];
  rewrite spec_seg_go_S, Hc in HG; clear Hc;
  cw_run cw_awr_stk; cpw_keep cw_kwr_stk; ctm_exit CONT2
| rewrite branch_eq_U in Hc; erewrite (ctm_seg _ _ m (Z.of_nat j)) in Hc;
  [ | exact E11 | exact (proj1 Hm) | lia | vm_compute; reflexivity ];
  rewrite spec_seg_go_S, Hc in HG; clear Hc;
  cw_run cw_awr_stk; cpw_keep cw_kwr_stk ] end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MM : cdc_meter_mask_specX tfibsegs B MT 0x855ac.
Hypothesis MSG : cdc_meter_segs_specX tfibsegs B MT 0x855c8.
Hypothesis RD : cdc_ring_dot_specX tfibsegs B MT 0x852d0.
Hypothesis RF : cdc_ring_fill_specX tfibsegs B MT 0x852f0.
Theorem check_text_masks_A_holds : cdc_check_masks_specX tfibsegs B MT 0x842b0.
Proof using MTL TL LAWS MM MSG RD RF.
unfold cdc_check_masks_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n mask HEN Hn Hmask HE1 HE2 HE3 HE4.
pose proof HEN as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_masks HEN
  ltac:(unfold T_check_masks; lia)) as (Hceil & H47 & H46 & _ & Hpres).
unfold T_check_masks in *.
pose proof (cw_entry_base B TL LAWS 0x842b0 48 [Z.min n 14] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 48
  HEN ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs (cw_extra [Z.min n 14])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [Z.min n 14])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (cw_ew_reg regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (cw_ew_reg regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (s32 n)) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact (proj2 Hn)).
assert (E11 : ew E 11 = Z_to_bv 64 mask) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl); exact (proj2 Hmask)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.min n 14)) by (subst E; exact (cw_ew_x regs [Z.min n 14] 0)).
clear HE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 48 cno_wr HJ0 ltac:(lia) ltac:(lia))
  as KT.
assert (HFRS : frames Sc = frames Sc) by reflexivity.
assert (HPERM : Permutation (ablocks B lyc Sc) (ablocks B lyc Sc)) by apply Permutation_refl.
assert (HIO : same_io mdc mdc) by apply same_io_refl.
assert (HMO : mo_le MT Sc Sc 0) by (apply mo_le_refl; exact MTL).
pose proof HJ0 as HJ.
pose proof (ctm_U10 E n E10) as U10.
unfold cfg_at. change (w64 0x842b0) with (Z_to_bv 64 0x842b0).
(* 0x842b0-0x842d4: the frame, the saves of ra and s0-s3, s1 = mask, s0 = s3 = n, a1 = 14; stop at 0x842d8 bltu *)
cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
(* the clamp joins at 0x842e0 with s3 = min(n, 14), held by atom 33 *)
lazymatch goal with |- SRr _ _ _ ?Q =>
eassert (CONT1 : forall ms1 md1, YP0l.st_ok tfibsegs E _ (restrict (w_H W) ms1) ->
  sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) (ms_mem ms1)) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) md1 k ->
  tcj_kept tfibsegs B 48 lyc Sc W memc W (ms_mem ms1) (spZ regs) cno_wr ->
  same_io mdc md1 ->
  SRr tfibsegs W (mkCfg ms1 md1) Q) end.
2: {
cw_branch Hc.
all: rewrite branch_ltu_U, U10, U_lit in Hc by lia.
- (* taken: n < 14, s3 = a0 = n *)
  assert (Hlt : n < 14) by (destruct (ctm_u n (proj1 Hn)) as [[H1 H2]|[H1 H2]]; rewrite ?H2 in Hc; apply Z.ltb_lt in Hc; lia).
  cw_run_to cw_awr_stk 0x842e0. cpw_keep cw_kwr_stk.
  ctm_pin (19%bv : bv 5) (SOff 33 0) ltac:(rewrite !sv_denot_SOff0, E33, E10, ctm_s32_lo by lia; f_equal; lia).
  ctm_drop_conds.
  eapply CONT1; [exact HS | exact SHOK | exact HJ | exact KT | cpw_io].
- (* not taken: 14 <= n, 0x842dc li s3,14 *)
  assert (Hge : 14 <= n) by (destruct (ctm_u n (proj1 Hn)) as [[H1 H2]|[H1 H2]]; rewrite ?H2 in Hc; apply Z.ltb_ge in Hc; lia).
  cw_run_to cw_awr_stk 0x842e0. cpw_keep cw_kwr_stk.
  ctm_pin (19%bv : bv 5) (SOff 33 0) ltac:(rewrite sv_denot_SOff0, E33; cbn [sv_denot]; f_equal; lia).
  ctm_drop_conds.
  eapply CONT1; [exact HS | exact SHOK | exact HJ | exact KT | cpw_io].
}
clear HS SHOK HJ KT HIO.
intros ms1 md1 HS SHOK HJ KT HIO.
(* 0x842e0 mv a0,s0; jal diginet_meter_mask *)
cw_run_to cw_awr_stk 0x855ac. cpw_keep cw_kwr_stk.
cpw_call_reseat MM 48 ctm_arg_n [0; 1; 2]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
rewrite HRc in HA0c. unfold w64 in HA0c. rename HA0c into EMM. clear HRc.
(* 0x842e8 li s2,-1; sllw a1,s2,s3; xor a0,a1,a0; stop at 0x842f4 bne a0,s2 *)
cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
pose proof (Z.min_spec n 14) as Hmin. pose proof (proj1 Hn) as Hn0.
cw_branch Hc.
- (* taken: the abort call, refuted *)
  exfalso. unfold meter_mask_spec in EMM.
  rewrite branch_ne_U, (ctm_chk1 _ 33 _ (Z.min n 14) _ E33 EMM ltac:(lia) eq_refl), U_lit in Hc by lia.
  rewrite Z.eqb_refl in Hc. discriminate Hc.
- clear Hc.
  (* 0x842f8 mv a0,s1; jal diginet_meter_segments *)
  cw_run_to cw_awr_stk 0x855c8. cpw_keep cw_kwr_stk.
  cpw_call_reseat MSG 48 ctm_arg_mask [0; 1; 2]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
  rewrite HRc in HA0c. unfold w64 in HA0c. rename HA0c into EMS. clear HRc.
  (* 0x84300 li a1,0; li a2,15; the loop's first test at 0x84310 beq a3,s2 *)
  cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
  assert (HG : meter_segments_spec mask = spec_seg_go mask 0 15) by exact HE2.
  (* the loop's sixteen exits join at 0x84324 *)
  lazymatch goal with |- SRr _ _ _ ?Q =>
  lazymatch goal with HS : YP0l.st_ok _ ?E1 _ (restrict (w_H ?W2) _),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly2 ?S2 ?W2 _ _ _ |- _ =>
  eassert (CONT2 : forall ms2 md2,
    YP0l.st_ok tfibsegs (havoc E1 66 [getr (ms_regs ms2) 11; getr (ms_regs ms2) 13]) _ (restrict (w_H W2) ms2) ->
    ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms2) md2 k ->
    tcj_kept tfibsegs B 48 lyc Sc W memc W2 (ms_mem ms2) (spZ regs) cno_wr ->
    same_io mdc md2 ->
    SRr tfibsegs W2 (mkCfg ms2 md2) Q) end end.
  2: { do 15 (ctm_iter CONT2). ctm_exit CONT2. }
  clear HS HJ KT HIO SHOK HG.
  intros msJ mdJ HS HJ KT HIO.
  cpw_rebase.
  (* 0x84324 mv a0,s0; jal diginet_ring_dot *)
  cw_run_to cw_awr_stk 0x852d0. cpw_keep cw_kwr_stk.
  cpw_call_reseat RD 48 ctm_arg_n [0; 1; 2]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
  rewrite HRc in HA0c. unfold w64 in HA0c. rename HA0c into ERD. clear HRc.
  (* 0x8432c sltiu a1,s0,15; li a2,1; sllw a2,a2,s0; neg a1,a1; and a1,a1,a2; stop at 0x84340 bne a1,a0 *)
  cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
  cw_branch Hc.
  + (* taken: the abort call, refuted *)
    exfalso. rewrite branch_ne_U, (ctm_chk3 _ _ n _ E10 Hn0 ERD eq_refl), Z.eqb_refl in Hc. discriminate Hc.
  + clear Hc.
    (* 0x84344 mv a0,s0; jal diginet_ring_fill *)
    cw_run_to cw_awr_stk 0x852f0. cpw_keep cw_kwr_stk.
    cpw_call_reseat RF 48 ctm_arg_n [0; 1; 2]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
    rewrite HRc in HA0c. unfold w64 in HA0c. rename HA0c into ERF. clear HRc.
    (* 0x8434c sltiu a1,s0,16; li a2,-1; sllw a2,a2,s0; not a2,a2; neg a1,a1; and a1,a1,a2; stop at 0x84364 bne a1,a0 *)
    cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
    cw_branch Hc.
    * (* taken: the abort call, refuted *)
      exfalso. rewrite branch_ne_U, (ctm_chk4 _ _ n _ E10 Hn0 ERF eq_refl), Z.eqb_refl in Hc. discriminate Hc.
    * clear Hc.
      (* 0x84368-0x84380: the epilogue and ret *)
      cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
      cpw_leaf ltac:(exact KT) ltac:(exact I).
Qed.
End d.
End b.
