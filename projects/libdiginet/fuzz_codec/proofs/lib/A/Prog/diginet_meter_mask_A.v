(* diginet_meter_mask (diginet_codec.c:202-207) at image A: 0x855ac, 7 instructions, no frame, no memory access, no
   call; against lib/A/Prog/CPgEncC.v's cdc_meter_mask_specX.
   0x855ac li a1,14; the engine stops at 0x855b0 bltu a0,a1 (BC_LTU a0 14), which is split:
   TAKEN (a0 <u 14, so s < 14 as the caller passes s32 s sign-extended, CPgBase.arg_u32A): to 0x855b8 li a1,-1,
      0x855bc sllw a0,a1,a0, 0x855c0 not a0,a0: a0 = sv_mask_lo = ~(-1 << s) = 2^s - 1 = meter_mask_spec s.
   not taken (14 <= s): 0x855b4 li a0,14, then the same three instructions, which the engine folds to the
      literal 16383 = 2^14 - 1 = meter_mask_spec s.
   Both paths end at 0x855c4 ret. The state has no region, so no byte is written (cw_kwr_ro) and the post's memory
   clause holds with T = 0. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgEncC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the arithmetic: the engine's a0 at the ret, as a Z value ---- *)
(* a0 at 0x855c4 on the taken path, as the engine leaves it *)
Definition sv_mask_lo : sv := SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 10 0)) (SLit (-1)).
(* the plain walk's s32_mod_ge / s32_mod_lt / meter_mask_hi (lib/Prog/diginet_meter_mask.v of the plain proof) *)
Lemma mm_s32_mod_ge : forall k n, 0 <= k < 2 ^ 31 -> k <= n < 2 ^ 32 -> k <= s32 n mod 18446744073709551616.
Proof.
  intros k n Hk Hn. unfold s32. destruct (Z.ltb_spec n (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small; lia.
  - Z.div_mod_to_equations. lia.
Qed.
Lemma mm_s32_mod_lt : forall k n, 0 <= k < 2 ^ 31 -> 0 <= n < 2 ^ 32 -> s32 n mod 18446744073709551616 < k -> n < k.
Proof.
  intros k n Hk Hn H. destruct (Z.ltb_spec n k) as [L|L]; [exact L|].
  pose proof (mm_s32_mod_ge k n Hk ltac:(lia)). lia.
Qed.
Lemma mm_meter_mask_hi : forall n, 14 <= n -> meter_mask_spec n = 16383.
Proof. intros n Hn. unfold meter_mask_spec. rewrite Z.min_r by lia. reflexivity. Qed.
(* an n below k (k < 2^31) passed as s32 n reads as n unsigned, so k <= s32 n mod 2^64 gives k <= n *)
Lemma mm_s32_mod_ge_inv : forall k n, 0 <= k < 2 ^ 31 -> 0 <= n -> k <= s32 n mod 18446744073709551616 -> k <= n.
Proof.
  intros k n Hk Hn H. destruct (Z.ltb_spec n k) as [L|L]; [|exact L].
  unfold s32 in H. rewrite (proj2 (Z.ltb_lt n (2 ^ 31))) in H by lia.
  rewrite Z.mod_small in H by lia. lia.
Qed.
(* the argument atom a0 = s32 n reads as s32 n mod 2^64 *)
Lemma mm_U_arg : forall E n, ew E 10 = Z_to_bv 64 (s32 n) -> U E (SOff 10 0) = s32 n mod 18446744073709551616.
Proof.
intros E n H. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon, M64.
change (2 ^ 64) with 18446744073709551616. apply Zmod_mod.
Qed.
Lemma U_mask_lo : forall E n, ew E 10 = Z_to_bv 64 (s32 n) -> 0 <= n < 14 -> U E sv_mask_lo = meter_mask_spec n.
Proof.
intros E n H10 Hn. pose proof (mm_U_arg E n H10) as Ux. unfold sv_mask_lo.
rewrite U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, Ux, !U_SLit. cbn [zalu_raw].
replace n with (Z.of_nat (Z.to_nat n)) by lia.
assert (K : (Z.to_nat n < 14)%nat) by lia.
generalize (Z.to_nat n) K. clear. intros j K.
do 14 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.

(* ---- the walk ---- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.
Theorem diginet_meter_mask_A_holds : cdc_meter_mask_specX tfibsegs B MT 0x855ac.
Proof using MTL LAWS.
unfold cdc_meter_mask_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s HEN Harg.
destruct HEN as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
destruct Harg as (Hs & H10).
pose proof HJ0 as HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry0 0x855ac [] W regs memc) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (s32 s)) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
clear HE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a)
by (intros; reflexivity).
pose proof (mm_U_arg E s E10) as Ux.
unfold cfg_at. change (w64 0x855ac) with (Z_to_bv 64 0x855ac).
(* 0x855ac li a1,14; stop at 0x855b0 bltu a0,a1 *)
cw_run awr_ok_tac. cw_keep cw_kwr_ro.
cw_branch Hb.
- (* bltu TAKEN: s < 14; 0x855b8-0x855c0 give 2^s - 1 *)
  rewrite branch_ltu_U, Ux, U_lit in Hb by lia. apply Z.ltb_lt in Hb.
  pose proof (mm_s32_mod_lt 14 s ltac:(lia) Hs Hb) as L.
  pose proof (U_mask_lo E s E10 ltac:(lia)) as Um. unfold sv_mask_lo in Um.
  cw_run awr_ok_tac. cw_keep cw_kwr_ro.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(idtac; intros ? []) ltac:(idtac; intros ? []))
  ltac:(cbv beta; rewrite R10, denot_lit_U, Um; reflexivity).
- (* not taken: 14 <= s; 0x855b4 li a0,14, then a0 = 16383 *)
  rewrite branch_ltu_U, Ux, U_lit in Hb by lia. apply Z.ltb_ge in Hb.
  pose proof (mm_s32_mod_ge_inv 14 s ltac:(lia) ltac:(lia) Hb) as L.
  cw_run awr_ok_tac. cw_keep cw_kwr_ro.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(idtac; intros ? []) ltac:(idtac; intros ? []))
  ltac:(cbv beta; rewrite R10, (mm_meter_mask_hi s L); reflexivity).
Qed.
End d.
End b.
