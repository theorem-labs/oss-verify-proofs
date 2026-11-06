(* diginet_ring_dot (diginet_codec.c:169-172) at image A: 0x852d0, 8 instructions, branchless, no frame, no memory
   access, no call; against lib/A/Prog/CPgEncC.v's cdc_ring_dot_specX.
   0x852d0 sltiu a1,a0,15 / 0x852dc negw a1,a1 make the mask (a0 <u 15 ? -1 : 0), 0x852d4 li a2,1 /
   0x852d8 sllw a0,a2,a0 the word 1 << (a0 mod 32), 0x852e0 and joins them, 0x852e4 slli 48 / 0x852e8 srli 48
   zero-extend the uint16_t, 0x852ec ret. The engine runs from the entry to the ret in one run (no undecided
   branch); it leaves a0 = sv_dot (the negw is a 64-bit subtraction there, as the sltiu result is 0 or 1).
   The caller passes n as s32 n sign-extended (CPgBase.arg_u32A), so the unsigned compare with 15 is n < 15.
   The state has no region, so no byte is written (cw_kwr_ro) and the post's memory clause holds with T = 0. *)
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
(* a0 at 0x852ec, as the engine leaves it *)
Definition sv_dot : sv :=
SAlu ALU_SRL
  (SAlu ALU_SLL
     (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 15)))
        (SAluw ALU_SLL (SLit 1) (SOff 10 0)))
     (SLit 48))
  (SLit 48).
(* the plain walk's s32_mod_ge (lib/Prog/diginet_ring_dot.v of the plain proof): an unsigned n >= k (k < 2^31)
   passed as s32 n reads as at least k unsigned *)
Lemma dot_s32_mod_ge : forall k n, 0 <= k < 2 ^ 31 -> k <= n < 2 ^ 32 -> k <= s32 n mod 18446744073709551616.
Proof.
  intros k n Hk Hn. unfold s32. destruct (Z.ltb_spec n (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small; lia.
  - Z.div_mod_to_equations. lia.
Qed.
(* the argument atom a0 = s32 n reads as s32 n mod 2^64 *)
Lemma dot_U_arg : forall E n, ew E 10 = Z_to_bv 64 (s32 n) -> U E (SOff 10 0) = s32 n mod 18446744073709551616.
Proof.
intros E n H. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon, M64.
change (2 ^ 64) with 18446744073709551616. apply Zmod_mod.
Qed.
(* `sltiu c, a, k; negw c, c; and r, c, b` with a >=u k: r = 0 *)
Lemma dot_U_mask0 : forall E a b k, 0 <= k < 2 ^ 64 -> k <= U E a ->
U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU a (SLit k))) b) = 0.
Proof.
intros E a b k Hk Ha. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (zcanon_id k) by (unfold M64; lia).
rewrite (proj2 (Z.ltb_ge (U E a) k) Ha).
first [reflexivity | vm_compute; reflexivity].
Qed.
Lemma U_dot : forall E n, ew E 10 = Z_to_bv 64 (s32 n) -> 0 <= n < 2 ^ 32 -> U E sv_dot = ring_dot_spec n.
Proof.
intros E n H10 Hn. pose proof (dot_U_arg E n H10) as Ux. unfold sv_dot, ring_dot_spec.
destruct (Z.ltb_spec n 15) as [L|L].
- rewrite !U_SAlu, (U_of_S E (SAluw _ _ _)), S_SAluw, Ux, !U_SLit. cbn [zalu_raw].
  replace n with (Z.of_nat (Z.to_nat n)) by lia.
  assert (K : (Z.to_nat n < 15)%nat) by lia.
  generalize (Z.to_nat n) K. clear. intros j K.
  do 15 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
- rewrite (U_SAlu E ALU_SRL), (U_SAlu E ALU_SLL).
  rewrite (dot_U_mask0 E (SOff 10 0) _ 15 ltac:(lia)
    ltac:(rewrite Ux; exact (dot_s32_mod_ge 15 n ltac:(lia) ltac:(lia)))).
  rewrite !U_SLit. vm_compute. reflexivity.
Qed.

(* ---- the walk ---- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.
Theorem diginet_ring_dot_A_holds : cdc_ring_dot_specX tfibsegs B MT 0x852d0.
Proof using MTL LAWS.
unfold cdc_ring_dot_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HEN Harg.
destruct HEN as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
destruct Harg as (Hn & H10).
pose proof HJ0 as HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry0 0x852d0 [] W regs memc) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (s32 n)) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
clear HE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a)
by (intros; reflexivity).
pose proof (U_dot E n E10 Hn) as Ud. unfold sv_dot in Ud.
unfold cfg_at. change (w64 0x852d0) with (Z_to_bv 64 0x852d0).
(* 0x852d0-0x852e8, then the stop at 0x852ec ret *)
cw_run awr_ok_tac. cw_keep cw_kwr_ro.
cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(idtac; intros ? []) ltac:(idtac; intros ? []))
ltac:(cbv beta; rewrite R10, denot_lit_U, Ud; reflexivity).
Qed.
End d.
End b.
