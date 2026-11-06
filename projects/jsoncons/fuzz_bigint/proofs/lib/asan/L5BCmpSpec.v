(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Cmp L5DefsAB0 L5CoreAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5CMPB.
Import L5A. Import L5CA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition CMP : Z := 0x91dd0.
Definition CMP_FR : Z := 112.
(* [comment removed for export] *)
Definition cmp_kept : list nat := [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition cmp_objA (M : word -> option byte) (sp o : Z) (b : L5.bigobj) : Prop :=
  L5.big_at RSEGS M o b /\ Z.testbit (L5.bo_fb b) 1 = false /\ (1 <= L5.bo_len b)%nat /\ Z.of_nat (L5.bo_len b) <= 300 /\
  o mod 8 = 0 /\ 4096 <= o <= 140737488355296 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\
  (sp - 112 + 112 <= o \/ o + 32 <= sp - 112) /\ L5KA.zeros_at M (o / 8 + SB) 4 /\
  (4096 <= L5.bo_data o b /\ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 140737488355328) /\ L5.bo_data o b mod 8 = 0 /\
  (2147446784 + 17592186048512 <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 2147446784) /\
  (sp <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= sp - 112) /\
  L5KA.zeros_at M (L5.bo_data o b / 8 + SB) (Z.of_nat (L5.bo_len b)).

Definition cmp_postA (M M' : word -> option byte) (R R' : bvmap 5 word) (sp : Z) (nx ny : nat) (wx wy : list Z) : Prop :=
  (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ (exists c, getr R' (reg 10) = Z_to_bv 64 c /\ L5CMP.res_sized c nx ny /\ (nx = ny -> c = L5CMP.cmp_val wx wy))
  /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.

Definition cmp_run_at : Prop :=
  forall (fx : FPState) R M (xo yo sp r : Z) (bx by_ : L5.bigobj) (wx wy : list Z),
  getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R (reg 2) = Z_to_bv 64 sp -> 140735332487280 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 112) 112 ->
  L5KA.zeros_at M ((sp - 112) / 8 + SB) 14 ->
  L5.img_clear M 860160 884736 -> L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  cmp_objA M sp xo bx -> cmp_objA M sp yo by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M')
    /\ cmp_postA M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

End SCFG_1.
End L5CMPB.
