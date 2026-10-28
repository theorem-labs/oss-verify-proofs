(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma lor_disjoint_add' : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.
Lemma lor_shl8_byte' : forall a b, (0 <= a)%Z -> (0 <= b < 256)%Z -> Z.lor (a * 256) b = (a * 256 + b)%Z.
Proof.
  intros a b Ha Hb. apply lor_disjoint_add'.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec n 8) as [L|L].
  - replace (a * 256)%Z with (a * 2 ^ 8)%Z by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
    assert (Z.log2 b < 8)%Z; [|lia]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
    apply Z.log2_lt_pow2; lia.
Qed.
End ACeilS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac or_lin := first [ rewrite lor_shl8_byte' by lia | rewrite Z.lor_0_l | rewrite Z.lor_0_r | idtac ].
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma rw_cells_recast : forall sg mm a cs cs', rw_cells sg mm a cs -> cs = cs' -> rw_cells sg mm a cs'.
Proof. intros; subst; assumption. Qed.
End ACeilS2.

Ltac cells_eq :=
  repeat first [ reflexivity | lia
               | lazymatch goal with
                 | |- (_ :: _) = (_ :: _) => f_equal
                 | |- C8 _ = C8 _ => f_equal | |- C4 _ = C4 _ => f_equal | |- C2 _ = C2 _ => f_equal | |- C1 _ = C1 _ => f_equal
                 | |- CB _ _ = CB _ _ => f_equal
                 | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                 end ].
Ltac rw_by H :=
  first [ exact H
        | lazymatch goal with |- rw_cells ?sg ?mm ?a ?cs' =>
            lazymatch type of H with rw_cells sg mm a ?cs => apply (rw_cells_recast sg mm a cs cs' H); cells_eq; cells_eq end end ].
Ltac hd_proj := cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
                     sh_cbn sh_verb sh_origPtr sh_tPos sh_k0].
Ltac bs_proj := unfold bupd; cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
(* [comment removed for export] *)
Ltac by_head S Hstrm := hd_proj; rewrite ?Hstrm; lazymatch goal with H : rw_cells s0segs ?mm S _ |- rw_cells s0segs ?mm S _ => rw_by H end.
Ltac by_strm strm Hsrc Hlen := bs_proj; rewrite ?Hsrc, ?Hlen; lazymatch goal with H : rw_cells s0segs ?mm strm _ |- rw_cells s0segs ?mm strm _ => rw_by H end.
Ltac by_mi := lazymatch goal with H : mem_inv s0segs ?mm |- mem_inv s0segs ?mm => exact H end.
Ltac by_rw A := lazymatch goal with H : rw_cells s0segs ?mm A _ |- rw_cells s0segs ?mm A _ => rw_by H end.
Section ACeilS3. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition MSd (usp S strm : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 x20
          x21 x22 x23 x24 (Z_to_bv 64 strm) x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None m (seg_rom s0segs).

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS3.
