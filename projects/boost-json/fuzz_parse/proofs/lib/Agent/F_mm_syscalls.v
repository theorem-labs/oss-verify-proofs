(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hc8mmap_len46Stdlib6ZArith6BinInt1Zm42le04Nposhc9range_ans35stdpp9bitvectorbdefinitionsp32bvp37Z_to_bv37Corelib4Init9Datatypesrf4bool37Corelib4Init5Logicte2eqm46modulom44landm45ldiffte3andm42ltm43powm43subm43eqbrf6optionrf4prodrf4consrf3nilrf4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hl02wa3h5LinuxProcessSemanticsfLinuxProcessSem3Runhp0capply_unmapshp0bapply_zeros79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~htb4resprf4listrf3nat3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiic7MemCopyiic9mkEffectU" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.


End HCW.


(* [comment removed for export] *)
Ltac transport_zeros segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac transport_unmaps segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma mmap_len_ge : ltac2:(zQ "30!h9!l9!nc>3len$0@2$2^1@1$1^1").
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_ret : ltac2:(zQ "30!o1!o7!r0>1a$1@1$2@1$0#k0") := ltac2:(zQ "60!o1!o7!r5!t7!h9!r0\1a$1M1\1a$1@1$5@1$0#k0^1\1e$4@2$2@1$0#k0-1\7changed$3@2$2@1$0#k0Z").
Definition rg_errno : ltac2:(zQ "30!o1!r0!o7>1a$2>4errv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!o1!o7!r0!t7!h9!r5\1a$1\4errv@1$2@1$0#k0M1\1a$1@1$2@1$0#k0^2\1e$4@2$5@1$0#k0^1\7changed$3^2").

(* [comment removed for export] *)

Lemma mmap_len_aligned : ltac2:(zQ "40!h9!v2!l9!v7>3len$0>0@3$1$0@2$3^1+hgg0Z@3$1$0@1$2^2^2").
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Lemma land_ldiff_distr' : ltac2:(zQ "40!h9!hg0!hg7!v2>1x$0>1a$0>1b$0@3$3$0@2$1^3@2$2^2^1@2$2@2$1^3^2^1").
Proof. intros x a b. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_m4096 : ltac2:(zQ "90!h9!hgf!v2!hg0!nc!hh5!v7!hha!hi0>1x$0>0@2$1@2$4Z^1@2$5^1@2$7+2+k0@3$2$0@2$3^2+vvvvvvvvvvvvvgg0@2$8^2@2$6^2+hgg0").
Proof. intros x.
  intros Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

   (* [comment removed for export] *)
          (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_fix_errno : ltac2:(zQ "10!h9>1e$0$0") := ltac2:(zQ "30!t7!h9!hi6\1e$1M0\0$0$1@2$2^1+1+c^1").

(* [comment removed for export] *)
Definition mmap_raw : ltac2:(zQ "51!o1!r0!hic!h9!t7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>6isnone$4>1x$3>3len$3>1m~0~0") := ltac2:(zQ "e5!o1!r0!hj5!t7!hjc!hk3!hic!hk9!h9!l9!hoa!r5!hrc!hsc&>0@1$1@1$0#k0@1$6@1$1@1$0#8&@2$2@1$1@1$0#k0@1$1@1$0#k0&@4$7@1$1@1$0#k0@1$1@1$0#k0@1$a^3@2$b@1$0#k0@1$9^2&@1$5~1&@3$4~1~2~3\6isnone$3\1x$8\3len$8\1m~0M3\6isnone$3~0^4@2$c^1~4@2$d^1~4").

(* [comment removed for export] *)

End HCW2.


(* [comment removed for export] *)
Ltac sys_nret_raw :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition fixed_shape : ltac2:(zQ "50!h9!t7!o1!ih7!r0>1A$0>1L$0>1r@1$4@1$2#k0>1u$1$3") := ltac2:(zQ "h04!o1!r0!hk3!hj5!t7!ihf!ii6!h9!ila!im5!hjc!hk9!l9!ih7!hoa!r5&@2$3@1$1@1$0#k0@1$5@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\1A$7\1L$7\1r@1$1@1$0#k0\1u$4M4\1u$4$d^1@6$9^2~1~3@3$a~2@4$b@1$1@1$0#k0@1$1@1$0#k0@1$e^4@2$f@1$0#k0@1$c^3~3@1$2$8@1$2@2$3@1$1@1$0#k0$6@6$9^2~1~3~3@1$2$8@1$2@2$3@1$1@1$0#k0$6").

End HCW3.

(* [comment removed for export] *)
