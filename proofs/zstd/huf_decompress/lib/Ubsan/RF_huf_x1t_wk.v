From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_h_iface.
Import ListNotations.
Open Scope Z_scope.

Lemma x1w_zx32 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Ltac x1w_inr := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
  let d := eval vm_compute in ((PHUF_RDT_X1 <=? z) && (z <? PHUF_RDT_X1 + 3064))%bool in
  lazymatch d with true => idtac | false => fail end end.
Ltac x1w_zbr := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | _ => x1w_inr; zstep end).
Ltac x1w_zto o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PHUF_RDT_X1 + o) in lazymatch d with true => fail | false => zstep end
  | _ => zstep end).
Ltac x1w_dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  tryif (match c with context [?v] => is_var v end) then fail else
  let b := eval vm_compute in c in change c with b; cbv iota end.
Ltac x1w_norm := repeat (first [ rewrite x1w_zx32 by lia | rewrite sx32_small by lia | rewrite unsigned_lit by lia
                               | rewrite swrap32_small by lia | rewrite zb_lxor_ones by lia | rewrite Z.add_0_r ]).
Ltac x1w_bfacts := repeat (match goal with H : context [Z.lxor ?a ?b] |- _ =>
  lazymatch goal with _ : 0 <= Z.lxor a b |- _ => fail | _ => assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia) end end).
Ltac x1w_hnorm U := repeat (first [ rewrite signed_lit in U by lia | rewrite unsigned_lit in U by lia ]).
Ltac x1w_hnorm_t U := try x1w_hnorm U.
Ltac x1w_ck := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
  first [ let d := eval vm_compute in (a =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "CK" in if_cases U; zify_cond U; [ exfalso; x1w_hnorm U; x1w_bfacts; lia | ] end
        | let d := eval vm_compute in (b =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "CK" in if_cases U; zify_cond U; [ | exfalso; x1w_hnorm U; x1w_bfacts; lia ] end ] end.
Ltac x1w_walk := repeat (x1w_zbr; x1w_norm; first [ x1w_dec_if | x1w_ck ]).
Ltac x1w_decl := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  first [ let U := fresh "BR" in if_cases U; zify_cond U; x1w_hnorm_t U; [ exfalso; lia | ]
        | let U := fresh "BR" in if_cases U; zify_cond U; x1w_hnorm_t U; [ | exfalso; lia ] ] end.
Ltac x1w_walkd := repeat (x1w_zbr; x1w_norm; first [ x1w_dec_if | x1w_ck | x1w_decl ]).
Ltac x1w_br U := if_cases U; zify_cond U; x1w_hnorm U.
