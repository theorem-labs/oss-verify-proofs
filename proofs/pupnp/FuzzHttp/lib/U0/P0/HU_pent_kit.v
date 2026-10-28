From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.

Lemma pe_zx32_lit : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Ltac pe_instr :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w => let d := eval vm_compute in (decode_any w) in
                 lazymatch d with Some (?i, _) => constr:(i) end
    end
  end.

Ltac pe_norm32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_lit e) by lia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (pe_zx32_lit e) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia
  end.

Ltac pe_cstep :=
  let i := pe_instr in
  lazymatch i with
  | Load _ _ _ _ _ => step; try pe_norm32
  | Store _ _ _ _ => step; try fix_lit_store
  | Branch _ _ _ _ => step
  | Op _ _ _ _ => zstep
  | OpImm _ _ _ _ => zstep
  | ShiftImm _ _ _ _ => zstep
  | OpImm32 _ _ _ => zstep; try pe_norm32
  | Op32 _ _ _ _ => zstep; try pe_norm32
  | _ => step
  end.

Ltac pe_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac pe_is_ms := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => idtac end.
Ltac pe_is_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.

Ltac pe_br :=
  first
    [ let K := fresh "K" in if_cases K; zify_cond K; [ first [ (exfalso; lia) | fail 1 ] | ]; try clear K
    | let K := fresh "K" in if_cases K; zify_cond K; [ | exfalso; lia ]; try clear K
    | ubr2
    | ubr3 ].

Ltac pe_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac pe_has_b2z_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => lazymatch c with context [Z.b2z] => idtac end end.

Ltac pe_walk_to p :=
  repeat first [ (pe_is_ms; tryif pe_at p then fail else pe_cstep) | (pe_has_b2z_if; pe_b2z; pe_br) | (pe_is_if; pe_br) ].

Ltac pe_name_reg_val v :=
  repeat lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    match R with context [Z_to_bv 64 ?e] => tryif constr_eq e v then fail else replace e with v by lia end end.
