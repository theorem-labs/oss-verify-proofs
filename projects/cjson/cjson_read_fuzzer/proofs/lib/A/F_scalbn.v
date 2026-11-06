(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgA.A_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition scalbn_entry := 0x92470%Z.
Definition scalbn_tailpc := 0x924ec%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.   (* [comment removed for export] *)
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).

(* [comment removed for export] *)
Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
  if (1023 <? n)%Z then
    let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
    if (1023 <? n)%Z then
      let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
      (y, if (1023 <? n)%Z then 1023%Z else n)
    else (y, n)
  else if (n <? -1022)%Z then
    let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
    if (n <? -1022)%Z then
      let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
      (y, if (n <? -1022)%Z then (-1022)%Z else n)
    else (y, n)
  else (x, n).

Definition scalbn_model (x : word) (n : Z) : word :=
  let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition scalbn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (x : word) (n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (f15 : word) fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             (bvmap_set 10 (scalbn_model x n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scalbn_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (Ft : bvmap 5 word) fc (m : word -> option byte) (n' : Z) (Q : machine_state -> Prop),
  mem_inv asegs m -> frm0 fc -> bv_signed a0 = n' -> (-1022 <= n' <= 1023)%Z ->
  (forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc',
     frm0 fc' ->
     Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           (bvmap_set 10 (fmul_d RNE (reg_get Ft 10) (scalbn_u n')) (bvmap_set 15 (scalbn_u n') Ft))
           (ret_pc ra) fc' None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 Ft (Z_to_bv 64 0x924ec) fc None m (seg_rom asegs)).
Proof. repeat match goal with |- forall (_ : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.Ceil), _ => intro end;
  first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_tail | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_tail as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_tail | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_tail | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgA.A_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
Ltac scalbn_close :=
  intros; unfold scalbn_post;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split;
  [ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
    repeat match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
    end;
    (* [comment removed for export] *)
    repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
    match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
    reflexivity
  | repeat match goal with |- _ /\ _ => split end; assumption ].

Ltac scalbn_go_tail n' :=
  lazymatch goal with
  | |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
      eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
      [ assumption | assumption | | lia | scalbn_close ]
  end.

Lemma scalbn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
  mem_inv asegs m -> frm0 fc -> bv_signed a0 = n -> (-2^31 <= n < 2^31)%Z ->
  evt asegs (scalbn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (reg_get F 10) n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x92470) fc None m (seg_rom asegs)).
Proof. repeat match goal with |- forall (_ : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.Ceil), _ => intro end;
  first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgA.A_img); typeclasses eauto) ]. Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac scalbn_close :=
  intros; unfold scalbn_post;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split;
  [ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
    repeat match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
    end;
    
    repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
    match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
    reflexivity
  | repeat match goal with |- _ /\ _ => split end; assumption ].
Ltac scalbn_go_tail n' :=
  lazymatch goal with
  | |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
      eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
      [ assumption | assumption | | lia | scalbn_close ]
  end.
#[export] Instance A_scalbn_contract : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_contract := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbn.scalbn_contract_ok.
