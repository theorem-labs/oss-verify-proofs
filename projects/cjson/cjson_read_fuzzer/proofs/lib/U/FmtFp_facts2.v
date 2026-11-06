(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_letf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgU.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_FmtFp_facts2.
Module F_frexpl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_letf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers2.SF_buildtac.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_letf2.U_letf2_contract.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

Definition frexpl_entry := 0x1ba0c%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma frexpl_unfold : forall n x e,
  frexpl (S n) x e =
   (let hi := hi64 x in
    let se := Z.shiftr hi 48 in
    let ee := Z.land se 0x7fff in
    if ee =? 0 then
      if negb (f128_le x F128_ZERO =? 0) then
        let k := f128_of_d D_0x1p120 in
        match frexpl n (f128_mul x k) e with Some (x, e) => Some (x, e - 120) | None => None end
      else Some (x, 0)
    else if ee =? 0x7fff then Some (x, e)
    else
      let e := ee - 0x3ffe in
      let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff)) 0x3ffe000000000000 in
      Some (mk128 hi (lo64 x), e))%Z.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_unfold | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_unfold as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_unfold | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_unfold | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
Definition frexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (bv_unsigned sp - 32) (bv_unsigned sp)
    /\ rw_cells usegs m' P [C4 (Z_to_bv 64 e')]
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Ltac frx_finish X E' :=
  apply evt_done; unfold frexpl_post; exists X, E';
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
         | repeat match goal with |- _ /\ _ => split end; try assumption ].
Lemma f128_le_land64_zero : forall a b, Z.land (f128_le a b) 18446744073709551615 = 0%Z <-> f128_le a b = 0%Z.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.f128_le_land64_zero | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.f128_le_land64_zero as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.f128_le_land64_zero | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.f128_le_land64_zero | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.f128_le_land64_zero OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Lemma frexpl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
  stk usegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
  mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
  (bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (32 <= bv_unsigned sp)%Z ->
  (let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
   Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
  evt usegs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ba0c) fc None m (seg_rom usegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
#[export] Instance U_frexpl_contract : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_contract := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_contract_ok.
End F_frexpl.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Module FmtFp_facts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import F_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


#[local] Existing Instances F_frexpl.U_frexpl_contract.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


(* [comment removed for export] *)
Fixpoint fmt_fp_dn_iter (n : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct n} : option (list Z * Z * Z * Z) :=
  match n with
  | O => Some s
  | S n' => let '(big, a, z, e2) := s in
            if e2 <? 0 then match fmt_fp_dn_body p t r s with Some s' => fmt_fp_dn_iter n' p t r s' | None => None end
            else None
  end.

(* [comment removed for export] *)
Definition dn_ok (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in (a <= z <= 127)%Z /\ (a = z -> znth big a <> 0%Z).

Definition dn_good (p t r : Z) (s : list Z * Z * Z * Z) : Prop :=
  forall n big a z e2, fmt_fp_dn_iter n p t r s = Some (big, a, z, e2) -> (e2 < 0)%Z -> dn_ok (big, a, z, e2).

(* [comment removed for export] *)
Definition dn_a1 (bigI : list Z) (a : Z) : Z := if znth bigI a =? 0 then a + 1 else a.
Definition dn_bz (bigI : list Z) (z cI : Z) : list Z * Z := if negb (cI =? 0) then (zupd bigI z cI, z + 1) else (bigI, z).
Definition dn_zf (t r need a1 z1 : Z) : Z :=
  let b := if Z.lor t 32 =? CHR_f then r else a1 in if need <? z1 - b then b + need else z1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_from (big : list Z) (z : Z) : Prop := forall i, (z <= i)%Z -> znth big i = 0%Z.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dig_words_fact (yv fl : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y',
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    (z' <= (if e2 <? 0 then 0 else 122) + 6)%Z.

(* [comment removed for export] *)
Definition e2_range_fact (yv fl : Z) : Prop :=
  forall y1 fr e0,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     let e2 := if ynz then e0 - 1 - 28 else e0 in
     -1102 <= e2 <= 1024)%Z.

(* [comment removed for export] *)
Definition dn_phase_fact (yv fl p t : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y' s,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    fmt_fp_up UP_FUEL (b', (if e2 <? 0 then 0 else 122)%Z, z', e2) = Some s ->
    dn_good (if p <? 0 then 6 else p)%Z t (if e2 <? 0 then 0 else 122)%Z s.
End FmtFp_facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
Import FmtFp_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


(* [comment removed for export] *)
Definition run_to_dn (yv fl p t : Z) (p1 r0 : Z) (big : list Z) (a z : Z) : Prop :=
  exists y1 fr e0 y e2 b' z' y' s e2',
    fst (fst (ffp_sign yv fl)) = y1 /\
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) /\
    p1 = (if p <? 0 then 6 else p) /\ r0 = (if e2 <? 0 then 0 else 122) /\
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, r0, y) = Some (b', z', y') /\
    fmt_fp_up UP_FUEL (b', r0, z', e2) = Some s /\
    fmt_fp_dn DN_FUEL p1 t r0 s = Some (big, a, z, e2').

(* [comment removed for export] *)
Definition words_all_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall i, 0 <= znth big i < 1000000000.

(* [comment removed for export] *)
Definition carry_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    0 <= aR.

(* [comment removed for export] *)
Definition azr_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR zS,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    fmt_fp_strip BIG_FUEL bigR aR zR = Some zS ->
    Z.lor t 32 <> CHR_f -> zS <= aR -> aR = r0.

(* [comment removed for export] *)
Definition yn_fact (y : Z) : Prop :=
  Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0 \/ f128_le y F128_ZERO = 0.

(* [comment removed for export] *)
Definition below_a_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall k, 0 <= k < a -> znth big k = 0.
