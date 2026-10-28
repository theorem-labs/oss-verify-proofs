(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_int P_asn1_empty.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_int_loops.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.


Notation ASN1_EMPTY_STACK_A := 48 (only parsing).

Definition asn1_empty_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
    : machine_state -> Prop :=
  fun ms' =>
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-96)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [(bv_unsigned sp - ASN1_EMPTY_STACK_A, bv_unsigned sp)] m m' /\
      wmono segs m m' /\
      mem_inv segs m' /\
      stk segs m' lo (bv_unsigned sp).

Definition asn1_empty_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (PP p lo : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 p)] ->
  0 <= p < 2 ^ 64 ->
  PP mod 8 = 0 -> 0 < PP ->
  (bv_unsigned sp <= PP \/ PP + 8 <= lo) ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_EMPTY_STACK_A -> 4096 <= lo ->
  bv_unsigned sp mod 16 = 0 -> mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  al_wf AL -> cs_ok AL CS -> abase segs AL m -> aobj segs AL CS m PP 8 -> crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 p ->
  evtA segs AL CS (asn1_empty_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.

  #[using="IMG"] Lemma A_asn1_get_tag_empty_walk : asn1_empty_stmtA asegs AL A_ASN1_GET_TAG.
  Proof.
    unfold asn1_empty_stmtA, A_ASN1_GET_TAG.
    intros until lo; intros HPP PB AL1 NZ DJ ST SLO LO4 SPA MI RA ALWF CSOK AB OPP SCS -> ->.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB; cbn [cells_size csize Nat.add] in PPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    pose proof (munch_refl [(bv_unsigned sp - ASN1_EMPTY_STACK_A, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lx_pre.
    lx_run_tac (PLAN [] [] 200%N).
    lx_tree.
    lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: try lx_arith.
  Qed.

  #[using="IMG"] Lemma A_asn1_get_int_empty_walk : asn1_empty_stmtA asegs AL A_ASN1_GET_INT.
  Proof.
    unfold asn1_empty_stmtA, A_ASN1_GET_INT.
    intros until lo; intros HPP PB AL1 NZ DJ ST SLO LO4 SPA MI RA ALWF CSOK AB OPP SCS -> ->.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB; cbn [cells_size csize Nat.add] in PPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    pose proof (munch_refl [(bv_unsigned sp - ASN1_EMPTY_STACK_A, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lx_pre.
    lx_run_tac (PLAN [] [] 200%N).
    lx_tree.
    lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: try lx_arith.
  Qed.
End Walk.

Lemma A_asn1_get_tag_empty : forall AL, asan_img_ok AL -> asn1_empty_stmtA asegs AL A_ASN1_GET_TAG.
Proof. exact A_asn1_get_tag_empty_walk. Qed.
Lemma A_asn1_get_int_empty : forall AL, asan_img_ok AL -> asn1_empty_stmtA asegs AL A_ASN1_GET_INT.
Proof. exact A_asn1_get_int_empty_walk. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
