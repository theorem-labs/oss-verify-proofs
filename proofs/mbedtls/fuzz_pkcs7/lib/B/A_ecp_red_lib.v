(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Open Scope Z_scope.

(* [comment removed for export] *)
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
Lemma grow_R_keep : forall nb dX LB LB' r dX', grow_R nb dX LB r dX' -> mpd_out LB dX LB' dX' -> binop_keep LB dX dX'.
Proof.
  (intros nb dX LB LB' r dX' dd_H; ddestruct dd_H as [[(_ & _ & Hn & Hp & _ & _)|[_ ->]] FR]; intros (EA & _)).
  - split; [exact EA|]. split; [exact Hp|]. split; [exact FR|]. rewrite Hn. lia.
  - split; [reflexivity|]. split; [reflexivity|]. split; [exact FR|]. lia.
Qed.

Definition A_ASAN_MEMSET_EC : Z := 0x68258.   (* [comment removed for export] *)
Definition red_frame40 (ra s0 s1 s2 s3 : word) : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Ltac wrq H L idx :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l idx _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
        let E := addr_expr a in
        pose proof (u32arr_write sg mm A l idx v H ltac:(lia)) as H';
        try (replace (A + 4 * idx)%Z with E in H' by lia);
        store_done; try clear H; rename H' into H;
        let l1 := fresh "ws" in let EE := fresh "E" in let L1 := fresh "L" in
        remember (upd l (Z.to_nat idx) v) as l1 eqn:EE;
        lazymatch type of L with _ = ?r => assert (L1 : Z.of_nat (length l1) = r) by (rewrite EE, upd_length; exact L) end;
        clear L EE; rename L1 into L; try clear l
      end
  end.

(* [comment removed for export] *)
Ltac rdq H idx RD :=
  let w := fresh "w" in let NE := fresh "NE" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat idx)) as [w|] eqn:NE; [| exfalso; apply nth_error_None in NE; lia];
      pose proof (u32arr_read sg mm A l idx w _ H NE ltac:(lia) ltac:(f_equal; lia)) as RD; clear NE
  end.

(* [comment removed for export] *)
Ltac split3 H iI kK PUlo PUmid PUtop :=
  lazymatch type of H with u32arr ?sg ?mm ?pp ?l =>
    let PU := fresh "PU" in
    pose proof H as PU;
    rewrite <- (firstn_skipn (Z.to_nat iI) l) in PU; apply u32arr_app in PU; destruct PU as [PUlo PU];
    rewrite firstn_length_le in PU by lia;
    rewrite <- (firstn_skipn (Z.to_nat kK) (skipn (Z.to_nat iI) l)) in PU; apply u32arr_app in PU; destruct PU as [PUmid PUtop];
    rewrite firstn_length_le in PUtop by (rewrite length_skipn; lia)
  end.
