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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_leaves_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma aceil : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac pc end.

(* [comment removed for export] *)
Ltac if_lia := let K := fresh "K" in (if_cases K; zify_cond K); [ first [exfalso; lia | clear K] | first [exfalso; lia | clear K] ].

(* [comment removed for export] *)
Ltac leaf_prep :=
  cbv beta delta [wz] in *; unfold ATP in *;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP
  end;
  idtac.

(* [comment removed for export] *)
Lemma RTREP_high : forall st W m m', RTWF st -> Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W ->
  munch W m m' -> wmono asegs m m' -> RTREP st m -> RTREP st m'.
Proof. intros st W m m' WF HW MU WM HR. eapply (RTREP_stack_frame st WF W); [exact HW| exact MU| exact WM| exact HR]. Qed.
Ltac rtrep_high HR WF MU WM :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of HR with RTREP ?st m =>
      apply (RTREP_high st W m m' WF) in HR; [| repeat (constructor; [cbn; lia|]); constructor | exact MU | exact WM ]
    end end.

(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lia | rewrite ?unsigned_lit by lia; lia | split; [first [lia | rewrite ?unsigned_lit by lia; lia] | exact I] ].

(* [comment removed for export] *)
Ltac restk :=
  repeat match goal with H : stk _ ?mm ?lo ?x, H' : stk _ ?mm' ?lo ?x' |- _ => constr_eq mm mm'; clear H' end;
  match goal with H : stk _ _ _ _ |- _ => rename H into ST end.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac pr r := let v := reg_val r in idtac r "=" v.

(* [comment removed for export] *)
Ltac is_Zlit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  | |- context [Z.eqb ?x ?y] => is_Zlit x; is_Zlit y;
      let b := eval vm_compute in (Z.eqb x y) in change (Z.eqb x y) with b; cbv iota
  end.
Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
Ltac fixMI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  match goal with H : mem_inv _ mm |- _ => try rename H into MI end end.
Ltac after_call :=
  cbv beta delta [wz] in *;
  repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end;
  restk; fixMI.

(* [comment removed for export] *)
Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
Ltac unhide H := unfold id in H.
Ltac recell H MU := unfold id in H; eapply (ro_cells_transport asegs _ _ _) in H; [| exact MU| cbn; lia].

(* [comment removed for export] *)
Lemma swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.pow]. change (2^Z.of_N 32) with 4294967296. change (Z.of_N 32 - 1) with 31. rewrite Z.mod_small; lia. Qed.
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_small. exact Hz. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ctx_range : forall st, RTWF st -> oclr (st_ctx st) (st_ctx st + 160) /\ st_ctx st + 160 <= alloc_ceiling.
Proof.
  intros st WF. destruct (wb_ctx_loose st (wf_base_ok st WF)) as (b & k & HIn & H1 & H2).
  destruct (loose0_range st WF b k HIn) as (R1 & R2 & R3 & R4).
  split; [apply (oclr_sub _ _ _ _ R1); lia| lia].
Qed.

(* [comment removed for export] *)
Lemma leaf_cells : forall st m, RTREP st m ->
  ro_cells asegs m 0xaaf58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xaaf7c [C4 (Z_to_bv 64 30)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa9adc [C1 (Z_to_bv 8 1)]                                    (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa9ae0 [C1 (Z_to_bv 8 1)]                                    (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa9ae4 [C4 (Z_to_bv 64 0)]                                    (* [comment removed for export] *)
  /\ ro_cells asegs m 0x12c4e1 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13bd40 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5dd260 [C4 (Z_to_bv 64 0)]                                    (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2bd8 [C8 (Z_to_bv 64 0x10)]                                 (* [comment removed for export] *)
  /\ ro_cells asegs m 6148600 [C8 (Z_to_bv 64 0x5fe5f8)]                              (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5fe5f8 [C8 (Z_to_bv 64 (st_ctx st))]                          (* [comment removed for export] *)
  /\ rw_cells asegs m (st_ctx st + 152) [C8 (Z_to_bv 64 (st_t st))].                  (* [comment removed for export] *)
Proof.
  intros st m HR.
  pose proof (rr_consts st m HR) as HC. pose proof (rr_thread st m HR) as HT.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & K11 & K12 & K13 & K14 & _ & _ & _ & K18 & K19 & _).
  destruct HT as (_ & _ & _ & _ & _ & T6 & T7 & T8 & _).
  split; [exact K9|]. split; [exact K10|]. split; [exact K11|]. split; [exact K12|]. split; [exact K13|]. split; [exact K14|].
  split; [exact K18|]. split; [exact K19|].
  split; [apply (R_link_at m 0xa2bd8 0x10 (rr_link st m HR)); vm_compute; reflexivity|].
  split; [exact T7|]. split; [exact T8|]. exact T6.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac pc end.
Ltac if_lia := let K := fresh "K" in (if_cases K; zify_cond K); [ first [exfalso; lia | clear K] | first [exfalso; lia | clear K] ].
Ltac leaf_prep :=
  cbv beta delta [wz] in *; unfold ATP in *;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP
  end;
  idtac.
Ltac rtrep_high HR WF MU WM :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of HR with RTREP ?st m =>
      apply (RTREP_high st W m m' WF) in HR; [| repeat (constructor; [cbn; lia|]); constructor | exact MU | exact WM ]
    end end.
Ltac slia ::= first [ exact I | lia | rewrite ?unsigned_lit by lia; lia | split; [first [lia | rewrite ?unsigned_lit by lia; lia] | exact I] ].
Ltac restk :=
  repeat match goal with H : stk _ ?mm ?lo ?x, H' : stk _ ?mm' ?lo ?x' |- _ => constr_eq mm mm'; clear H' end;
  match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac pr r := let v := reg_val r in idtac r "=" v.
Ltac is_Zlit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  | |- context [Z.eqb ?x ?y] => is_Zlit x; is_Zlit y;
      let b := eval vm_compute in (Z.eqb x y) in change (Z.eqb x y) with b; cbv iota
  end.
Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.
Ltac fixMI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  match goal with H : mem_inv _ mm |- _ => try rename H into MI end end.
Ltac after_call :=
  cbv beta delta [wz] in *;
  repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end;
  restk; fixMI.
Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
Ltac unhide H := unfold id in H.
Ltac recell H MU := unfold id in H; eapply (ro_cells_transport asegs _ _ _) in H; [| exact MU| cbn; lia].
End RTW_leaves_lib.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Module RTW_depot_hash.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma MM_M_val : MM_M = 14313749767032793493. Proof. reflexivity. Qed.

Lemma trace_cells_size : forall tr, Z.of_nat (cells_size (trace_cells tr)) = 8 * zlen tr.
Proof. unfold trace_cells, zlen. induction tr as [|x tr IH]; [reflexivity|]. cbn [map cells_size Cells.csize length]. lia. Qed.

Lemma h0_code : forall n, 0 <= n ->
  Z.lxor ((n * 3829533694005038248) mod 18446744073709551616) 10900877739976798860 = Z.lxor MM_SEED (w64 (8 * n * MM_M)).
Proof.
  intros n Hn. unfold w64. rewrite MM_M_val. unfold MM_SEED. change (2^64) with 18446744073709551616. rewrite Z.lxor_comm. f_equal.
  replace 3829533694005038248 with ((8 * 14313749767032793493) mod 18446744073709551616) by reflexivity.
  rewrite Z.mul_mod_idemp_r by lia. f_equal. lia.
Qed.

Lemma mm_add_range : forall h w, 0 <= mm_add h w < 2^64.
Proof. intros. unfold mm_add, w64. apply Z.mod_pos_bound. lia. Qed.
Lemma mm_fold_range : forall l h, 0 <= h < 2^64 -> 0 <= fold_left mm_add l h < 2^64.
Proof. induction l as [|w l IH]; intros h Hh; cbn; [exact Hh| apply IH; apply mm_add_range]. Qed.

Lemma mm_add_code : forall h w,
  Z_to_bv 64 (Z.lxor ((Z.lxor (Z.shiftr ((w * 14313749767032793493) mod 18446744073709551616) 47)
                               ((w * 14313749767032793493) mod 18446744073709551616) * 14313749767032793493) mod 18446744073709551616) h
              * 14313749767032793493)
  = Z_to_bv 64 (mm_add h w).
Proof.
  intros h w. unfold mm_add, w64. rewrite MM_M_val. change (2^64) with 18446744073709551616.
  rewrite (Z.lxor_comm (Z.shiftr _ 47)). rewrite (Z.lxor_comm h). symmetry. apply Z_to_bv_mod64.
Qed.

Lemma mm_add_zero_code : forall h, Z_to_bv 64 (Z.lxor 0 h * 14313749767032793493) = Z_to_bv 64 (mm_add h 0).
Proof.
  intros h. unfold mm_add, w64. rewrite MM_M_val. change (2^64) with 18446744073709551616.
  rewrite Z.mul_0_l. cbn -[Z.mul Z.lxor Z.modulo Z_to_bv]. change (0 mod 18446744073709551616) with 0. cbn -[Z.mul Z.lxor Z.modulo Z_to_bv].
  change ((0 * 14313749767032793493) mod 18446744073709551616) with 0.
  rewrite Z.lxor_0_r, Z.lxor_0_l. symmetry. apply Z_to_bv_mod64.
Qed.

Lemma mm_fin_code : forall h, 0 <= h < 2^64 ->
  Z.lxor (Z.shiftr ((Z.lxor (Z.shiftr h 47) h * 14313749767032793493) mod 18446744073709551616) 47)
         ((Z.lxor (Z.shiftr h 47) h * 14313749767032793493) mod 18446744073709551616)
  = mm_fin h.
Proof.
  intros h Hh. unfold mm_fin, w64. rewrite MM_M_val. change (2^64) with 18446744073709551616.
  rewrite (Z.lxor_comm (Z.shiftr h 47)). rewrite (Z.lxor_comm (Z.shiftr _ 47)). reflexivity.
Qed.

Lemma mm_fin_range : forall h, 0 <= h < 2^64 -> 0 <= mm_fin h < 2^64.
Proof.
  intros h Hh. unfold mm_fin, w64. apply zr_lxor; [apply zr_mod64|]. apply zr_shiftr; [apply zr_mod64| lia].
Qed.
Lemma bucket_code : forall h, 0 <= h < 2^64 -> Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = 4 * dbucket h.
Proof.
  intros h Hh. unfold dbucket, DEPOT_TAB_LOG. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^20 * 2^44). rewrite Z.mul_mod_distr_r by lia.
  Z.div_mod_to_equations. nia.
Qed.

Section HASH.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (P : Z) (tr : list Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TRR : Forall (fun pc => 0 <= pc < 2^64) tr.
  Hypothesis PB : 0 <= P /\ P + 8 * zlen tr < 2^64.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation ST_ pc q h x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 q) (Z_to_bv 64 h) a3
              (Z_to_bv 64 (P + 8 * zlen tr)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma hash_loop : forall rest done (h q : Z) x15 x16,
    tr = done ++ rest -> rest <> [] -> 0 <= h < 2^64 -> q = P + 8 * zlen done ->
    ro_cells asegs m q (trace_cells rest) ->
    evt asegs (fun ms' => exists x15' x16', ms' = ST_ 0x7444c (P + 8 * zlen tr) (fold_left mm_add rest h) x15' x16')
        (ST_ 0x74428 q h x15 x16).
  Proof.
    induction rest as [|w rest IH]; intros done h q x15 x16 HTR NE Hh HQ CELLS; [congruence|].
    assert (HW : 0 <= w < 2^64) by (rewrite HTR in TRR; apply Forall_app in TRR; destruct TRR as [_ T2]; inversion T2; assumption).
    assert (LD : zlen tr = zlen done + 1 + zlen rest) by (rewrite HTR, zlen_app, zlen_cons; lia).
    pose proof (zlen_nonneg done) as Z1. pose proof (zlen_nonneg rest) as Z2.
    unfold trace_cells in CELLS. cbn [map] in CELLS. cbv delta [wz] in CELLS.
    do 8 zstep. rewrite mm_add_code.
    zstep. (if_cases K; zify_cond K).
    - (* [comment removed for export] *)
      destruct rest as [|w' rest']. { exfalso. rewrite zlen_nil in *. lia. }
      eapply (IH (done ++ [w])); [rewrite HTR, <- app_assoc; reflexivity| congruence| | rewrite zlen_app, zlen_cons, zlen_nil; lia|].
      + unfold mm_add, w64. apply Z.mod_pos_bound. lia.
      + apply (proj1 (cells_at_app m q [C8 (Z_to_bv 64 w)] (trace_cells (w' :: rest'))) ) in CELLS.
        destruct CELLS as [_ CELLS]. cbn [cells_size Cells.csize Nat.add] in CELLS.
        replace (P + 8 * zlen (done ++ [w])) with (q + Z.of_nat 8) by (rewrite zlen_app, zlen_cons, zlen_nil; lia). exact CELLS.
    - (* [comment removed for export] *)
      destruct rest as [|w' rest']. 2:{ exfalso. rewrite zlen_cons in *. pose proof (zlen_nonneg rest'). lia. }
      cbn [fold_left]. apply evt_done. eexists _, _. rewrite <- K. reflexivity.
  Qed.

End HASH.

Section PUTA.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (P : Z) (tr : list Z) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TRR : Forall (fun pc => 0 <= pc < 2^64) tr.
  Hypothesis TRL : 1 <= zlen tr <= 30.
  Hypothesis PB : 0 < P /\ P + 8 * zlen tr < 2^64.
  Hypothesis CELLS : ro_cells asegs m P (trace_cells tr).
  Hypothesis PSEP : P + 8 * zlen tr <= bv_unsigned sp - 112 \/ bv_unsigned sp <= P.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : 0 <= lo /\ lo + 112 <= bv_unsigned sp.

  (* [comment removed for export] *)
  Lemma put_A : forall (Q : machine_state -> Prop),
    (forall (x10 x11 x12 x14 x15 x16 : word) m1 (junk : list byte),
       rw_cells asegs m1 (bv_unsigned sp + -112)
         [CB 8 junk; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (zlen tr)); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       mem_inv asegs m1 -> munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
       stk asegs m1 lo (bv_unsigned sp + -112) ->
       evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_DEPOT) x10 x11
                         x12 (Z_to_bv 64 0x400000) x14 x15 x16 a7
                         (Z_to_bv 64 (A_DEPOT + 4 * dbucket (trace_hash tr))) (Z_to_bv 64 (trace_hash tr)) s4 s5
                         (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x74498) fc None m1 (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_DEPOT) (Z_to_bv 64 P) (Z_to_bv 64 (zlen tr)) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x74398) fc None m (seg_rom asegs)).
  Proof.
    intros Q K. pose proof ST as ST1.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (zlen_nonneg tr) as Z0.
    pose proof CELLS as TC. change (ro_cells asegs m P (trace_cells tr)) with (id (ro_cells asegs m P (trace_cells tr))) in TC. clear CELLS.
    unfold A_DEPOT in *.
    carve_frame 112%nat ST1.
    do 12 zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. rewrite swrap32_small by lia. zstep.
    zstep. if_lia. zstep. if_lia.
    zstep. setreg 13 (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    zstep. zstep. zstep. zstep. zstep. fl. zstep.
    setreg 12 (Z_to_bv 64 (zlen tr)) ltac:(f_equal; change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. zstep. fl. zstep. fl.
    zstep. zstep. zstep. zstep.
    setreg 12 (Z_to_bv 64 (Z.lxor MM_SEED (w64 (8 * zlen tr * MM_M)))) ltac:(f_equal; symmetry; apply h0_code; lia).
    setreg 14 (Z_to_bv 64 (P + 8 * zlen tr)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TC1 : ro_cells asegs mm P (trace_cells tr))
        by (unfold id in TC; eapply (ro_cells_transport asegs _ m mm); [exact TC| exact MU|]; rewrite trace_cells_size; cbn; lia) end.
    eapply evt_cut.
    { eapply (hash_loop _ _ gp tp t0 t1 t2 _ _ _ a7 _ _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ P tr TRR ltac:(lia) tr [] _ P);
        [reflexivity| destruct tr; [unfold zlen in TRL; cbn in TRL; lia| congruence]| | unfold zlen; cbn [length]; lia | exact TC1].
      apply zr_lxor; [apply zr_lit; unfold MM_SEED; lia| apply zr_mod64]. }
    cbv beta. intros ms' (x15' & x16' & ->).
    pose proof (mm_fold_range tr (Z.lxor MM_SEED (w64 (8 * zlen tr * MM_M))) ltac:(apply zr_lxor; [apply zr_lit; unfold MM_SEED; lia| apply zr_mod64])) as FR1.
    set (h1 := fold_left mm_add tr (Z.lxor MM_SEED (w64 (8 * zlen tr * MM_M)))) in *.
    do 11 zstep. rewrite mm_add_zero_code.
    pose proof (mm_add_range h1 0) as FR2. set (h2 := mm_add h1 0) in *.
    do 5 zstep. rewrite mm_fin_code by exact FR2.
    pose proof (mm_fin_range h2 FR2) as FR3. set (h3 := mm_fin h2) in *.
    zstep. zstep. rewrite bucket_code by exact FR3. zstep.
    assert (EH : h3 = trace_hash tr) by (subst h3 h2 h1; reflexivity).
    clearbody h3. subst h3.
    eapply K; [exact FR| | exact MU| exact WM| exact ST1]. assumption.
  Qed.
End PUTA.


End CeilWrap.
End RTW_depot_hash.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
Module RTW_depot_lock.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac amo_sym2 :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      replace (amo_aligned wd a) with true by (symmetry; apply amo_aligned_wz; [lia| cbn [amo_bytes]; first [assumption| lia]]);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity| f_equal; word_eq_tac| lia]); cbv iota
  end.
Ltac amo_step_core2 segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; amo_sym2; exec_cbv; amo_sym2; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; refold_mkR ]
      end
  end.
Ltac amo_zstep2 :=
  cbv beta delta [wz];
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => amo_step_core2 segs R F pc fc rv m ro
  end; zsimp.

Section LOCK.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (p v lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis HP : 0 <= p /\ p + 4 <= alloc_ceiling /\ p mod 4 = 0.
  Hypothesis HV : 0 <= v < 2^31.
  Hypothesis TB : rw_cells asegs m p [C4 (Z_to_bv 64 v)].
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 48 <= bv_unsigned sp.

  Lemma lock_spec : forall (Q : machine_state -> Prop),
    (forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m',
       rw_cells asegs m' p [C4 (Z_to_bv 64 (Z.lor v 18446744071562067968))] ->
       mem_inv asegs m' -> munch [(bv_unsigned sp - 48, bv_unsigned sp); (p, p + 4)] m m' -> wmono asegs m m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       evt asegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x74b0c) fc None m (seg_rom asegs)).
  Proof.
    intros Q K. pose proof ST as ST1.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (p, p + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    assert (AL : p mod 4 = 0) by lia. assert (PR : 0 <= p < 2^64) by lia.
    carve_frame 48%nat ST1.
    do 6 zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 v) ltac:(symmetry; unfold sx32; f_equal; rewrite unsigned_lit by lia; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                                  cbn -[Z.add Z.sub Z.modulo Z.pow]; change (2^Z.of_N 32) with 4294967296; change (Z.of_N 32 - 1) with 31; rewrite Z.mod_small; lia).
    zstep. if_lia. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    amo_zstep. (* [comment removed for export] *)
    setreg 13 (Z_to_bv 64 v) ltac:(symmetry; unfold sx32; f_equal; rewrite unsigned_lit by lia; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                                  cbn -[Z.add Z.sub Z.modulo Z.pow]; change (2^Z.of_N 32) with 4294967296; change (Z.of_N 32 - 1) with 31; rewrite Z.mod_small; lia).
    zstep. if_lia. (* [comment removed for export] *)
    amo_zstep2. fix_lit_store. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    do 7 zstep.
    release_frame FR ST1 (bv_unsigned sp).
    eapply K; [exact TB| exact MI| exact MU| exact WM| exact ST1].
  Qed.
End LOCK.


End CeilWrap.
(* [comment removed for export] *)
Ltac amo_sym2 :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      replace (amo_aligned wd a) with true by (symmetry; apply amo_aligned_wz; [lia| cbn [amo_bytes]; first [assumption| lia]]);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity| f_equal; word_eq_tac| lia]); cbv iota
  end.
Ltac amo_step_core2 segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; amo_sym2; exec_cbv; amo_sym2; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; refold_mkR ]
      end
  end.
Ltac amo_zstep2 :=
  cbv beta delta [wz];
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => amo_step_core2 segs R F pc fc rv m ro
  end; zsimp.
End RTW_depot_lock.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
Module RTW_depot_memcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma ro_C1_of_bytes_at : forall m A bs (i : Z) b,
  bytes_at asegs m A bs -> nth_error bs (Z.to_nat i) = Some b -> 0 <= i -> ro_cells asegs m (A + i) [C1 b].
Proof.
  intros m A bs i b (HA & HL & HB) Hn Hi. pose proof (nth_error_lt _ _ _ Hn) as LT.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|].
  intros j Hj. cbn in Hj. assert (j = 0)%nat by lia. subst j. cbn [nth_error].
  replace (A + i + Z.of_nat 0) with (A + Z.of_nat (Z.to_nat i)) by lia. rewrite HB by lia. exact Hn.
Qed.

Section MEMCPY.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S n : Z) (sbs : list byte).
  Hypothesis Rn : 1 <= n.
  Hypothesis DB : 0 <= D /\ D + n < 2^64.
  Hypothesis SBR : 0 <= S /\ S + n <= 2^64.
  Hypothesis DISJ : S + n <= D \/ D + n <= S.
  Hypothesis SRC : bytes_at asegs m S sbs.
  Hypothesis SLEN : length sbs = Z.to_nat n.

  #[warnings="-notation-for-abbreviation"] Notation ST_ pc mm x11 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) x11 (Z_to_bv 64 (D + n)) x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma imemcpy_loop : forall (K : nat) (i : Z) (m1 : word -> option byte) (bs : list byte) x14 (Q : machine_state -> Prop) (cs cd : Z),
    Z.to_nat (n - i) = K -> 0 <= i < n -> cs = S + i -> cd = D + i ->
    u8arr asegs m1 D bs -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch [(D, D + n)] m m1 -> wmono asegs m m1 ->
    (forall m2 bs2 x14', u8arr asegs m2 D bs2 -> length bs2 = Z.to_nat n -> mem_inv asegs m2 -> munch [(D, D + n)] m m2 -> wmono asegs m m2 ->
       evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + n)) x14' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
    evt asegs Q (ST_ 0x657a4 m1 (Z_to_bv 64 cs) (Z_to_bv 64 cd) x14).
  Proof using Rn DB SBR DISJ SRC SLEN.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs x14 Q cs cd HK Hi -> -> ARR LEN MI MU WM HQ.
    (* [comment removed for export] *)
    assert (SRC1 : bytes_at asegs m1 S sbs).
    { eapply bytes_at_transport; [exact SRC| exact MU|]. rewrite SLEN. cbn. lia. }
    destruct (nth_error sbs (Z.to_nat i)) as [b|] eqn:Hb.
    2:{ exfalso. apply nth_error_None in Hb. lia. }
    destruct (ex_intro (fun q => q = S + i) _ eq_refl) as [q Hq].
    pose proof (ro_C1_of_bytes_at m1 S sbs i b SRC1 Hb ltac:(lia)) as CELL. rewrite <- Hq in CELL.
    replace (Z_to_bv 64 (S + i)) with (Z_to_bv 64 q : word) by (f_equal; exact Hq).
    zstep. (* [comment removed for export] *)
    clear CELL.
    pose proof (u8arr_store_ok asegs _ D bs i (wa (D + i)) ARR ltac:(rewrite LEN; lia) eq_refl) as SOK.
    zstep. (* [comment removed for export] *)
    assert (Eb : le1 (Z_to_bv 64 (bv_unsigned b)) = [b]).
    { rewrite le1_byte. f_equal. rewrite unsigned_lit by (pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
      rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
      apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
    rewrite Eb. clear Eb.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u8arr_write asegs mm D bs i b ARR ltac:(rewrite LEN; lia)) as ARR' end.
    store_done.
    zstep. zstep. (* [comment removed for export] *)
    replace (Z_to_bv 64 (q + 1)) with (Z_to_bv 64 (S + (i + 1)) : word) by (f_equal; lia).
    replace (D + i + 1) with (D + (i + 1)) by lia.
    zstep. (if_cases KK; zify_cond KK).
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity| lia| reflexivity| reflexivity| exact ARR'| rewrite upd_length; exact LEN| exact MI| exact MU| exact WM| exact HQ].
    - assert (i + 1 = n) by lia. replace (i + 1) with n by lia.
      zstep. (* [comment removed for export] *)
      eapply HQ; [exact ARR'| rewrite upd_length; exact LEN| exact MI| exact MU| exact WM].
  Qed.

  Lemma imemcpy_spec : forall (bs : list byte) x13 x14 (Q : machine_state -> Prop),
    u8arr asegs m D bs -> length bs = Z.to_nat n -> mem_inv asegs m ->
    (forall m2 bs2 x14', u8arr asegs m2 D bs2 -> length bs2 = Z.to_nat n -> mem_inv asegs m2 -> munch [(D, D + n)] m m2 -> wmono asegs m m2 ->
       evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + n)) x14' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x65798) fc None m (seg_rom asegs)).
  Proof using Rn DB SBR DISJ SRC SLEN.
    intros bs x13 x14 Q ARR LEN MI HQ.
    pose proof (munch_refl [(D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. if_lia. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    eapply (imemcpy_loop (Z.to_nat n) 0); [lia| lia| lia| lia| exact ARR| exact LEN| exact MI| exact MU| exact WM| exact HQ].
  Qed.
End MEMCPY.


End CeilWrap.
End RTW_depot_memcpy.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_depot_mmap.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition mmap_consts (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1f60 [C8 (Z_to_bv 64 0x139d20)] /\ ro_cells asegs m 0x139d20 [C8 (Z_to_bv 64 4096)]
  /\ ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]
  /\ ro_cells asegs m 0x13beac [C1 (Z_to_bv 8 0)]                 (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be38 [C8 (Z_to_bv 64 0)]                (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1fc0 [C8 (Z_to_bv 64 1)]                (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13bd9c [C4 (Z_to_bv 64 0)].               (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_consts_munch : forall W m m', mmap_consts m -> munch W m m' ->
  disjoint_from W 0xa1f60 8 -> disjoint_from W 0x139d20 8 -> disjoint_from W 0xa1f70 8 -> disjoint_from W 0x13beac 1 ->
  disjoint_from W 0x13be38 8 -> disjoint_from W 0xa1fc0 8 -> disjoint_from W 0x13bd9c 4 ->
  mmap_consts m'.
Proof.
  intros W m m' (C1_ & C2_ & C3_ & C4_ & C5_ & C6_ & C7_) MU D1 D2 D3 D4 D5 D6 D7.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| cbn; assumption]).
Qed.

Lemma mmap_cells : forall st m, RTREP st m -> mmap_consts m.
Proof.
  intros st m HR. unfold mmap_consts. pose proof (rr_consts st m HR) as HC. pose proof (rr_link st m HR) as HL.
  (nelimp HC 17%nat; intros _ _ _ CF K5 _ _ _ _ _ _ _ _ _ _ K16 _).
  split; [apply (R_link_at m 0xa1f60 0x139d20 HL); vm_compute; reflexivity|].
  split; [exact K5|].
  split; [apply (R_link_at m 0xa1f70 0x13bda8 HL); vm_compute; reflexivity|].
  split; [exact (cflags_byte m 260 CF ltac:(lia))|].
  split; [exact (cflags_word m 144 0 CF ltac:(lia) ltac:(lia) ltac:(intros i Hi; do 8 (destruct i as [|i]; [reflexivity|]); lia))|].
  split; [apply (R_link_at m 0xa1fc0 1 HL); vm_compute; reflexivity|].
  exact K16.
Qed.

Lemma land_align12 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.lxor (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 12) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 12)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia. rewrite (Z.ones_spec_high 12 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma roundup_aligned : forall sz, 0 < sz -> sz mod 4096 = 0 -> sz + 4096 <= 2^63 -> Z.land (sz + 4095) 18446744073709547520 = sz.
Proof. intros sz H1 H2 H3. rewrite land_align12 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma pru_id : forall sz, 0 <= sz -> sz mod 4096 = 0 -> page_round_up_Z sz = sz.
Proof. intros sz H1 H2. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. Qed.

Lemma asegs_reserved : segments_reserved asegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x71000); (Z_to_bv 64 0xa1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xa3000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma grant_above_image : forall mo (a : word) n, LOK asegs mo -> mmap_grant mo a n -> 0x10000 <= n < 2^64 -> AIMG_HI <= bv_unsigned a.
Proof.
  intros mo a n HO (AL & POS & CE & RF) Hn. rewrite region_free_app in RF. apply andb_true_iff in RF as [RF _].
  rewrite (lok_resv _ _ HO), asegs_reserved in RF. cbn [region_free] in RF. unfold iv_overlap in RF.
  rewrite !unsigned_lit in RF by lia.
  repeat (apply andb_true_iff in RF as [?X RF]; apply negb_true_iff in X; apply andb_false_iff in X; destruct X as [X|X]; apply Z.ltb_ge in X);
  unfold AIMG_HI; try lia.
Qed.

Section MMAPORDIE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (sz nm rw lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 320 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 <= sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis NM : 0 < nm < 2^64.
  Hypothesis RW : 0 <= rw < 2^64.

  (* [comment removed for export] *)
  Lemma mmapordie_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    sz <= R -> mmap_placeable mo sz ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a sz ->
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' (bv_unsigned a) [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_add_map a (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) (Z_to_bv 64 nm) (Z_to_bv 64 rw) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x67700) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P HRsz HPL K.
    (nelimp HC 7%nat; intros GOTP PSC GOTC CF260 CF144 GOTS DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 48%nat ST.
    do 6 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 18 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    rename FR into FR1. carve_frame 272%nat ST.
    do 8 lstep. lstep. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
    pose proof CF260 as CF1. recell CF1 MU. lstep. fl. clear CF1. lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    do 10 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + -48). rename FR1 into FR.
   
    lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply lscps_mmap_rw_spin2.
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { rewrite pru_id by lia. lia. } { rewrite pru_id by lia. exact HPL. }
    { (* [comment removed for export] *)
      intros e He. cbn in He. destruct He as [<-|[]].
      unfold efferr, eff0. sys_nret. unfold errno_ret, ENOMEM.
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      carve_frame 48%nat ST.
      do 6 lstep. (* [comment removed for export] *)
      pose proof GOTS as GOTS1. recell GOTS1 MU. lstep. lstep. fl. clear GOTS1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      pose proof DY as DY1. recell DY1 MU. lstep. lstep. fl. clear DY1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      apply evt_done. apply jself_MS. vm_compute. reflexivity. }
    { intros a GR. rewrite pru_id in GR |- * by lia.
      (nelimp GR 4%nat; intros GA GP GC GF). idtac.
      pose proof (grant_above_image mo a sz HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
      apply lscps_step_evt. rewrite <- (Z_to_bv_bv_unsigned a). sys_nret. fixMI.
      Unshelve.
      2:{ apply ro_addr_noseg. eapply (region_free_reserved_noseg asegs (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 sz) _ mo NWX HOK).
          - rewrite region_free_app in GF. apply andb_true_iff in GF as [GF _]. rewrite Z_to_bv_bv_unsigned. exact GF.
          - rewrite !unsigned_lit by lia. lia. }
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
      pose proof CF144 as CF1. recell CF1 MU. lstep. fl. clear CF1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. do 5 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW]. }
  Qed.
End MMAPORDIE.

Section MMAPNORESERVE_OPEN.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (sz nm lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 320 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 <= sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis NM : 0 < nm < 2^64.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mmapnoreserve_open_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    sz <= R -> mmap_placeable mo sz ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a sz ->
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' (bv_unsigned a) [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_add_lazy a (Z_to_bv 64 sz) mo)
             (mkG ((bv_unsigned a, bv_unsigned a + sz) :: G) (R - sz))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) (Z_to_bv 64 nm) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x67c38) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P HRsz HPL K.
    (nelimp HC 7%nat; intros GOTP PSC GOTC CF260 CF144 GOTS DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 48%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 9 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
    lstep. lstep. fl. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    rename FR into FR1. carve_frame 272%nat ST.
    do 8 lstep. lstep. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
    pose proof CF260 as CF1. recell CF1 MU. lstep. fl. clear CF1. lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    do 10 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + -48). rename FR1 into FR.
    lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply n2open_proof.
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { rewrite pru_id by lia. lia. } { rewrite pru_id by lia. exact HPL. }
    { (* [comment removed for export] *)
      intros e He. cbn in He. destruct He as [<-|[]].
      unfold efferr, eff0. sys_nret. unfold errno_ret, ENOMEM.
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      carve_frame 48%nat ST.
      do 6 lstep. (* [comment removed for export] *)
      pose proof GOTS as GOTS1. recell GOTS1 MU. lstep. lstep. fl. clear GOTS1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      pose proof DY as DY1. recell DY1 MU. lstep. lstep. fl. clear DY1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      apply evt_done. apply jself_MS. vm_compute. reflexivity. }
    { intros a GR. rewrite pru_id in GR |- * by lia.
      (nelimp GR 4%nat; intros GA GP GC GF). idtac.
      pose proof (grant_above_image mo a sz HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
      apply lscps_step_evt. rewrite <- (Z_to_bv_bv_unsigned a). sys_nret. fixMI.
      Unshelve.
      2:{ apply ro_addr_noseg. eapply (region_free_reserved_noseg asegs (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 sz) _ mo NWX HOK).
          - rewrite region_free_app in GF. apply andb_true_iff in GF as [GF _]. rewrite Z_to_bv_bv_unsigned. exact GF.
          - rewrite !unsigned_lit by lia. lia. }
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
      pose proof CF144 as CF1. recell CF1 MU. lstep. fl. clear CF1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. do 4 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW]. }
  Qed.
End MMAPNORESERVE_OPEN.


End CeilWrap.
End RTW_depot_mmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import STRW_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
Import RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac pr r := let v := reg_val r in idtac r "=" v.

Lemma land15_lor : forall a b, 0 <= a -> 0 <= b -> Z.land (Z.lor a b) 15 = 0 -> a mod 16 = 0 /\ b mod 16 = 0.
Proof.
  intros a b Ha Hb H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2].
  change 15 with (Z.ones 4) in H1, H2. rewrite Z.land_ones in H1, H2 by lia. change (2^4) with 16 in *. lia.
Qed.

Section MS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s n lo : Z).
  Hypothesis Rn : 0 <= n.
  Hypothesis SB : 0 <= s /\ s + n < 2^64.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.

  #[warnings="-notation-for-abbreviation"] Notation W := [(s, s + n)].
  #[warnings="-notation-for-abbreviation"] Notation POST c := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W lo m
               (fun _ _ m' => rw_cells asegs m' s [CB (Z.to_nat n) (repeat (zb c) (Z.to_nat n))])).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation ST_ pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma ms_ret : forall c (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop) x11 x12 x13,
    u8arr asegs m1 s bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < n -> Q j) ->
    evt asegs (POST c) (ST_ 0x65870 m1 x11 x12 x13).
  Proof.
    intros c m1 bs Q x11 x12 x13 ARR FIL LEN MI MU WM HQ.
    pose proof (filled_all _ _ _ FIL ltac:(rewrite LEN; intros j Hj; apply HQ; lia)) as E.
    rewrite LEN in E. rewrite E in ARR. apply rw_cells_of_u8arr in ARR. rewrite repeat_length in ARR.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp)) by (eapply stk_wmono_noseg; [exact ST0| exact WM| idtac; unfold AIMG_HI; lia]).
    zstep. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_byte_loop : forall (K : nat) c (i : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K -> 0 <= c < 256 ->
    u8arr asegs m1 s bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    evt asegs (POST c) (ST_ 0x6582c m1 (Z_to_bv 64 c) (Z_to_bv 64 (s + n)) (Z_to_bv 64 (s + i))).
  Proof using Rn SB ST0 CEIL.
    induction K as [K IH] using lt_wf_ind; intros c i m1 bs Q HK Rc ARR FIL LEN MI MU WM HQ Hi.
    mst i 1%nat ltac:(rewrite le1_byte; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (s + i + 1) with (s + (i + 1)) by lia.
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) c (i + 1) _ _ _ eq_refl Rc ARR FIL LEN MI MU WM); [|lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
    - (* [comment removed for export] *) zstep. eapply ms_ret; [exact ARR| exact FIL| exact LEN| exact MI| exact MU| exact WM|].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ms_wide_loop : forall (K : nat) c (i : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K -> 0 <= c < 256 ->
    u8arr asegs m1 s bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> i mod 16 = 0 -> n mod 16 = 0 ->
    evt asegs (POST c) (ST_ 0x65860 m1 (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 (s + n)) (Z_to_bv 64 (s + i))).
  Proof using Rn SB ST0 CEIL.
    induction K as [K IH] using lt_wf_ind; intros c i m1 bs Q HK Rc ARR FIL LEN MI MU WM HQ Hi Hi16 Hn16.
    mst i 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (i + 8) 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. if_cases KK; zify_cond KK.
    - replace (s + i + 16) with (s + (i + 16)) by lia.
      eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) c (i + 16) _ _ _ eq_refl Rc ARR FIL LEN MI MU WM);
        [| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| exact Hn16].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|].
      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
    - eapply ms_ret; [exact ARR| exact FIL| exact LEN| exact MI| exact MU| exact WM|].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|].
      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; Z.div_mod_to_equations; lia].
  Qed.

  Lemma ms_body : forall c x13 junk, 0 <= c < 256 -> mem_inv asegs m ->
    rw_cells asegs m s [CB (Z.to_nat n) junk] ->
    evt asegs (POST c) (ST_ 0x65814 m (Z_to_bv 64 c) (Z_to_bv 64 n) x13).
  Proof using Rn SB ST0 CEIL.
    intros c x13 junk Rc MI DST.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      destruct (land15_lor n s ltac:(lia) ltac:(lia) K0) as [N16 S16].
      zstep. if_cases K1; zify_cond K1.
      { eapply ms_ret; [exact ARR| exact FIL| exact LEN| exact MI| exact MU| exact WM| intros; lia]. }
      do 7 zstep. setreg 11 (Z_to_bv 64 (c * BC8)) ltac:(unfold BC8; brute256 c Rc).
      zstep. rewrite <- (Z.add_0_r s) at 3.
      eapply (ms_wide_loop _ c 0 _ _ _ eq_refl Rc ARR FIL LEN MI MU WM); [intros; lia| lia| reflexivity| exact N16].
    - zstep. if_cases K1; zify_cond K1.
      { eapply ms_ret; [exact ARR| exact FIL| exact LEN| exact MI| exact MU| exact WM| intros; lia]. }
      zstep. zstep. rewrite <- (Z.add_0_r s) at 3.
      eapply (ms_byte_loop _ c 0 _ _ _ eq_refl Rc ARR FIL LEN MI MU WM); [intros; lia| lia].
  Qed.
End MS.

Theorem internal_memset_proof : internal_memset_spec.
Proof.
  unfold internal_memset_spec. intros until lo. intros MI -> -> -> Rc Rn Rsn DST SEP ST CEIL LO.
  unfold A_INTERNAL_MEMSET. cbv beta delta [wz].
  pose proof (rw_cells_bound _ _ _ _ DST) as B.
  eapply ms_body; [exact Rn| lia| exact ST| exact CEIL| exact Rc| exact MI| exact DST].
Qed.

(* [comment removed for export] *)
Lemma internal_memset_Z :
  forall (s c n : Z) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  mem_inv asegs m -> 0 <= c < 256 -> 0 <= n -> s + n < 2^64 ->
  rw_cells asegs m s [CB (Z.to_nat n) junk] ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(s, s + n)] lo m
               (fun _ _ m' => rw_cells asegs m' s [CB (Z.to_nat n) (repeat (zb c) (Z.to_nat n))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65814) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI Rc Rn Rsn DST ST CEIL.
  pose proof (rw_cells_bound _ _ _ _ DST) as B.
  eapply ms_body; [exact Rn| lia| exact ST| exact CEIL| exact Rc| exact MI| exact DST].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac pr r := let v := reg_val r in idtac r "=" v.
