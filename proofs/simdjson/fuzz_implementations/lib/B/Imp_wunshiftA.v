(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import F_uselocaleA Imp_xifaceA.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Ltac retpc_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition WUNSH : Z := 0x14a7c8.
Definition USELOC_RA1 : Z := 0x14a7f8.
Definition USELOC_RA2 : Z := 0x14a820.
Definition CLOC : Z := 0x37998.
Definition TPLOC : Z := 0x6be3b8.
Definition GLOC : Z := 0x6de6b0.
Definition RTP_ : Z := 0x6be3e8.
Definition WUNSH_DEPTH : Z := 64 + ICPT_DEPTH.

Section WUnshiftA.
Variable IX : mem -> Prop.
Variable XLO : Z.
Hypothesis IXF : IX_frame_stmt IX XLO.
Hypothesis IWC : iwcrtomb_stmt IX XLO.

Definition wunshift_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (E, E + 8); (0x6be3b8, 0x6be3b8 + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' E [C8 (Z_to_bv 64 X)]
    /\ rw_cells bsegs m' 0x6be3b8 [C8 (Z_to_bv 64 0x6de6b0)]
    /\ IX m'.

Lemma wunshift_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (CV E X PS lo hi : Z) (j : list byte),
  a0 = Z_to_bv 64 CV -> rw_cells bsegs m (CV + 16) [C8 (Z_to_bv 64 CLOC)] -> (0 < CV) -> (CV + 24 <= lo) ->
  a4 = Z_to_bv 64 E -> a2 = Z_to_bv 64 X -> a3 = Z_to_bv 64 (X + 8) -> rw_cells bsegs m E [CB 8 j] -> (0 <= X) -> (X + 16 < 2^64) ->
  (bv_unsigned sp <= E) -> (E + 8 < 2^63) -> (E + 8 <= hi) ->
  a1 = Z_to_bv 64 PS -> rw_cells bsegs m PS [C8 (Z_to_bv 64 0)] -> (0x6bc488 <= PS) -> (PS + 8 <= 0x6bcc28) ->
  tp = Z_to_bv 64 RTP_ -> rw_cells bsegs m 0x6be3b8 [C8 (Z_to_bv 64 0x6de6b0)] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - WUNSH_DEPTH) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
  IX m -> mem_inv bsegs m ->
  evt bsegs (wunshift_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E X lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WUNSH) fc None m (seg_rom bsegs)).
Proof.
  intros until j. intros -> CVL CV0 CVH -> -> -> CE X0 XH ES EH EHI -> PSC PS0 PSH -> TPL ST LO GLO XL SPHI IXm MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold WUNSH, WUNSH_DEPTH, ICPT_DEPTH, GLOBALS_TOP, CLOC, TPLOC, GLOC, RTP_, XTPLOC in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (E, E + 8); (0x6be3b8, 0x6be3b8 + 8)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  do 6 lstep.
  lstep. lstep. lstep.
  lstep.
  lstep.
  lstep.
  name_sp sp (-64)%Z. replace (bv_unsigned sp + -64) with (bv_unsigned sp0) in ST, FR by lia.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 7202480 227736);
    [ first [reflexivity | lia | eassumption] .. | ].
  Ltac eval_post H := cbn [usel_ret usel_new] in H;
    match type of H with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] => let v' := eval vm_compute in v in replace v with v' in H by (vm_compute; reflexivity) end.
  Ltac eval_a0 := cbn [usel_ret usel_new];
    match goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      let v' := eval vm_compute in v in replace v with v' by (vm_compute; reflexivity) end.
  eval_post POST. eval_a0. rename POST into TPL1.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.

  lazymatch type of FR with rw_cells _ ?mm ?A (CB 16 ?jj :: ?rest) =>
    pose proof (rw_cells_split_CB bsegs mm A [] 16 jj rest [12%nat; 4%nat] FR eq_refl) as FRS; cbn [app mk_CB_cells] in FRS;
    apply (proj1 (rw_cells_app _ _ _ [CB 12 _] _)) in FRS as [FA FRS];
    apply (proj1 (rw_cells_app _ _ _ [CB 4 _] _)) in FRS as [FD FREST];
    cbn [cells_size csize Nat.add] in FD, FREST; change (Z.of_nat 12) with 12 in FD; change (Z.of_nat 12) with 12 in FREST; change (Z.of_nat 4) with 4 in FREST
  end.
  replace (bv_unsigned sp0 + 12 + 4) with (bv_unsigned sp0 + 16) in FREST by lia. clear FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IX0 : IX mm) by (eapply (IXF _ lo hi); [exact IXm | exact MU | exact WM | unfold GLOBALS_TOP; lia | unfold sub_fp, XWI, XTPLOC; cbn [outside]; intros; lia]) end.
  lazymatch type of FD with rw_cells _ _ _ [CB 4 ?jd] =>
    call (IWC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp0 + 12) PS lo jd) end;
    try first [ reflexivity | exact FD | exact PSC | exact ST | exact IX0 | unfold XTPLOC, GLOBALS_TOP, ICPT_DEPTH; lia | eassumption ].
  clear IX0. match goal with H : IX _ |- _ => clear H end.
  first [ match goal with H : stk bsegs _ _ _ |- _ => tryif constr_eq H ST then fail else (try clear ST; rename H into ST) end | idtac ].
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + 12) [CB 4 _] |- _ => rename H into FD end.
  try retpc_lit.
  lstep.
  lstep. if_lit.
  lstep. lstep.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 227736 18446744073709551615);
    [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. eval_a0. rename POST into TPL2.
  lstep. lstep. lstep. if_lit.
  lstep.
  lstep.
  lstep.
  lstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - K1 X0 XH. try rewrite !unsigned_lit in K1 by lia. lia. } clear K1.
  lstep. if_lit.
  do 5 lstep.
  unname_sp.
  lstep.
  release_frame FA ST (bv_unsigned sp + -64 + 12). release_frame FD ST (bv_unsigned sp + -64 + 16). release_frame FREST ST (bv_unsigned sp).
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IX1 : IX mm) by (eapply (IXF _ lo hi); [exact IXm | exact MU | exact WM | unfold GLOBALS_TOP; lia | unfold sub_fp, XWI, XTPLOC; cbn [outside]; intros; lia]) end.
  apply evt_done. unfold wunshift_post. sys_finish.
Qed.
End WUnshiftA.
