(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Import Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_ff_defs Sj_num_fc_stmt Sj_num_ff_top Sj_num_ff_cf Sj_num_ff_pn Sj_num_ff_pn2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_x.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section FFPN3.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Hypothesis SHPT : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' (f_p E) (8 * (f_n E / 8)).
  Hypothesis SHL1 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x28c20 10416.
  Hypothesis SHL2 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x2b5a0 640.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac pn_start INV := (let I0 := fresh "INV0" in pose proof INV as I0);
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; num_mark_words.
  Ltac cut_exit INV := first [ eapply evt_eq; [| eapply (ff_exit E OK m0)]; [num_st_eq | exact INV | assumption] | fail 100 "cut exit" ].

  Lemma ffb_3b8 : forall (IP IL : Z) xra xt1 xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb27bc xra (Z_to_bv 64 (IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (IP + IL)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT H1 H2 H3. pn_start INV.
    apply (num_cb8_c8 bsegs mm _ [] _ j) in FR. cbn [app] in FR.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2ad4%Z => first [ eapply evt_eq; [| eapply (ffb_6d0 E OK m0 SHPT SHL1 SHL2 IP IL 0%Z (IP + IL)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xb2964%Z => first [ eapply evt_eq; [| eapply (ffb_560 E OK m0 SHPT SHL1 SHL2 IP IL (IP + IL + 1)%Z)]; [num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia] | fail 100 "cut" pc ]
      | 0xb2864%Z => first [ let INVS := fresh "INVS" in
                             num_cur_mem ltac:(fun m1 => assert (INVS : FFINVS E m0 m1 (Z_to_bv 64 (IP + IL + 1))) by ffs_close);
                             eapply evt_eq; [| eapply (ffb_L2 E OK m0 SHPT SHL1 SHL2 (Z.to_nat LAST) IP IL (IP + IL + 1)%Z (IP + IL + 1)%Z)];
                             [num_st_eq | exact INVS | assumption | unfold ffb_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_398 : forall (IP IL : Z) xra xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb279c xra (Z_to_bv 64 (IL)) (Z_to_bv 64 (IP / 8)) xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (IP + IL)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT H1 H2 H3. pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2f74%Z => cut_exit INV
      | 0xb27bc%Z => first [ eapply evt_eq; [| eapply (ffb_3b8 IP IL)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac top_cuts INV HLT IP :=
    fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2f74%Z => cut_exit INV
      | 0xb279c%Z => first [ eapply evt_eq; [| eapply (ffb_398 IP _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end.

  Lemma ffb_L1 : forall (f : nat) (IP p : Z) xra xs0 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < p)%Z -> (p <= LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2740 xra (Z_to_bv 64 (2)) (Z_to_bv 64 (IP / 8)) (Z_to_bv 64 (10)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (9)) xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT H1 H2 Hf.
    { assert (p = LAST) by lia. subst p. pn_start INV. bwalk ltac:(top_cuts INV HLT IP). }
    pn_start INV. bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb2740%Z => first [ eapply evt_eq; [| eapply (IH IP (p + 1)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | _ => top_cuts INV HLT IP pc
      end).
  Qed.

  Lemma ffb_1f4 : forall (IP : Z) xra xt0 xt1 xt2 xs0 xs1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST <= IP < LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb25f8 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM H1. pn_start INV.
    assert (HLT : (FIRST < LAST)%Z) by lia.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb2740%Z => first [ eapply evt_eq; [| eapply (ffb_L1 (Z.to_nat LAST) IP (IP + 5)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | _ => top_cuts INV HLT IP pc
      end).
  Qed.

  Lemma ffb_19c : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc ->
    evt bsegs (ff_mid E m0) (FFS E 0xb25a0 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM. pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2f74%Z => cut_exit INV
      | 0xb25f8%Z => first [ eapply evt_eq; [| eapply (ffb_1f4 _)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN3.

Theorem ffb_body : ffb_body_stmt.
Proof.
  unfold ffb_body_stmt. intros E m0 OK HF0 SHPT SHL1 SHL2. intros until mm. intros INV FRM.
  eapply (ffb_19c E OK m0 SHPT SHL1 SHL2); [exact INV | exact FRM].
Qed.

Theorem ffb_ok : forall RT, art_facts RT -> num_lits_acc RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc -> ffb_stmt RT PMc.
Proof. intros RT AF NLA PMc FDO MST HFC. exact (ffb_of_body RT AF NLA PMc FDO MST HFC ffb_body). Qed.
