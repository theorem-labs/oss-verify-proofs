(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_ff_defs Sj_num_ff_cf Sj_num_ff_pn Sj_num_ff_pn2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FFPN3.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.
  Hypothesis SHPT : forall m', munch (FF_W E) m0 m' -> wmono asegs m0 m' -> shz m' (f_p E) (8 * (f_n E / 8)).
  Hypothesis SHL1 : forall m', munch (FF_W E) m0 m' -> wmono asegs m0 m' -> shz m' 0x2a2e0 10416.
  Hypothesis SHL2 : forall m', munch (FF_W E) m0 m' -> wmono asegs m0 m' -> shz m' 0x2cc60 640.
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
  Ltac c_exit INV := first [ eapply (ff_exit E OK m0); [exact INV | assumption] | fail 100 "cut exit" ].
  Ltac c_8c8 INV p4 dc := eapply evt_eq; [| eapply (ff_8c8 E OK m0 SHPT SHL1 SHL2 p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia].
  Ltac c_6a0 INV p bf p4 dc := eapply evt_eq; [| eapply (ff_6a0 E OK m0 SHPT SHL1 SHL2 p bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia].
  Ltac c_6a8 INV p bf p4 dc := eapply evt_eq; [| eapply (ff_6a8 E OK m0 SHPT SHL1 SHL2 p bf p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia].
  Ltac c_7cc INV p p4 dc := eapply evt_eq; [| eapply (ff_7cc E OK m0 SHPT SHL1 SHL2 p p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia].

  Lemma div8_step : forall p, ((p + 8) / 8 = p / 8 + 1)%Z.
  Proof. intros p. Z.div_mod_to_equations. lia. Qed.

  Lemma ff_L2 : forall (f : nat) (p bf p4 dc : Z) xra xt0 xs0 xs1 xa5 xa6 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xt4 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (0 <= dc)%Z -> (p4 + dc < bf)%Z -> (bf <= p)%Z -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb95f0 xra xt0 (Z_to_bv 64 (dc)) (Z_to_bv 64 (bf)) xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p + 7)) xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 (Z_to_bv 64 (7)) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (LAST - p)) xt4 (Z_to_bv 64 (p / 8 + 2147450880)) xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hdc Hbf Hp Hp8 Hf; [exfalso; lia|].
    pn_start INV. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb96f8%Z => first [ c_6a8 INV p bf p4 dc | fail 100 "cut" pc ]
      | 0xb96f0%Z => first [ c_6a0 INV (p + 8)%Z bf p4 dc | fail 100 "cut" pc ]
      | 0xb95f0%Z => first [ (let IH' := fresh "IH'" in pose proof (IH (p + 8)%Z bf p4 dc) as IH'; rewrite (div8_step p) in IH';
                              eapply evt_eq; [| eapply IH']; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia | lia]) | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_504 : forall (p p4 : Z) xra xt0 xt2 xs0 xs1 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 < p <= LAST)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9554 xra xt0 (Z_to_bv 64 (p - p4)) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) xa4 xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM Hp4 Hp. pn_start INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb981c%Z => first [ c_7cc INV p p4 (p - p4)%Z | fail 100 "cut" pc ]
      | 0xb9918%Z => first [ c_8c8 INV p4 (p - p4)%Z | fail 100 "cut" pc ]
      | 0xb96f0%Z => first [ c_6a0 INV (p + 1)%Z (p + 1)%Z p4 (p - p4)%Z | fail 100 "cut" pc ]
      | 0xb95f0%Z => first [ eapply evt_eq; [| eapply (ff_L2 (Z.to_nat (f_LAST E - p)) (p + 1)%Z (p + 1)%Z p4 (p - p4)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_4e8 : forall (p p4 : Z) xra xt0 xt2 xs0 xs1 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 < p <= LAST)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9538 xra xt0 (Z_to_bv 64 (p - p4)) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) xa4 (Z_to_bv 64 (p4 / 8 + 2147450880)) xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM Hp4 Hp. pn_start INV. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9ca4%Z => c_exit INV
      | 0xb9554%Z => first [ eapply evt_eq; [| eapply (ff_504 p p4)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_4e0 : forall (p p4 : Z) xra xt0 xt1 xt2 xs0 xs1 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= p <= LAST)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9530 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) xa4 (Z_to_bv 64 (p4 / 8 + 2147450880)) xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM Hp4 Hp. pn_start INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9ca4%Z => c_exit INV
      | 0xb9538%Z => first [ eapply evt_eq; [| eapply (ff_4e8 p p4)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  Ltac c_4e0 INV p p4 := eapply evt_eq; [| eapply (ff_4e0 p p4)]; [num_st_eq | exact INV | assumption | lia | lia].

  Lemma ff_L1 : forall (f : nat) (p p4 : Z) xra xt0 xs0 xs1 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb94e0 xra xt0 (Z_to_bv 64 (10)) (Z_to_bv 64 (9)) xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p4 / 8 + 2147450880)) xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hp Hf; [exfalso; lia|].
    pn_start INV. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9ca4%Z => c_exit INV
      | 0xb9530%Z => first [ c_4e0 INV p p4 | fail 100 "cut" pc ]
      | 0xb9538%Z => first [ eapply evt_eq; [| eapply (ff_4e8 (f_LAST E) p4)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      | 0xb94e0%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z p4)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_334 : forall  xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc ->
    evt asegs (ff_mid E m0) (FFS E 0xb9384 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM. pn_start INV.
    Ltac c_4e0s INV q :=
      first [ c_4e0 INV q q | c_4e0 INV (q + 1)%Z q | c_4e0 INV (q + 2)%Z q | c_4e0 INV (q + 3)%Z q | c_4e0 INV (q + 4)%Z q | c_4e0 INV (q + 5)%Z q ].
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9ca4%Z => c_exit INV
      | 0xb9530%Z => first [ c_4e0s INV (f_FIRST E) | c_4e0s INV (f_FIRST E + 1)%Z | fail 100 "cut" pc ]
      | 0xb94e0%Z => first [ eapply evt_eq; [| eapply (ff_L1 (Z.to_nat (f_LAST E - f_FIRST E)) (f_FIRST E + 5)%Z (f_FIRST E))]; [num_st_eq | exact INV | assumption | lia | lia | lia]
                           | eapply evt_eq; [| eapply (ff_L1 (Z.to_nat (f_LAST E - f_FIRST E)) (f_FIRST E + 1 + 5)%Z (f_FIRST E + 1)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN3.
