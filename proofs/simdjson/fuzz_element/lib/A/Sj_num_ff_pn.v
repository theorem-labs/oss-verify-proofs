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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_ff_defs Sj_num_ff_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Lemma wz_signed : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof.
  intros w. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  Z.div_mod_to_equations. lia.
Qed.

Section FFPN.
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

  Lemma ff_930w : forall  xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc ->
    evt asegs (ff_mid E m0) (FFS E 0xb9980 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHL1 SHL2.
    intros until mm. intros INV FRM.
    rewrite <- (wz_signed xa5).
    pose proof (bv_signed_in_range 64 xa5 ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
    change (2 ^ Z.of_N 64 / 2)%Z with 9223372036854775808%Z in R.
    eapply (ff_930 E OK m0 SHL1 SHL2 (bv_signed xa5)); [exact INV | exact FRM | lia].
  Qed.

  Lemma ff_L5 : forall (f : nat) (p4 : Z) xra xt0 xt1 xs0 xs1 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 < LAST)%Z -> (LAST - p4 <= Z.of_nat f)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9948 xra xt0 xt1 (Z_to_bv 64 (46)) xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p4)) (Z_to_bv 64 (48)) xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp Hl Hf; [exfalso; lia|].
    pn_start INV. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9d44%Z => first [ eapply (ff_cf4 E OK m0); [exact INV | assumption | lia] | fail 100 "cut" pc ]
      | 0xb9980%Z => first [ eapply ff_930w; [exact INV | assumption] | fail 100 "cut" pc ]
      | 0xb9948%Z => first [ eapply evt_eq; [| eapply (IH (p4 + 1)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_8c8 : forall (p4 dc : Z) xra xt0 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb9918 xra xt0 (Z_to_bv 64 (dc)) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) xa3 xa4 xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM Hp Hl Hdc. pn_start INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9980%Z => first [ eapply ff_930w; [exact INV | assumption] | fail 100 "cut" pc ]
      | 0xb9948%Z => first [ eapply (ff_L5 (Z.to_nat (LAST - p4)) p4); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_8bc : forall (p4 dc : Z) xra xt0 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb990c xra xt0 (Z_to_bv 64 (dc)) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) xa3 xa4 xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM Hp Hl Hdc. pn_start INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9918%Z => first [ eapply (ff_8c8 p4 dc); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_L4 : forall (f : nat) (p p4 dc : Z) xra xt0 xt2 xs0 xs1 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= LAST)%Z -> (-9223372036854775808 <= dc <= LAST - p4)%Z -> (A <= p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt asegs (ff_mid E m0) (FFS E 0xb98cc xra xt0 (Z_to_bv 64 (dc)) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 (p4)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p)) xa5 xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (9)) (Z_to_bv 64 (10)) (Z_to_bv 64 (268435456)) xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hl Hdc Hp Hf; [exfalso; lia|].
    pn_start INV. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb990c%Z => first [ eapply (ff_8bc p4 dc); [exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xb98cc%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z p4 dc)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN.
