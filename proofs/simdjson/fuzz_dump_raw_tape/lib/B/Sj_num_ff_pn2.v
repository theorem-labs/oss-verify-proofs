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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_ff_defs Sj_num_ff_cf Sj_num_ff_pn.
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

Section FFPN2.
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
  Ltac pns_start INV := (let I0 := fresh "INV0" in pose proof INV as I0);
    lazymatch goal with INVh : FFINVS _ _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ffs_open I1 end; ff_env OK; num_mark_words.
  Ltac cut_exit INV := first [ eapply evt_eq; [| eapply (ff_exit E OK m0)]; [num_st_eq | exact INV | assumption] | fail 100 "cut exit" ].

  Definition ffb_bfacts (IP IL FPT p : Z) : Prop := (FIRST < LAST /\ A <= IP < LAST /\ 0 <= IL <= 2147483648 /\ A <= FPT <= p /\ p <= LAST)%Z.

  Lemma ffb_6b4 : forall (IP IL FPT p : Z) xra xt1 xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> ffb_bfacts IP IL FPT p ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2ab8 xra (Z_to_bv 64 (IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (FPT)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM (HLT & Hip & Hil & Hf & Hp). pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2f74%Z => cut_exit INV
      | 0xb2ad4%Z => first [ eapply evt_eq; [| eapply (ffb_6d0 E OK m0 SHPT SHL1 SHL2 IP (IL - (FPT - p))%Z (FPT - p)%Z p)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_L3 : forall (f : nat) (IP IL FPT p : Z) xra xt1 xs0 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> ffb_bfacts IP IL FPT p -> (p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2a68 xra (Z_to_bv 64 (IL)) xt1 (Z_to_bv 64 (9)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (FPT)) xs9 xs10 xs11 (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM BF Hp Hf; [exfalso; lia|].
    pose proof BF as (HLT & Hip & Hil & Hfp & Hpl). pn_start INV.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2ab8%Z => first [ eapply evt_eq; [| eapply (ffb_6b4 IP IL FPT _)]; [num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia] | fail 100 "cut" pc ]
      | 0xb2a68%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT (p + 1)%Z)]; [num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_650 : forall (IP IL FPT p : Z) xra xt1 xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> ffb_bfacts IP IL FPT p ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2a54 xra (Z_to_bv 64 (IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (FPT)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM BF. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl). pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2ab8%Z => first [ eapply evt_eq; [| eapply (ffb_6b4 IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF] | fail 100 "cut" pc ]
      | 0xb2a68%Z => first [ eapply evt_eq; [| eapply (ffb_L3 (Z.to_nat LAST) IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_58c : forall (IP IL FPT p : Z) xra xt1 xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> ffb_bfacts IP IL FPT p -> (p + 4 <= LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2990 xra (Z_to_bv 64 (IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (FPT)) xs9 xs10 xs11 xt3 (Z_to_bv 64 (p)) xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM BF Hp4. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl). pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2a54%Z => first [ eapply evt_eq; [| eapply (ffb_650 IP IL FPT _)]; [num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_560 : forall (IP IL FPT : Z) xra xt1 xs0 xs1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> ffb_bfacts IP IL FPT FPT ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2964 xra (Z_to_bv 64 (IL)) xt1 (Z_to_bv 64 (LAST - FPT)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (FPT)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM BF. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl). pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2a54%Z => first [ eapply evt_eq; [| eapply (ffb_650 IP IL FPT FPT)]; [num_st_eq | exact INV | assumption | exact BF] | fail 100 "cut" pc ]
      | 0xb2990%Z => first [ eapply evt_eq; [| eapply (ffb_58c IP IL FPT FPT)]; [num_st_eq | exact INV | assumption | exact BF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_57c : forall (IP IL FPT p : Z) xra xt1 xs0 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINVS E m0 mm (Z_to_bv 64 FPT) -> frm0 xfc -> ffb_bfacts IP IL FPT p ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2980 xra (Z_to_bv 64 (IL)) xt1 (Z_to_bv 64 (LAST - p)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p + 7)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM BF. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof (FFINV_of_S _ _ _ _ INV) as INVF. pns_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2a54%Z => first [ eapply evt_eq; [| eapply (ffb_650 IP IL FPT p)]; [num_st_eq | exact INVF | assumption | exact BF] | fail 100 "cut" pc ]
      | 0xb2990%Z => first [ eapply evt_eq; [| eapply (ffb_58c IP IL FPT p)]; [num_st_eq | exact INVF | assumption | exact BF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_574 : forall (IP IL FPT p : Z) xra xt1 xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 xF xfc mm,
    FFINVS E m0 mm (Z_to_bv 64 FPT) -> frm0 xfc -> ffb_bfacts IP IL FPT p -> (p + 8 <= LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2978 xra (Z_to_bv 64 (IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (p)) xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM BF Hp8. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof (FFINV_of_S _ _ _ _ INV) as INVF. pns_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2990%Z => first [ eapply evt_eq; [| eapply (ffb_58c IP IL FPT p)]; [num_st_eq | exact INVF | assumption | exact BF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_L2 : forall (f : nat) (IP IL FPT p : Z) xra xt1 xs0 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xF xfc mm,
    FFINVS E m0 mm (Z_to_bv 64 FPT) -> frm0 xfc -> ffb_bfacts IP IL FPT p -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2864 xra (Z_to_bv 64 (IL)) xt1 (Z_to_bv 64 (LAST - p)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) (Z_to_bv 64 (p + 7)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (7)) xs8 xs9 xs10 xs11 (Z_to_bv 64 (8)) xt4 xt5 (Z_to_bv 64 (p / 8 + 2147450880)) xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM BF Hp Hf; [exfalso; lia|].
    pose proof BF as (HLT & Hip & Hil & Hfp & Hpl). pns_start INV.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2978%Z => first [ eapply evt_eq; [| eapply (ffb_574 IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF | lia] | fail 100 "cut" pc ]
      | 0xb2980%Z => first [ eapply evt_eq; [| eapply (ffb_57c IP IL FPT (p + 8)%Z)]; [num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia] | fail 100 "cut" pc ]
      | 0xb2864%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT (p + 8)%Z)];
                             [replace ((p + 8) / 8)%Z with (p / 8 + 1)%Z by (Z.div_mod_to_equations; lia); num_st_eq | exact INV | assumption | unfold ffb_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN2.
