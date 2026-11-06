(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Local Ltac akstep ::=
  zstep; nnorm; kb2z; anorm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (Z_to_le_bytes ?n ?z)) _) =>
      lazymatch n with
      | 8%nat => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
      | 4%nat => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
      | 2%nat => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
      | 1%nat => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z))
      end;
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]; mem_after_store
  | |- _ => idtac
  end.

Ltac akwalk_abs PCS K :=
  akwalk ltac:(fun pc => first [ K pc | (lazymatch PCS with context [pc] => idtac end; num_abstract_loads; num_abstract_data; akstep; akwalk_abs PCS K) ]).

Section FCA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq f A FIRST LAST OUT : Z) (txt : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 192 - d)%Z.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c1000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + TL)%Z.
  Hypothesis TSEP : ((A + TL <= f \/ f + 1024 <= A) /\ (A + TL <= S \/ S + 128 <= A))%Z.
  Hypothesis OUTR : (OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP)%Z.

  Notation W := [(lo, spq + 88); (f + 32, f + 536); (f + 608, f + 680); (f / 8 + 2147450884, f / 8 + 2147450947); (OUT, OUT + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (FIRST / 8)) (LAST - 8 * (FIRST / 8)).
  Hypothesis SHPO : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' OUT 8.
  Variable Q : machine_state -> Prop.
  Collection FCH := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO.

  Notation FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Notation FCP pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (f + 608)) xs6 (Z_to_bv 64 LAST) xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Notation tb := (ftb A txt).
  Notation ge48 := (fge48 A txt).
  Notation FCPINV := (fc_pinv spq f A OUT lo txt m0).

  Notation ERRA_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm ->
     evt asegs Q (FCP 0x7eea4 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Notation ERRB_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
     evt asegs Q (FCP 0x7eea4 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Hypothesis KERRA : forall ra1, In ra1 FC_ERRA -> ERRA_K ra1.
  Hypothesis KERRB : forall ra1, In ra1 FC_ERRB -> ERRB_K ra1.

  Ltac fc_in_list := unfold FC_ERRA, FC_ERRB; cbn [In]; repeat (first [left; reflexivity | right]).
  Ltac fc_erra_cut := eapply evt_eq; [| eapply KERRA]; [num_st_eq | fc_in_list | fc_pclose].
  Ltac fc_errb_cut := eapply evt_eq; [| eapply KERRB]; [num_st_eq | fc_in_list | fc_pclose].

  Notation FCD D := (D sp gp tp F fc lo spq f A FIRST LAST OUT txt m0 Q) (only parsing).
  Notation FCL L := (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q) (only parsing).

  Ltac fc_env :=
    destruct SPQ as [Hd Hspq]; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8.

  Notation PF := (fpfacts A txt FIRST LAST).
  Notation FF := (fffacts A txt FIRST LAST).

  Definition fc_exp_k : Prop :=
    forall (IP IL FPT FL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> PF IP IL FPT FL ->
      ((FPT = 0 /\ p = IP + IL) \/ (FPT <> 0 /\ p = FPT + FL))%Z ->
      evt asegs Q (FCP 0xdca4c xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 (Z_to_bv 64 (- FL)) (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                       (Z_to_bv 64 p) xs11 (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) (Z_to_bv 64 FPT) mm).

  Notation FRS pc IP IL p xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 mm :=
    (FCP pc xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 IL) xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
         (Z_to_bv 64 p) xs11 (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) (Z_to_bv 64 (IP + IL + 1)) mm).

  Lemma fc_504 : fc_exp_k -> forall (IP IL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> FF IP IL p ->
    evt asegs Q (FRS 0xdca34 IP IL p xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 mm).
  Proof using FCH KERRB.
    intros KEXP. intros until mm. intros INV FFp. pose proof INV as INV0. fc_popen INV0. fc_env.
    pose proof FFp as ((F1 & F2 & F3 & F4) & _).
    akwalk ltac:(fun pc => lazymatch pc with
      | 0x7eea4%Z => first [ fc_errb_cut | fail 100 "cut" pc ]
      | 0xdca4c%Z => first [ eapply evt_eq; [| eapply (KEXP IP IL (IP + IL + 1)%Z (p - (IP + IL + 1))%Z p)];
                             [ num_st_eq | exact INV | apply fffacts_pfacts; [exact FFp | lia] | right; lia ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_L3 : fc_exp_k -> forall (fu : nat) (IP IL p : Z) xra xt0 xt1 xt2 xa1 xa4 xa5 xa7 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> FF IP IL p -> (p < LAST)%Z -> (LAST - p <= Z.of_nat fu)%Z ->
    evt asegs Q (FRS 0xdc9ec IP IL p xra xt0 xt1 xt2 (Z_to_bv 64 p) xa1 (Z_to_bv 64 9) xa4 xa5 (Z_to_bv 64 10) xa7 xs3 xs11 xt4 mm).
  Proof using FCH KERRB.
    intros KEXP fu. induction fu as [|fu IH]; intros until mm; intros INV FFp H2 Hf; [exfalso; lia|].
    pose proof INV as INV0. fc_popen INV0. fc_env.
    pose proof FFp as ((F1 & F2 & F3 & F4) & _).
    pose proof (ftb_range A txt p) as Rp. unfold ftb in Rp.
    akstep.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdca34%Z => first [ eapply evt_eq; [| eapply (fc_504 KEXP IP IL _)]; [num_st_eq | exact INV |];
                             first [ exact FFp
                                   | eapply (fffacts_app_eq _ _ _ _ _ _ p 1%Z); [exact FFp | lia | lia | apply fge48_1; unfold ftb; lia | lia] ] | fail 100 "cut" pc ]
      | 0xdc9ec%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 1)%Z)]; [num_st_eq | exact INV | | lia | lia];
                             eapply (fffacts_app_eq _ _ _ _ _ _ p 1%Z); [exact FFp | lia | lia | apply fge48_1; unfold ftb; lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_4ac : fc_exp_k -> forall (IP IL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> FF IP IL p ->
    evt asegs Q (FRS 0xdc9dc IP IL p xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 mm).
  Proof using FCH KERRB.
    intros KEXP. intros until mm. intros INV FFp. pose proof INV as INV0. fc_popen INV0. fc_env.
    pose proof FFp as ((F1 & F2 & F3 & F4) & _).
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdca34%Z => first [ eapply evt_eq; [| eapply (fc_504 KEXP IP IL p)]; [num_st_eq | exact INV | exact FFp] | fail 100 "cut" pc ]
      | 0xdc9ec%Z => first [ eapply evt_eq; [| eapply (fc_L3 KEXP (Z.to_nat LAST) IP IL p)]; [num_st_eq | exact INV | exact FFp | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_3ec : fc_exp_k -> forall (IP IL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> FF IP IL p -> (p + 4 <= LAST)%Z ->
    evt asegs Q (FRS 0xdc91c IP IL p xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt4 mm).
  Proof using FCH KERRB.
    intros KEXP. intros until mm. intros INV FFp H4. pose proof INV as INV0. fc_popen INV0. fc_env.
    pose proof FFp as ((F1 & F2 & F3 & F4) & _).
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdc9dc%Z => first [ eapply evt_eq; [| eapply (fc_4ac KEXP IP IL _)]; [num_st_eq | exact INV |];
                             first [ exact FFp
                                   | eapply (fffacts_app_eq _ _ _ _ _ _ p 4%Z); [exact FFp | lia | lia | | lia];
                                     lazymatch goal with KB : Z.land _ 18446744071570489472 = 0%Z |- _ => exact (fswar4 A txt p _ KB) end ] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation FRINV IP IL c0 c8 c32 c64 c80 mm :=
    (FCPINV c0 c8 (Z_to_bv 64 53) (Z_to_bv 64 0xA0000002E) c32 (Z_to_bv 64 (IP + IL + 1)) (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm).

  Lemma fc_3dc : fc_exp_k -> forall (IP IL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs11 xt3 xt4 xt5 xt6 c0 c8 c32 c64 c80 (mm : mem),
    FRINV IP IL c0 c8 c32 c64 c80 mm -> FF IP IL p -> (p + 8 <= LAST)%Z ->
    evt asegs Q (FCP 0xdc90c xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 IL) xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) xs11 xt3 xt4 xt5 xt6 mm).
  Proof using FCH KERRB.
    intros KEXP. intros until mm. intros INV FFp H8. pose proof INV as INV0. fc_popen INV0. fc_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdc91c%Z => first [ eapply evt_eq; [| eapply (fc_3ec KEXP IP IL p)]; [num_st_eq | exact INV | exact FFp | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  Lemma fc_238 : fc_exp_k -> forall (IP IL p : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa7 xs3 xs11 xt3 xt4 xt5 xt6 c0 c8 c32 c64 c80 (mm : mem),
    FRINV IP IL c0 c8 c32 c64 c80 mm -> FF IP IL p ->
    evt asegs Q (FCP 0xdc768 xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 IL) xa4 xa5 (Z_to_bv 64 (LAST - p)) xa7 xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) xs11 xt3 xt4 xt5 xt6 mm).
  Proof using FCH KERRB.
    intros KEXP. intros until mm. intros INV FFp. pose proof INV as INV0. fc_popen INV0. fc_env.
    pose proof FFp as ((F1 & F2 & F3 & F4) & _).
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdc91c%Z => first [ eapply evt_eq; [| eapply (fc_3ec KEXP IP IL p)]; [num_st_eq | exact INV | exact FFp | lia] | fail 100 "cut" pc ]
      | 0xdc9dc%Z => first [ eapply evt_eq; [| eapply (fc_4ac KEXP IP IL p)]; [num_st_eq | exact INV | exact FFp] | fail 100 "cut" pc ]
      end).
  Qed.

End FCA.
