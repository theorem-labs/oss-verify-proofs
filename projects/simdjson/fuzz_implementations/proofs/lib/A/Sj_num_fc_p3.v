(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_defs Sj_num_fc_p2.
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
  Hypothesis FLO : (0x6d2000 <= f /\ f + 1016 <= lo)%Z.
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
     evt asegs Q (FCP 0x84a08 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Notation ERRB_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
     evt asegs Q (FCP 0x84a08 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
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
  Notation EXP_K := (FCD fc_exp_k).

  Definition fc_84c_k : Prop :=
    forall (IP IL FPT FL : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> PF IP IL FPT FL -> (IL + FL < 20)%Z ->
      evt asegs Q (FCP 0xea484 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                       xs10 xs11 (Z_to_bv 64 0xA0000002E) xt4 xt5 (Z_to_bv 64 FPT) mm).
  Definition fc_77c_k : Prop :=
    forall (IP IL FPT FL : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> PF IP IL FPT FL -> (20 <= IL + FL)%Z ->
      evt asegs Q (FCP 0xea3b4 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                       xs10 xs11 (Z_to_bv 64 0xA0000002E) xt4 xt5 (Z_to_bv 64 FPT) mm).

  Section EXPPART.
  Hypothesis K84 : fc_84c_k.
  Hypothesis K77 : fc_77c_k.
  Variables IP IL FPT FL : Z.
  Hypothesis PFp : PF IP IL FPT FL.

  Lemma fc_flb : (1 <= IL /\ 0 <= FL /\ FIRST <= IP /\ IP + IL <= LAST /\ FL <= LAST)%Z.
  Proof using FCH PFp.
    destruct PFp as ((P1 & P2 & P3) & _ & PD). destruct FLR as (R1 & R2 & R3). destruct TXR as (T1 & T2 & T3).
    destruct PD as [[-> ->]|[(-> & Q1 & Q2 & _) _]]; lia.
  Qed.

  Ltac exp_cut pc :=
    lazymatch pc with
    | 0xea484%Z => first [ eapply evt_eq; [| eapply (K84 IP IL FPT FL)]; [num_st_eq | fc_pclose | exact PFp | lia] | fail 100 "cut" pc ]
    | 0xea3b4%Z => first [ eapply evt_eq; [| eapply (K77 IP IL FPT FL)]; [num_st_eq | fc_pclose | exact PFp | lia] | fail 100 "cut" pc ]
    end.

  Lemma fc_75c : forall xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
    evt asegs Q (FCP 0xea394 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 FPT) (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 0xA0000002E) mm).
  Proof using FCH K84 K77 PFp.
    intros until mm. intros INV. fc_popen INV. fc_env. pose proof fc_flb as FLB.
    assert (D0 : IsData xt0) by exact I. assert (D1 : IsData xt1) by exact I. assert (D6 : IsData xa6) by exact I. assert (D5 : IsData xa5) by exact I.
    awalk exp_cut.
  Qed.

  Lemma fc_LX : forall (fu : nat) (q : Z) xra xt0 xt1 xa1 xa4 xa5 xa6 xs10 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> (FIRST <= q < LAST)%Z -> (LAST - q <= Z.of_nat fu)%Z ->
    evt asegs Q (FCP 0xea2dc xra xt0 xt1 (Z_to_bv 64 9) (Z_to_bv 64 q) xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) (Z_to_bv 64 FPT) (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 (Z_to_bv 64 q) (Z_to_bv 64 10) (Z_to_bv 64 268435456) xt5 (Z_to_bv 64 0xA0000002E) mm).
  Proof using FCH K84 K77 PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV Hq Hf; [exfalso; lia|].
    pose proof INV as INV0. fc_popen INV0. fc_env. pose proof fc_flb as FLB.
    assert (D0 : IsData xt0) by exact I. assert (D1 : IsData xt1) by exact I. assert (D6 : IsData xa6) by exact I. assert (D5 : IsData xa5) by exact I.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xea394%Z => first [ eapply evt_eq; [| eapply fc_75c; exact INV]; num_st_eq | fail 100 "cut" pc ]
      | 0xea2dc%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z); [exact INV | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_650 : forall (q : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> (FIRST <= q <= LAST)%Z -> (xa6 = Z_to_bv 64 (- FL)) ->
    evt asegs Q (FCP 0xea288 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 (Z_to_bv 64 q) (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) (Z_to_bv 64 FPT) mm).
  Proof using FCH K84 K77 PFp.
    intros until mm. intros INV Hq ->. pose proof INV as INV0. fc_popen INV0. fc_env. pose proof fc_flb as FLB.
    assert (D1 : IsData xt1) by exact I. assert (D4 : IsData xt4) by exact I.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xea2dc%Z => first [ eapply evt_eq; [| eapply (fc_LX (Z.to_nat LAST) q); [exact INV | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | _ => exp_cut pc
      end).
  Qed.

  Lemma fc_63c : forall (q : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xs3 xs10 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> (FIRST <= q < LAST)%Z ->
    evt asegs Q (FCP 0xea274 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 (Z_to_bv 64 (- FL)) (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 (Z_to_bv 64 q) (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) (Z_to_bv 64 FPT) mm).
  Proof using FCH K84 K77 PFp.
    intros until mm. intros INV Hq. pose proof INV as INV0. fc_popen INV0. fc_env.
    do 4 akstep.
    lazymatch goal with |- context [Z.b2z ?c] => destruct c end; cbn [Z.b2z]; akstep.
    all: eapply evt_eq; [| eapply (fc_650 _); [exact INV | | reflexivity]]; [num_st_eq | lia].
  Qed.

  Lemma fc_exp_body : forall (p : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xs3 xs11 xt4 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
      ((FPT = 0 /\ p = IP + IL) \/ (FPT <> 0 /\ p = FPT + FL))%Z ->
      evt asegs Q (FCP 0xea154 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 (Z_to_bv 64 (- FL)) (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                       (Z_to_bv 64 p) xs11 (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) (Z_to_bv 64 FPT) mm).
  Proof using FCH K84 K77 PFp.
    intros until mm. intros INV Hp. pose proof INV as INV0. fc_popen INV0. fc_env. pose proof fc_flb as FLB.
    assert (PB : (FIRST <= p <= LAST)%Z).
    { destruct PFp as (_ & _ & PD). destruct PD as [[E1 E2]|[(E1 & Q1 & Q2 & _) _]]; lia. }
    assert (D1 : IsData xa1) by exact I. assert (D4 : IsData xt4) by exact I.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xea288%Z => first [ eapply evt_eq; [| eapply (fc_650 _); [exact INV | | reflexivity]]; [num_st_eq | lia] | fail 100 "cut" pc ]
      | 0xea274%Z => first [ eapply evt_eq; [| eapply (fc_63c _); [exact INV |]]; [num_st_eq | lia] | fail 100 "cut" pc ]
      | _ => exp_cut pc
      end).
  Qed.
  End EXPPART.

  Lemma fc_exp : fc_84c_k -> fc_77c_k -> EXP_K.
  Proof using FCH.
    intros K84 K77. unfold fc_exp_k. intros until mm. intros INV PFp Hp.
    eapply (fc_exp_body K84 K77 IP IL FPT FL PFp p); [exact INV | exact Hp].
  Qed.
End FCA.
