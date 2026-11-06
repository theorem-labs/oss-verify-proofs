(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_kit2 Sj_num_fc_defs Sj_num_fc_defs2 Sj_num_fc_defs3 Sj_num_fc_arith Sj_num_fc_runs Sj_num_fc_q1 Sj_num_fc_q3.
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
  Hypothesis FLO : (0x6ca000 <= f /\ f + 1016 <= lo)%Z.
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
     evt asegs Q (FCP 0x81794 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Notation ERRB_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
     evt asegs Q (FCP 0x81794 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
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

  Hypothesis FRM0 : frm0 fc.
  Hypothesis SHPL1 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2a2e0 10416.
  Hypothesis SHPL2 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2cc60 640.
  Collection FCH2 := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO SHPL1 SHPL2.
  Notation FCS2 pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom asegs)).
  Notation FCINV2 := (fc_inv2 spq f A OUT lo txt m0).

  Notation FCL2 L := (L sp gp tp lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q SHPL1 SHPL2) (only parsing).

  Notation PF := (fpfacts A txt FIRST LAST).
  Notation FCINV3 := (fc_inv3 spq f A OUT lo txt m0).

  Definition fc_mset_k : Prop :=
    forall (qe IP IL FPT FL : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
           c0 c8 c16 c24 c32 c40 c64 qw ww lmw negb vb tmb errw (mm : mem),
      FCINV3 c0 c8 c16 c24 c32 c40 c64 (Z_to_bv 64 0) qw ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
      PF IP IL FPT FL -> (-342 <= qe <= 330)%Z ->
      evt asegs Q (FCS2 0x81794 (Z_to_bv 64 0xe5698) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) (Z_to_bv 64 504) xa3 xa4 xa5 xa6 xa7
                        (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) (Z_to_bv 64 4294967295) xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                        (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Section SCIEXP.
  Hypothesis KMSET : fc_mset_k.
  Variables IP IL FPT FL : Z.
  Hypothesis PFp : PF IP IL FPT FL.

  Notation DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm :=
    (FCINV2 c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm).

  Lemma fc_530 : forall (qe : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc -> (-342 <= qe <= 330)%Z ->
    evt asegs Q (FCS2 0xe5580 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. fc_open2 INV0. fc_env.
    awalk ltac:(fun pc => lazymatch pc with 0xe5588%Z => idtac end).
    num_cur_mem ltac:(fun m1 => eapply (fc_run1 f m1 ltac:(lia) Q); [exact BSH | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI BSH; intros mm2 BSH MI MU' WM'; transport_after_call asegs m1 mm2 MU' WM'; clear MU' WM').
    awalk ltac:(fun pc => lazymatch pc with
      | 0x81794%Z => first [ eapply evt_eq; [| eapply (KMSET qe IP IL FPT FL)]; [num_st_eq | fc_close3 | assumption | exact PFp | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_LC : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 100 * 8 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + Z.of_nat fu + 1 <= 330)%Z ->
    evt asegs Q (FCS2 0xe556c xra xt0 xt1 xt2 (Z_to_bv 64 w) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 99) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV FRM Hw Hw64 Hq Hb.
    - change (8 ^ Z.of_nat 0)%Z with 1%Z in Hw.
      pose proof (sci_c8 w ltac:(lia)) as BT.
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe556c%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xe5580%Z => first [ eapply evt_eq; [| eapply (fc_530 (qe + 1)%Z)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
        end).
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hw by lia.
      pose proof (sci_c8 w ltac:(lia)) as BT.
      assert (P0 : (0 < 8 ^ Z.of_nat fu)%Z) by (apply Z.pow_pos_nonneg; lia).
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe556c%Z => first [ eapply evt_eq; [| eapply (IH _ (qe + 1)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
        | 0xe5580%Z => first [ eapply evt_eq; [| eapply (fc_530 (qe + 1)%Z)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fc_508 : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 100 * 8 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + Z.of_nat fu + 1 <= 330)%Z ->
    evt asegs Q (FCS2 0xe5558 xra xt0 xt1 xt2 (Z_to_bv 64 w) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hw Hw64 Hq Hb.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe556c%Z => first [ eapply evt_eq; [| eapply (fc_LC fu w qe)]; [num_st_eq | exact INV | assumption | exact Hw | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_4e0 : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 100 * 8 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + Z.of_nat fu + 1 <= 330)%Z ->
    evt asegs Q (FCS2 0xe5530 xra xt0 xt1 xt2 (Z_to_bv 64 w) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hw Hw64 Hq Hb. pose proof INV as INV0. fc_open2 INV0. fc_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe5558%Z => first [ eapply evt_eq; [| eapply (fc_508 fu w qe)]; [num_st_eq | fc_close2 | assumption | exact Hw | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xe5580%Z => first [ eapply evt_eq; [| eapply (fc_530 qe)]; [num_st_eq | fc_close2 | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_4f4 : forall (w qe : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 100)%Z -> (-342 <= qe)%Z -> (qe + 1 <= 330)%Z ->
    evt asegs Q (FCS2 0xe5544 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 w) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hw Hq Hb. pose proof INV as INV0. fc_open2 INV0. fc_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe5558%Z => first [ eapply evt_eq; [| eapply (fc_508 0%nat w qe)]; [num_st_eq | fc_close2 | assumption | change (8 ^ Z.of_nat 0)%Z with 1%Z; lia | lia | lia | change (Z.of_nat 0) with 0%Z; lia]
                           | fail 100 "cut" pc ]
      | 0xe5580%Z => first [ eapply evt_eq; [| eapply (fc_530 qe)]; [num_st_eq | fc_close2 | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_LB : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 10000 * 64 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + 2 * (Z.of_nat fu + 1) + 2 <= 330)%Z ->
    evt asegs Q (FCS2 0xe5514 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 w) (Z_to_bv 64 2951479051793528259) (Z_to_bv 64 624) xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV FRM Hw Hw64 Hq Hb.
    - change (64 ^ Z.of_nat 0)%Z with 1%Z in Hw.
      pose proof (sci_b w ltac:(lia)) as BT. pose proof (Z.shiftr_div_pow2 w 4 ltac:(lia)) as SH4. change (2 ^ 4)%Z with 16%Z in SH4.
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe5514%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xe5530%Z => first [ eapply evt_eq; [| eapply (fc_4e0 1%nat _ (qe + 2)%Z)]; [num_st_eq | exact INV | assumption | change (8 ^ Z.of_nat 1)%Z with 8%Z; lia | lia | lia | change (Z.of_nat 1) with 1%Z; lia]
                             | fail 100 "cut" pc ]
        end).
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hw by lia.
      pose proof (sci_b w ltac:(lia)) as BT. pose proof (Z.shiftr_div_pow2 w 4 ltac:(lia)) as SH4. change (2 ^ 4)%Z with 16%Z in SH4.
      assert (P0 : (0 < 64 ^ Z.of_nat fu)%Z) by (apply Z.pow_pos_nonneg; lia).
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe5514%Z => first [ eapply evt_eq; [| eapply (IH _ (qe + 2)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
        | 0xe5530%Z => first [ eapply evt_eq; [| eapply (fc_4e0 1%nat _ (qe + 2)%Z)]; [num_st_eq | exact INV | assumption | change (8 ^ Z.of_nat 1)%Z with 8%Z; lia | lia | lia | change (Z.of_nat 1) with 1%Z; lia]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fc_4ac : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 10000 * 64 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + 2 * (Z.of_nat fu + 1) + 2 <= 330)%Z ->
    evt asegs Q (FCS2 0xe54fc xra xt0 xt1 xt2 xa0 (Z_to_bv 64 w) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hw Hw64 Hq Hb. pose proof INV as INV0. fc_open2 INV0. fc_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe5544%Z => first [ eapply evt_eq; [| eapply (fc_4f4 w qe)]; [num_st_eq | fc_close2 | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xe5514%Z => first [ eapply evt_eq; [| eapply (fc_LB fu w qe)]; [num_st_eq | fc_close2 | assumption | exact Hw | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_LA : forall (fu : nat) (w qe : Z) xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc ->
    (0 <= w < 100000000 * 8192 ^ Z.of_nat fu)%Z -> (w < 18446744073709551616)%Z -> (-342 <= qe)%Z -> (qe + 4 * (Z.of_nat fu + 1) + 6 <= 330)%Z ->
    evt asegs Q (FCS2 0xe54e8 xra xt0 xt1 xt2 (Z_to_bv 64 3777893186295716171) (Z_to_bv 64 w) (Z_to_bv 64 99999999) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV FRM Hw Hw64 Hq Hb.
    - change (8192 ^ Z.of_nat 0)%Z with 1%Z in Hw.
      pose proof (sci_a w ltac:(lia)) as BT.
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe54e8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xe54fc%Z => first [ eapply evt_eq; [| eapply (fc_4ac 1%nat _ (qe + 4)%Z)]; [num_st_eq | exact INV | assumption | change (64 ^ Z.of_nat 1)%Z with 64%Z; lia | lia | lia | change (Z.of_nat 1) with 1%Z; lia]
                             | fail 100 "cut" pc ]
        end).
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hw by lia.
      pose proof (sci_a w ltac:(lia)) as BT.
      assert (P0 : (0 < 8192 ^ Z.of_nat fu)%Z) by (apply Z.pow_pos_nonneg; lia).
      akstep.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xe54e8%Z => first [ eapply evt_eq; [| eapply (IH _ (qe + 4)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
        | 0xe54fc%Z => first [ eapply evt_eq; [| eapply (fc_4ac 1%nat _ (qe + 4)%Z)]; [num_st_eq | exact INV | assumption | change (64 ^ Z.of_nat 1)%Z with 64%Z; lia | lia | lia | change (Z.of_nat 1) with 1%Z; lia]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fc_47c : forall (q : Z) (ww : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 qw lmw negb vb tmb errw (mm : mem),
    DINV c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb errw mm -> frm0 xfc -> (-342 <= q <= 308)%Z ->
    evt asegs Q (FCS2 0xe54cc xra xt0 xt1 xt2 xa0 ww xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 q) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KMSET PFp.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. fc_open2 INV0. fc_env.
    rewrite <- (Z_to_bv_bv_unsigned ww).
    pose proof (bv_unsigned_in_range 64 ww) as RW. unfold bv_modulus in RW. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RW.
    remember (bv_unsigned ww) as w eqn:EW. clear EW.
    pose proof (Z.shiftr_div_pow2 w 4 ltac:(lia)) as SH4. change (2 ^ 4)%Z with 16%Z in SH4.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe54fc%Z => first [ eapply evt_eq; [| eapply (fc_4ac 0%nat w q)]; [num_st_eq | exact INV | assumption | change (64 ^ Z.of_nat 0)%Z with 1%Z; lia | lia | lia | change (Z.of_nat 0) with 0%Z; lia]
                           | fail 100 "cut" pc ]
      | 0xe54e8%Z => first [ eapply evt_eq; [| eapply (fc_LA 3%nat w q)]; [num_st_eq | exact INV | assumption | change (8192 ^ Z.of_nat 3)%Z with 549755813888%Z; lia | lia | lia | change (Z.of_nat 3) with 3%Z; lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
  End SCIEXP.

  Lemma fc_47c_ok : fc_mset_k -> fc_47c_k sp gp tp lo spq f A FIRST LAST OUT txt m0 Q.
  Proof using FCH2.
    intros KMSET. unfold fc_47c_k. intros until mm. intros INV FRM PFp Hq.
    eapply (fc_47c KMSET IP IL FPT FL PFp q ww); [exact INV | exact FRM | exact Hq].
  Qed.
End FCA.
