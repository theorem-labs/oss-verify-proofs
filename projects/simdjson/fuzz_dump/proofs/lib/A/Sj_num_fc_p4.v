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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_defs Sj_num_fc_p2 Sj_num_fc_p3 Sj_num_fc_kit2.
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

  Definition fc_8cc_k : Prop :=
    forall (IP IL FPT FL tm : Z) (xa1 : word) xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs3 xs8 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> PF IP IL FPT FL -> (0 <= tm <= 1)%Z ->
      (tm <> 0 -> 1 <= bv_unsigned xa1 <= 18446744073709551614)%Z ->
      evt asegs Q (FCP 0xdcdfc xra xt0 xt1 xt2 (Z_to_bv 64 tm) xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 IP) xs8
                       xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 FPT) mm).

  Section LOOK2.
  Hypothesis K8CC : fc_8cc_k.
  Variables IP IL FPT FL : Z.
  Hypothesis PFp : PF IP IL FPT FL.

  Notation nzf z := ((49 <= tb z)%Z /\ ((IP <= z < IP + IL)%Z \/ (FPT <> 0 /\ FPT <= z < FPT + FL)%Z)).
  Notation cs d := (Z.min d IL + Z.max 0 (Z.min (d - IL - 1) FL))%Z.

  Ltac l2_env :=
    fc_env;
    let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let G1 := fresh "G1" in let PD := fresh "PD" in
    pose proof PFp as ((P1 & P2 & P3) & G1 & PD);
    let FR0 := fresh "FR0" in let FR1 := fresh "FR1" in
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PD as [[? ?] | [(? & ? & ? & ?) _]]; lia);
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PD as [[? ?] | [(? & ? & ? & ?) _]]; lia);
    let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in destruct FLR as (R1 & R2 & R3);
    let T1 := fresh "T1" in let T2 := fresh "T2" in let T3 := fresh "T3" in destruct TXR as (T1 & T2 & T3).

  Ltac akif := let H := fresh "KB" in if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H; first [ solve [exfalso; lia] | idtac ].

  Ltac cut8cc INV tm := eapply evt_eq; [| eapply (K8CC IP IL FPT FL tm)]; [num_st_eq | exact INV | exact PFp | lia | ].

  Lemma fc_84c : forall xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
    evt asegs Q (FCP 0xdcd7c xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 (Z_to_bv 64 0xA0000002E) xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros until mm. intros INV.
    akstep. akstep.
    cut8cc INV 0%Z. intros C. exfalso. apply C. reflexivity.
  Qed.

  Lemma fc_L7 : forall (fu : nat) (z k w : Z) xra xt0 xa4 xa5 xs3 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> nzf z ->
    (FPT <> 0)%Z -> (0 <= k < FL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ FPT + k <= z)%Z -> (FL - k <= Z.of_nat fu)%Z ->
    evt asegs Q (FCP 0xdcda0 xra xt0 (Z_to_bv 64 10) (Z_to_bv 64 (FL + -1 - k)) (Z_to_bv 64 (FPT + k)) (Z_to_bv 64 w) (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5
                     (Z_to_bv 64 (FPT + k)) (Z_to_bv 64 999999999999999999) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV NZ HF Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. fc_popen INV0. l2_env.
    destruct PD as [[PA PB] | [(PA & PB & PC & PDD) G2]]; [exfalso; lia|].
    pose proof (G2 (FPT + k)%Z ltac:(lia)) as Gk. pose proof (ftb_range A txt (FPT + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold ftb in Gk, Rk.
    assert (NZk : (z = FPT + k -> 49 <= bv_unsigned (nth (Z.to_nat (FPT + k - A)) txt (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    akstep.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdcdfc%Z => first [ cut8cc INV 1%Z; intros _; rewrite ?unsigned_lit by lia; destruct (Z.eq_dec z (FPT + k)); lia | fail 100 "cut" pc ]
      | 0xdcda0%Z => first [ eapply evt_eq; [| eapply (IH z (k + 1)%Z (w * 10 + bv_unsigned (nth (Z.to_nat (FPT + k - A)) txt (Z_to_bv 8 0)) - 48)%Z)];
                             [num_st_eq | exact INV | split; assumption | lia | lia | lia | destruct (Z.eq_dec z (FPT + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_854 : forall (z w : Z) xra xt0 xt2 xa0 xa4 xa5 xa6 xs3 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> nzf z ->
    (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + IL <= z)%Z ->
    evt asegs Q (FCP 0xdcd84 xra xt0 (Z_to_bv 64 1000000000000000000) xt2 xa0 (Z_to_bv 64 w) (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5
                     xa6 (Z_to_bv 64 10) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros until mm. intros INV NZ Hw Hz.
    pose proof INV as INV0. fc_popen INV0. l2_env.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdcdfc%Z => first [ cut8cc INV 1%Z; intros _; rewrite ?unsigned_lit by lia; lia | fail 100 "cut" pc ]
      | 0xdcda0%Z => first [ eapply evt_eq; [| eapply (fc_L7 (Z.to_nat FL) z 0%Z w)];
                             [num_st_eq | exact INV | split; assumption | lia | lia | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_L6 : forall (fu : nat) (z k w : Z) xra xt0 xt2 xa4 xa5 xs3 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> nzf z ->
    (0 <= k <= IL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + k <= z)%Z -> (IL - k < Z.of_nat fu)%Z ->
    evt asegs Q (FCP 0xdcd3c xra xt0 (Z_to_bv 64 1000000000000000000) xt2 (Z_to_bv 64 (IP + k)) (Z_to_bv 64 w) (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5
                     (Z_to_bv 64 (IP + k)) (Z_to_bv 64 10) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV NZ Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. fc_popen INV0. l2_env.
    pose proof (ftb_range A txt (IP + k)) as Rk.
    assert (Gk : (k < IL -> 48 <= ftb A txt (IP + k))%Z) by (intros X; apply G1; lia).
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold ftb in Gk, Rk.
    assert (NZk : (z = IP + k -> 49 <= bv_unsigned (nth (Z.to_nat (IP + k - A)) txt (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    akstep.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdcdfc%Z => first [ cut8cc INV 1%Z; intros _; rewrite ?unsigned_lit by lia; lia | fail 100 "cut" pc ]
      | 0xdcd84%Z => first [ eapply evt_eq; [| eapply (fc_854 z w)]; [num_st_eq | exact INV | split; assumption | lia | lia] | fail 100 "cut" pc ]
      | 0xdcd3c%Z => first [ eapply evt_eq; [| eapply (IH z (k + 1)%Z (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) txt (Z_to_bv 8 0)) - 48)%Z)];
                             [num_st_eq | exact INV | split; assumption | lia | lia | destruct (Z.eq_dec z (IP + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_7dc : forall (z cnt : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt3 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> (-4294967296 <= cnt <= IL + FL)%Z -> (20 <= cnt -> nzf z) ->
    evt asegs Q (FCP 0xdcd0c xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 cnt) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros until mm. intros INV Hcnt NZ.
    pose proof INV as INV0. fc_popen INV0. l2_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdcdfc%Z => first [ cut8cc INV 0%Z; intros C; exfalso; apply C; reflexivity | fail 100 "cut" pc ]
      | 0xdcd3c%Z => first [ eapply evt_eq; [| eapply (fc_L6 (Datatypes.S (Z.to_nat IL)) z 0%Z 0%Z)];
                             [num_st_eq | exact INV | apply NZ; lia | lia | lia | right; destruct (NZ ltac:(lia)) as [_ [?|[? ?]]]; lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac nodisj := repeat match goal with
    | H : _ \/ _ |- _ => clear H
    | H : (_ \/ _) /\ _ |- _ => clear H
    | H : _ /\ (_ \/ _) |- _ => clear H
    end.
  Lemma fc_L5 : forall (fu : nat) (c cnt : Z) xra xt0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
    (IP <= c < LAST)%Z -> (IL + FL - (c - IP) <= cnt <= IL + FL - cs (c - IP))%Z -> (LAST - c <= Z.of_nat fu)%Z ->
    evt asegs Q (FCP 0xdcce0 xra xt0 (Z_to_bv 64 46) (Z_to_bv 64 48) (Z_to_bv 64 c) xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 cnt) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 (Z_to_bv 64 c) xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV Hc Hcnt Hf; [exfalso; lia|].
    pose proof INV as INV0. fc_popen INV0. l2_env.
    pose proof (ftb_range A txt c) as Rc.
    assert (S1 : (IP <= c < IP + IL -> 48 <= ftb A txt c)%Z) by (intros X; apply G1; lia).
    assert (S2 : (FPT <> 0 -> FPT <= c < FPT + FL -> 48 <= ftb A txt c)%Z).
    { intros X Y. destruct PD as [[? ?] | [_ G2]]; [lia | apply G2; lia]. }
    assert (D1 : (FPT <> 0 -> c = IP + IL -> ftb A txt c = 46)%Z).
    { intros X ->. destruct PD as [[? ?] | [(? & ? & ? & ?) _]]; [lia | assumption]. }
    unfold ftb in Rc, S1, S2, D1.
    assert (CR : (-4294967296 <= cnt - 1 /\ cnt <= IL + FL)%Z) by (clear - Hc Hcnt R1 R2 R3 T1 T3 P1 P2 FR0 FR1; lia).

    assert (CS1 : fhold (cs (c + 1 - IP) <= cs (c - IP) + 1)%Z) by (unfold fhold; clear - P2; lia).
    assert (CSL : fhold (c + 1 = LAST -> cs (c + 1 - IP) = IL + FL)%Z) by (unfold fhold; clear - P2 P3 FR0 FR1; lia).
    assert (CSD : fhold (bv_unsigned (nth (Z.to_nat (c - A)) txt (Z_to_bv 8 0)) = 46 -> cs (c + 1 - IP) = cs (c - IP))%Z) by (unfold fhold; clear - Hc P2 FR0 FR1 S1 S2; lia).
    assert (SPN : fhold (bv_unsigned (nth (Z.to_nat (c - A)) txt (Z_to_bv 8 0)) <> 46 -> 20 <= cnt -> IP <= c < IP + IL \/ (FPT <> 0 /\ FPT <= c < FPT + FL))%Z)
      by (unfold fhold; clear - Hc Hcnt P2 FR0 FR1 D1; lia).
    apply fhold_in in Hcnt. apply fhold_in in S1. apply fhold_in in S2. apply fhold_in in D1. apply fhold_in in FR0. apply fhold_in in FR1. clear PD G1.
    do 4 akstep. akif.
    akstep. akstep.
    if_cases KZ; zify_cond KZ; [rewrite KZ | akstep; if_cases KZ0; zify_cond KZ0; [rewrite KZ0 | ]].
    -
      clear S1 S2 D1 CSD SPN.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xdcd0c%Z => first [ eapply evt_eq; [| eapply (fc_7dc c (cnt - 1)%Z)]; [num_st_eq | exact INV | unfold fhold in *; nodisj; lia | intros X; exfalso; unfold fhold in *; nodisj; lia] | fail 100 "cut" pc ]
        | 0xdcce0%Z => first [ eapply evt_eq; [| eapply (IH (c + 1)%Z (cnt - 1)%Z)]; [num_st_eq | exact INV | unfold fhold in *; nodisj; lia | unfold fhold in *; nodisj; lia | nodisj; lia] | fail 100 "cut" pc ]
        end).
    -
      pose proof (fhold_in _ (fhold_out _ CSD KZ0)) as CSE. clear S1 S2 D1 CSD SPN.
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xdcd0c%Z => first [ eapply evt_eq; [| eapply (fc_7dc c cnt)]; [num_st_eq | exact INV | unfold fhold in *; nodisj; lia | intros X; exfalso; unfold fhold in *; nodisj; lia] | fail 100 "cut" pc ]
        | 0xdcce0%Z => first [ eapply evt_eq; [| eapply (IH (c + 1)%Z cnt)]; [num_st_eq | exact INV | unfold fhold in *; nodisj; lia | unfold fhold in *; nodisj; lia | nodisj; lia] | fail 100 "cut" pc ]
        end).
    -
      akwalk ltac:(fun pc => lazymatch pc with
        | 0xdcd0c%Z => first [ eapply evt_eq; [| eapply (fc_7dc c cnt)]; [num_st_eq | exact INV | unfold fhold in *; nodisj; lia |];
                               intros X; pose proof (fhold_out _ SPN KZ0 X) as SPAN;
                               split; [unfold ftb; unfold fhold in *; clear - SPAN S1 S2 KZ Rc; lia | exact SPAN]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fc_77c : forall xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs3 xs10 xs11 xt4 xt5 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
    FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm -> (20 <= IL + FL)%Z ->
    evt asegs Q (FCP 0xdccac xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FL) (Z_to_bv 64 IL) xa4 xa5 xa6 (Z_to_bv 64 (IL + FL)) xs3 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + IL))
                     xs10 xs11 (Z_to_bv 64 0xA0000002E) xt4 xt5 (Z_to_bv 64 FPT) mm).
  Proof using FCH K8CC PFp.
    intros until mm. intros INV H20.
    pose proof INV as INV0. fc_popen INV0. l2_env.
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xdcce0%Z => first [ eapply evt_eq; [| eapply (fc_L5 (Z.to_nat LAST) IP (IL + FL)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xdcd18%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      end).
  Qed.
  End LOOK2.

  Lemma fc_look2 : fc_8cc_k -> FCD fc_84c_k /\ FCD fc_77c_k.
  Proof using FCH.
    intros K8CC. split.
    - unfold fc_84c_k. intros until mm. intros INV PFp H20. eapply (fc_84c K8CC IP IL FPT FL PFp). exact INV.
    - unfold fc_77c_k. intros until mm. intros INV PFp H20. eapply (fc_77c K8CC IP IL FPT FL PFp); [exact INV | exact H20].
  Qed.
End FCA.
